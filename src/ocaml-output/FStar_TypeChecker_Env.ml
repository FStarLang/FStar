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
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
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
           (fun uu___0_14039  ->
              match uu___0_14039 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14042 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____14042  in
                  let uu____14043 =
                    let uu____14044 = FStar_Syntax_Subst.compress y  in
                    uu____14044.FStar_Syntax_Syntax.n  in
                  (match uu____14043 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14048 =
                         let uu___327_14049 = y1  in
                         let uu____14050 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___327_14049.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___327_14049.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14050
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14048
                   | uu____14053 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst  ->
    fun env1  ->
      let uu___333_14067 = env1  in
      let uu____14068 = rename_gamma subst env1.gamma  in
      {
        solver = (uu___333_14067.solver);
        range = (uu___333_14067.range);
        curmodule = (uu___333_14067.curmodule);
        gamma = uu____14068;
        gamma_sig = (uu___333_14067.gamma_sig);
        gamma_cache = (uu___333_14067.gamma_cache);
        modules = (uu___333_14067.modules);
        expected_typ = (uu___333_14067.expected_typ);
        sigtab = (uu___333_14067.sigtab);
        attrtab = (uu___333_14067.attrtab);
        instantiate_imp = (uu___333_14067.instantiate_imp);
        effects = (uu___333_14067.effects);
        generalize = (uu___333_14067.generalize);
        letrecs = (uu___333_14067.letrecs);
        top_level = (uu___333_14067.top_level);
        check_uvars = (uu___333_14067.check_uvars);
        use_eq = (uu___333_14067.use_eq);
        use_eq_strict = (uu___333_14067.use_eq_strict);
        is_iface = (uu___333_14067.is_iface);
        admit = (uu___333_14067.admit);
        lax = (uu___333_14067.lax);
        lax_universes = (uu___333_14067.lax_universes);
        phase1 = (uu___333_14067.phase1);
        failhard = (uu___333_14067.failhard);
        nosynth = (uu___333_14067.nosynth);
        uvar_subtyping = (uu___333_14067.uvar_subtyping);
        tc_term = (uu___333_14067.tc_term);
        type_of = (uu___333_14067.type_of);
        universe_of = (uu___333_14067.universe_of);
        check_type_of = (uu___333_14067.check_type_of);
        use_bv_sorts = (uu___333_14067.use_bv_sorts);
        qtbl_name_and_index = (uu___333_14067.qtbl_name_and_index);
        normalized_eff_names = (uu___333_14067.normalized_eff_names);
        fv_delta_depths = (uu___333_14067.fv_delta_depths);
        proof_ns = (uu___333_14067.proof_ns);
        synth_hook = (uu___333_14067.synth_hook);
        try_solve_implicits_hook = (uu___333_14067.try_solve_implicits_hook);
        splice = (uu___333_14067.splice);
        mpreprocess = (uu___333_14067.mpreprocess);
        postprocess = (uu___333_14067.postprocess);
        identifier_info = (uu___333_14067.identifier_info);
        tc_hooks = (uu___333_14067.tc_hooks);
        dsenv = (uu___333_14067.dsenv);
        nbe = (uu___333_14067.nbe);
        strict_args_tab = (uu___333_14067.strict_args_tab);
        erasable_types_tab = (uu___333_14067.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14076  -> fun uu____14077  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___340_14099 = env1  in
      {
        solver = (uu___340_14099.solver);
        range = (uu___340_14099.range);
        curmodule = (uu___340_14099.curmodule);
        gamma = (uu___340_14099.gamma);
        gamma_sig = (uu___340_14099.gamma_sig);
        gamma_cache = (uu___340_14099.gamma_cache);
        modules = (uu___340_14099.modules);
        expected_typ = (uu___340_14099.expected_typ);
        sigtab = (uu___340_14099.sigtab);
        attrtab = (uu___340_14099.attrtab);
        instantiate_imp = (uu___340_14099.instantiate_imp);
        effects = (uu___340_14099.effects);
        generalize = (uu___340_14099.generalize);
        letrecs = (uu___340_14099.letrecs);
        top_level = (uu___340_14099.top_level);
        check_uvars = (uu___340_14099.check_uvars);
        use_eq = (uu___340_14099.use_eq);
        use_eq_strict = (uu___340_14099.use_eq_strict);
        is_iface = (uu___340_14099.is_iface);
        admit = (uu___340_14099.admit);
        lax = (uu___340_14099.lax);
        lax_universes = (uu___340_14099.lax_universes);
        phase1 = (uu___340_14099.phase1);
        failhard = (uu___340_14099.failhard);
        nosynth = (uu___340_14099.nosynth);
        uvar_subtyping = (uu___340_14099.uvar_subtyping);
        tc_term = (uu___340_14099.tc_term);
        type_of = (uu___340_14099.type_of);
        universe_of = (uu___340_14099.universe_of);
        check_type_of = (uu___340_14099.check_type_of);
        use_bv_sorts = (uu___340_14099.use_bv_sorts);
        qtbl_name_and_index = (uu___340_14099.qtbl_name_and_index);
        normalized_eff_names = (uu___340_14099.normalized_eff_names);
        fv_delta_depths = (uu___340_14099.fv_delta_depths);
        proof_ns = (uu___340_14099.proof_ns);
        synth_hook = (uu___340_14099.synth_hook);
        try_solve_implicits_hook = (uu___340_14099.try_solve_implicits_hook);
        splice = (uu___340_14099.splice);
        mpreprocess = (uu___340_14099.mpreprocess);
        postprocess = (uu___340_14099.postprocess);
        identifier_info = (uu___340_14099.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___340_14099.dsenv);
        nbe = (uu___340_14099.nbe);
        strict_args_tab = (uu___340_14099.strict_args_tab);
        erasable_types_tab = (uu___340_14099.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___344_14111 = e  in
      let uu____14112 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___344_14111.solver);
        range = (uu___344_14111.range);
        curmodule = (uu___344_14111.curmodule);
        gamma = (uu___344_14111.gamma);
        gamma_sig = (uu___344_14111.gamma_sig);
        gamma_cache = (uu___344_14111.gamma_cache);
        modules = (uu___344_14111.modules);
        expected_typ = (uu___344_14111.expected_typ);
        sigtab = (uu___344_14111.sigtab);
        attrtab = (uu___344_14111.attrtab);
        instantiate_imp = (uu___344_14111.instantiate_imp);
        effects = (uu___344_14111.effects);
        generalize = (uu___344_14111.generalize);
        letrecs = (uu___344_14111.letrecs);
        top_level = (uu___344_14111.top_level);
        check_uvars = (uu___344_14111.check_uvars);
        use_eq = (uu___344_14111.use_eq);
        use_eq_strict = (uu___344_14111.use_eq_strict);
        is_iface = (uu___344_14111.is_iface);
        admit = (uu___344_14111.admit);
        lax = (uu___344_14111.lax);
        lax_universes = (uu___344_14111.lax_universes);
        phase1 = (uu___344_14111.phase1);
        failhard = (uu___344_14111.failhard);
        nosynth = (uu___344_14111.nosynth);
        uvar_subtyping = (uu___344_14111.uvar_subtyping);
        tc_term = (uu___344_14111.tc_term);
        type_of = (uu___344_14111.type_of);
        universe_of = (uu___344_14111.universe_of);
        check_type_of = (uu___344_14111.check_type_of);
        use_bv_sorts = (uu___344_14111.use_bv_sorts);
        qtbl_name_and_index = (uu___344_14111.qtbl_name_and_index);
        normalized_eff_names = (uu___344_14111.normalized_eff_names);
        fv_delta_depths = (uu___344_14111.fv_delta_depths);
        proof_ns = (uu___344_14111.proof_ns);
        synth_hook = (uu___344_14111.synth_hook);
        try_solve_implicits_hook = (uu___344_14111.try_solve_implicits_hook);
        splice = (uu___344_14111.splice);
        mpreprocess = (uu___344_14111.mpreprocess);
        postprocess = (uu___344_14111.postprocess);
        identifier_info = (uu___344_14111.identifier_info);
        tc_hooks = (uu___344_14111.tc_hooks);
        dsenv = uu____14112;
        nbe = (uu___344_14111.nbe);
        strict_args_tab = (uu___344_14111.strict_args_tab);
        erasable_types_tab = (uu___344_14111.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14129 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____14129)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14144) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14147,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14149,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14152 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14166 . unit -> 'uuuuuu14166 FStar_Util.smap =
  fun uu____14173  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14179 . unit -> 'uuuuuu14179 FStar_Util.smap =
  fun uu____14186  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14324 = new_gamma_cache ()  in
                  let uu____14327 = new_sigtab ()  in
                  let uu____14330 = new_sigtab ()  in
                  let uu____14337 =
                    let uu____14352 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14352, FStar_Pervasives_Native.None)  in
                  let uu____14373 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14377 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14381 = FStar_Options.using_facts_from ()  in
                  let uu____14382 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14385 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14386 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14400 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14324;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14327;
                    attrtab = uu____14330;
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
                    qtbl_name_and_index = uu____14337;
                    normalized_eff_names = uu____14373;
                    fv_delta_depths = uu____14377;
                    proof_ns = uu____14381;
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
                    identifier_info = uu____14382;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14385;
                    nbe;
                    strict_args_tab = uu____14386;
                    erasable_types_tab = uu____14400
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
  fun uu____14597  ->
    let uu____14598 = FStar_ST.op_Bang query_indices  in
    match uu____14598 with
    | [] -> failwith "Empty query indices!"
    | uu____14653 ->
        let uu____14663 =
          let uu____14673 =
            let uu____14681 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14681  in
          let uu____14735 = FStar_ST.op_Bang query_indices  in uu____14673 ::
            uu____14735
           in
        FStar_ST.op_Colon_Equals query_indices uu____14663
  
let (pop_query_indices : unit -> unit) =
  fun uu____14831  ->
    let uu____14832 = FStar_ST.op_Bang query_indices  in
    match uu____14832 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14959  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14996  ->
    match uu____14996 with
    | (l,n) ->
        let uu____15006 = FStar_ST.op_Bang query_indices  in
        (match uu____15006 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15128 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15151  ->
    let uu____15152 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15152
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15220 =
       let uu____15223 = FStar_ST.op_Bang stack  in env1 :: uu____15223  in
     FStar_ST.op_Colon_Equals stack uu____15220);
    (let uu___417_15272 = env1  in
     let uu____15273 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15276 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15279 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15286 =
       let uu____15301 =
         let uu____15305 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15305  in
       let uu____15337 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15301, uu____15337)  in
     let uu____15386 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15389 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15392 =
       let uu____15395 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15395  in
     let uu____15415 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15428 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___417_15272.solver);
       range = (uu___417_15272.range);
       curmodule = (uu___417_15272.curmodule);
       gamma = (uu___417_15272.gamma);
       gamma_sig = (uu___417_15272.gamma_sig);
       gamma_cache = uu____15273;
       modules = (uu___417_15272.modules);
       expected_typ = (uu___417_15272.expected_typ);
       sigtab = uu____15276;
       attrtab = uu____15279;
       instantiate_imp = (uu___417_15272.instantiate_imp);
       effects = (uu___417_15272.effects);
       generalize = (uu___417_15272.generalize);
       letrecs = (uu___417_15272.letrecs);
       top_level = (uu___417_15272.top_level);
       check_uvars = (uu___417_15272.check_uvars);
       use_eq = (uu___417_15272.use_eq);
       use_eq_strict = (uu___417_15272.use_eq_strict);
       is_iface = (uu___417_15272.is_iface);
       admit = (uu___417_15272.admit);
       lax = (uu___417_15272.lax);
       lax_universes = (uu___417_15272.lax_universes);
       phase1 = (uu___417_15272.phase1);
       failhard = (uu___417_15272.failhard);
       nosynth = (uu___417_15272.nosynth);
       uvar_subtyping = (uu___417_15272.uvar_subtyping);
       tc_term = (uu___417_15272.tc_term);
       type_of = (uu___417_15272.type_of);
       universe_of = (uu___417_15272.universe_of);
       check_type_of = (uu___417_15272.check_type_of);
       use_bv_sorts = (uu___417_15272.use_bv_sorts);
       qtbl_name_and_index = uu____15286;
       normalized_eff_names = uu____15386;
       fv_delta_depths = uu____15389;
       proof_ns = (uu___417_15272.proof_ns);
       synth_hook = (uu___417_15272.synth_hook);
       try_solve_implicits_hook = (uu___417_15272.try_solve_implicits_hook);
       splice = (uu___417_15272.splice);
       mpreprocess = (uu___417_15272.mpreprocess);
       postprocess = (uu___417_15272.postprocess);
       identifier_info = uu____15392;
       tc_hooks = (uu___417_15272.tc_hooks);
       dsenv = (uu___417_15272.dsenv);
       nbe = (uu___417_15272.nbe);
       strict_args_tab = uu____15415;
       erasable_types_tab = uu____15428
     })
  
let (pop_stack : unit -> env) =
  fun uu____15438  ->
    let uu____15439 = FStar_ST.op_Bang stack  in
    match uu____15439 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15493 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15583  ->
           let uu____15584 = snapshot_stack env1  in
           match uu____15584 with
           | (stack_depth,env2) ->
               let uu____15618 = snapshot_query_indices ()  in
               (match uu____15618 with
                | (query_indices_depth,()) ->
                    let uu____15651 = (env2.solver).snapshot msg  in
                    (match uu____15651 with
                     | (solver_depth,()) ->
                         let uu____15708 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____15708 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___442_15775 = env2  in
                                 {
                                   solver = (uu___442_15775.solver);
                                   range = (uu___442_15775.range);
                                   curmodule = (uu___442_15775.curmodule);
                                   gamma = (uu___442_15775.gamma);
                                   gamma_sig = (uu___442_15775.gamma_sig);
                                   gamma_cache = (uu___442_15775.gamma_cache);
                                   modules = (uu___442_15775.modules);
                                   expected_typ =
                                     (uu___442_15775.expected_typ);
                                   sigtab = (uu___442_15775.sigtab);
                                   attrtab = (uu___442_15775.attrtab);
                                   instantiate_imp =
                                     (uu___442_15775.instantiate_imp);
                                   effects = (uu___442_15775.effects);
                                   generalize = (uu___442_15775.generalize);
                                   letrecs = (uu___442_15775.letrecs);
                                   top_level = (uu___442_15775.top_level);
                                   check_uvars = (uu___442_15775.check_uvars);
                                   use_eq = (uu___442_15775.use_eq);
                                   use_eq_strict =
                                     (uu___442_15775.use_eq_strict);
                                   is_iface = (uu___442_15775.is_iface);
                                   admit = (uu___442_15775.admit);
                                   lax = (uu___442_15775.lax);
                                   lax_universes =
                                     (uu___442_15775.lax_universes);
                                   phase1 = (uu___442_15775.phase1);
                                   failhard = (uu___442_15775.failhard);
                                   nosynth = (uu___442_15775.nosynth);
                                   uvar_subtyping =
                                     (uu___442_15775.uvar_subtyping);
                                   tc_term = (uu___442_15775.tc_term);
                                   type_of = (uu___442_15775.type_of);
                                   universe_of = (uu___442_15775.universe_of);
                                   check_type_of =
                                     (uu___442_15775.check_type_of);
                                   use_bv_sorts =
                                     (uu___442_15775.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___442_15775.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___442_15775.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___442_15775.fv_delta_depths);
                                   proof_ns = (uu___442_15775.proof_ns);
                                   synth_hook = (uu___442_15775.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___442_15775.try_solve_implicits_hook);
                                   splice = (uu___442_15775.splice);
                                   mpreprocess = (uu___442_15775.mpreprocess);
                                   postprocess = (uu___442_15775.postprocess);
                                   identifier_info =
                                     (uu___442_15775.identifier_info);
                                   tc_hooks = (uu___442_15775.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___442_15775.nbe);
                                   strict_args_tab =
                                     (uu___442_15775.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___442_15775.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15809  ->
             let uu____15810 =
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
             match uu____15810 with
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
                             ((let uu____15990 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15990
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____16006 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____16006
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____16038,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____16080 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16110  ->
                  match uu____16110 with
                  | (m,uu____16118) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16080 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16132 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16132 next);
              (let uu___487_16135 = env1  in
               {
                 solver = (uu___487_16135.solver);
                 range = (uu___487_16135.range);
                 curmodule = (uu___487_16135.curmodule);
                 gamma = (uu___487_16135.gamma);
                 gamma_sig = (uu___487_16135.gamma_sig);
                 gamma_cache = (uu___487_16135.gamma_cache);
                 modules = (uu___487_16135.modules);
                 expected_typ = (uu___487_16135.expected_typ);
                 sigtab = (uu___487_16135.sigtab);
                 attrtab = (uu___487_16135.attrtab);
                 instantiate_imp = (uu___487_16135.instantiate_imp);
                 effects = (uu___487_16135.effects);
                 generalize = (uu___487_16135.generalize);
                 letrecs = (uu___487_16135.letrecs);
                 top_level = (uu___487_16135.top_level);
                 check_uvars = (uu___487_16135.check_uvars);
                 use_eq = (uu___487_16135.use_eq);
                 use_eq_strict = (uu___487_16135.use_eq_strict);
                 is_iface = (uu___487_16135.is_iface);
                 admit = (uu___487_16135.admit);
                 lax = (uu___487_16135.lax);
                 lax_universes = (uu___487_16135.lax_universes);
                 phase1 = (uu___487_16135.phase1);
                 failhard = (uu___487_16135.failhard);
                 nosynth = (uu___487_16135.nosynth);
                 uvar_subtyping = (uu___487_16135.uvar_subtyping);
                 tc_term = (uu___487_16135.tc_term);
                 type_of = (uu___487_16135.type_of);
                 universe_of = (uu___487_16135.universe_of);
                 check_type_of = (uu___487_16135.check_type_of);
                 use_bv_sorts = (uu___487_16135.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___487_16135.normalized_eff_names);
                 fv_delta_depths = (uu___487_16135.fv_delta_depths);
                 proof_ns = (uu___487_16135.proof_ns);
                 synth_hook = (uu___487_16135.synth_hook);
                 try_solve_implicits_hook =
                   (uu___487_16135.try_solve_implicits_hook);
                 splice = (uu___487_16135.splice);
                 mpreprocess = (uu___487_16135.mpreprocess);
                 postprocess = (uu___487_16135.postprocess);
                 identifier_info = (uu___487_16135.identifier_info);
                 tc_hooks = (uu___487_16135.tc_hooks);
                 dsenv = (uu___487_16135.dsenv);
                 nbe = (uu___487_16135.nbe);
                 strict_args_tab = (uu___487_16135.strict_args_tab);
                 erasable_types_tab = (uu___487_16135.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16152,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16167 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16167 next);
              (let uu___496_16170 = env1  in
               {
                 solver = (uu___496_16170.solver);
                 range = (uu___496_16170.range);
                 curmodule = (uu___496_16170.curmodule);
                 gamma = (uu___496_16170.gamma);
                 gamma_sig = (uu___496_16170.gamma_sig);
                 gamma_cache = (uu___496_16170.gamma_cache);
                 modules = (uu___496_16170.modules);
                 expected_typ = (uu___496_16170.expected_typ);
                 sigtab = (uu___496_16170.sigtab);
                 attrtab = (uu___496_16170.attrtab);
                 instantiate_imp = (uu___496_16170.instantiate_imp);
                 effects = (uu___496_16170.effects);
                 generalize = (uu___496_16170.generalize);
                 letrecs = (uu___496_16170.letrecs);
                 top_level = (uu___496_16170.top_level);
                 check_uvars = (uu___496_16170.check_uvars);
                 use_eq = (uu___496_16170.use_eq);
                 use_eq_strict = (uu___496_16170.use_eq_strict);
                 is_iface = (uu___496_16170.is_iface);
                 admit = (uu___496_16170.admit);
                 lax = (uu___496_16170.lax);
                 lax_universes = (uu___496_16170.lax_universes);
                 phase1 = (uu___496_16170.phase1);
                 failhard = (uu___496_16170.failhard);
                 nosynth = (uu___496_16170.nosynth);
                 uvar_subtyping = (uu___496_16170.uvar_subtyping);
                 tc_term = (uu___496_16170.tc_term);
                 type_of = (uu___496_16170.type_of);
                 universe_of = (uu___496_16170.universe_of);
                 check_type_of = (uu___496_16170.check_type_of);
                 use_bv_sorts = (uu___496_16170.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___496_16170.normalized_eff_names);
                 fv_delta_depths = (uu___496_16170.fv_delta_depths);
                 proof_ns = (uu___496_16170.proof_ns);
                 synth_hook = (uu___496_16170.synth_hook);
                 try_solve_implicits_hook =
                   (uu___496_16170.try_solve_implicits_hook);
                 splice = (uu___496_16170.splice);
                 mpreprocess = (uu___496_16170.mpreprocess);
                 postprocess = (uu___496_16170.postprocess);
                 identifier_info = (uu___496_16170.identifier_info);
                 tc_hooks = (uu___496_16170.tc_hooks);
                 dsenv = (uu___496_16170.dsenv);
                 nbe = (uu___496_16170.nbe);
                 strict_args_tab = (uu___496_16170.strict_args_tab);
                 erasable_types_tab = (uu___496_16170.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16199 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16199 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___503_16215 = e  in
         {
           solver = (uu___503_16215.solver);
           range = r;
           curmodule = (uu___503_16215.curmodule);
           gamma = (uu___503_16215.gamma);
           gamma_sig = (uu___503_16215.gamma_sig);
           gamma_cache = (uu___503_16215.gamma_cache);
           modules = (uu___503_16215.modules);
           expected_typ = (uu___503_16215.expected_typ);
           sigtab = (uu___503_16215.sigtab);
           attrtab = (uu___503_16215.attrtab);
           instantiate_imp = (uu___503_16215.instantiate_imp);
           effects = (uu___503_16215.effects);
           generalize = (uu___503_16215.generalize);
           letrecs = (uu___503_16215.letrecs);
           top_level = (uu___503_16215.top_level);
           check_uvars = (uu___503_16215.check_uvars);
           use_eq = (uu___503_16215.use_eq);
           use_eq_strict = (uu___503_16215.use_eq_strict);
           is_iface = (uu___503_16215.is_iface);
           admit = (uu___503_16215.admit);
           lax = (uu___503_16215.lax);
           lax_universes = (uu___503_16215.lax_universes);
           phase1 = (uu___503_16215.phase1);
           failhard = (uu___503_16215.failhard);
           nosynth = (uu___503_16215.nosynth);
           uvar_subtyping = (uu___503_16215.uvar_subtyping);
           tc_term = (uu___503_16215.tc_term);
           type_of = (uu___503_16215.type_of);
           universe_of = (uu___503_16215.universe_of);
           check_type_of = (uu___503_16215.check_type_of);
           use_bv_sorts = (uu___503_16215.use_bv_sorts);
           qtbl_name_and_index = (uu___503_16215.qtbl_name_and_index);
           normalized_eff_names = (uu___503_16215.normalized_eff_names);
           fv_delta_depths = (uu___503_16215.fv_delta_depths);
           proof_ns = (uu___503_16215.proof_ns);
           synth_hook = (uu___503_16215.synth_hook);
           try_solve_implicits_hook =
             (uu___503_16215.try_solve_implicits_hook);
           splice = (uu___503_16215.splice);
           mpreprocess = (uu___503_16215.mpreprocess);
           postprocess = (uu___503_16215.postprocess);
           identifier_info = (uu___503_16215.identifier_info);
           tc_hooks = (uu___503_16215.tc_hooks);
           dsenv = (uu___503_16215.dsenv);
           nbe = (uu___503_16215.nbe);
           strict_args_tab = (uu___503_16215.strict_args_tab);
           erasable_types_tab = (uu___503_16215.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16235 =
        let uu____16236 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16236 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16235
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16291 =
          let uu____16292 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16292 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16291
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16347 =
          let uu____16348 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16348 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16347
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16403 =
        let uu____16404 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16404 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16403
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___520_16468 = env1  in
      {
        solver = (uu___520_16468.solver);
        range = (uu___520_16468.range);
        curmodule = lid;
        gamma = (uu___520_16468.gamma);
        gamma_sig = (uu___520_16468.gamma_sig);
        gamma_cache = (uu___520_16468.gamma_cache);
        modules = (uu___520_16468.modules);
        expected_typ = (uu___520_16468.expected_typ);
        sigtab = (uu___520_16468.sigtab);
        attrtab = (uu___520_16468.attrtab);
        instantiate_imp = (uu___520_16468.instantiate_imp);
        effects = (uu___520_16468.effects);
        generalize = (uu___520_16468.generalize);
        letrecs = (uu___520_16468.letrecs);
        top_level = (uu___520_16468.top_level);
        check_uvars = (uu___520_16468.check_uvars);
        use_eq = (uu___520_16468.use_eq);
        use_eq_strict = (uu___520_16468.use_eq_strict);
        is_iface = (uu___520_16468.is_iface);
        admit = (uu___520_16468.admit);
        lax = (uu___520_16468.lax);
        lax_universes = (uu___520_16468.lax_universes);
        phase1 = (uu___520_16468.phase1);
        failhard = (uu___520_16468.failhard);
        nosynth = (uu___520_16468.nosynth);
        uvar_subtyping = (uu___520_16468.uvar_subtyping);
        tc_term = (uu___520_16468.tc_term);
        type_of = (uu___520_16468.type_of);
        universe_of = (uu___520_16468.universe_of);
        check_type_of = (uu___520_16468.check_type_of);
        use_bv_sorts = (uu___520_16468.use_bv_sorts);
        qtbl_name_and_index = (uu___520_16468.qtbl_name_and_index);
        normalized_eff_names = (uu___520_16468.normalized_eff_names);
        fv_delta_depths = (uu___520_16468.fv_delta_depths);
        proof_ns = (uu___520_16468.proof_ns);
        synth_hook = (uu___520_16468.synth_hook);
        try_solve_implicits_hook = (uu___520_16468.try_solve_implicits_hook);
        splice = (uu___520_16468.splice);
        mpreprocess = (uu___520_16468.mpreprocess);
        postprocess = (uu___520_16468.postprocess);
        identifier_info = (uu___520_16468.identifier_info);
        tc_hooks = (uu___520_16468.tc_hooks);
        dsenv = (uu___520_16468.dsenv);
        nbe = (uu___520_16468.nbe);
        strict_args_tab = (uu___520_16468.strict_args_tab);
        erasable_types_tab = (uu___520_16468.erasable_types_tab)
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
      let uu____16499 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16499
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16512 =
      let uu____16514 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____16514  in
    (FStar_Errors.Fatal_NameNotFound, uu____16512)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16529 =
      let uu____16531 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16531  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16529)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16540  ->
    let uu____16541 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
    FStar_Syntax_Syntax.U_unif uu____16541
  
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
      | ((formals,t),uu____16643) ->
          let vs = mk_univ_subst formals us  in
          let uu____16667 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16667)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16684  ->
    match uu___1_16684 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16710  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16730 = inst_tscheme t  in
      match uu____16730 with
      | (us,t1) ->
          let uu____16741 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16741)
  
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
          let uu____16766 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16768 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16766 uu____16768
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
        fun uu____16795  ->
          match uu____16795 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16809 =
                    let uu____16811 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16815 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16819 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16821 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16811 uu____16815 uu____16819 uu____16821
                     in
                  failwith uu____16809)
               else ();
               (let uu____16826 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16826))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16844 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16855 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16866 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____16880 =
        let uu____16882 = FStar_Ident.nsstr l  in
        let uu____16884 = FStar_Ident.string_of_lid cur  in
        uu____16882 = uu____16884  in
      if uu____16880
      then Yes
      else
        (let uu____16890 =
           let uu____16892 = FStar_Ident.nsstr l  in
           let uu____16894 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____16892 uu____16894  in
         if uu____16890
         then
           let lns =
             let uu____16900 = FStar_Ident.ns_of_lid l  in
             let uu____16903 =
               let uu____16906 = FStar_Ident.ident_of_lid l  in [uu____16906]
                in
             FStar_List.append uu____16900 uu____16903  in
           let cur1 =
             let uu____16910 = FStar_Ident.ns_of_lid cur  in
             let uu____16913 =
               let uu____16916 = FStar_Ident.ident_of_lid cur  in
               [uu____16916]  in
             FStar_List.append uu____16910 uu____16913  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____16940) -> Maybe
             | (uu____16947,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____16966 = FStar_Ident.text_of_id hd  in
                 let uu____16968 = FStar_Ident.text_of_id hd'  in
                 uu____16966 = uu____16968 -> aux tl tl'
             | uu____16971 -> No  in
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
        (let uu____17023 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17023 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17067 =
            let uu____17070 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17070  in
          match uu____17067 with
          | FStar_Pervasives_Native.None  ->
              let uu____17092 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17136  ->
                     match uu___2_17136 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17175 = FStar_Ident.lid_equals lid l  in
                         if uu____17175
                         then
                           let uu____17198 =
                             let uu____17217 =
                               let uu____17232 = inst_tscheme t  in
                               FStar_Util.Inl uu____17232  in
                             let uu____17247 = FStar_Ident.range_of_lid l  in
                             (uu____17217, uu____17247)  in
                           FStar_Pervasives_Native.Some uu____17198
                         else FStar_Pervasives_Native.None
                     | uu____17300 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17092
                (fun uu____17338  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17348  ->
                        match uu___3_17348 with
                        | (uu____17351,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17353);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17354;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17355;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17356;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17357;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17358;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17380 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17380
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
                                  uu____17432 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17439 -> cache t  in
                            let uu____17440 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17440 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17446 =
                                   let uu____17447 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17447)
                                    in
                                 maybe_cache uu____17446)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17518 = find_in_sigtab env1 lid  in
         match uu____17518 with
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
      let uu____17599 = lookup_qname env1 lid  in
      match uu____17599 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17620,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17734 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17734 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17779 =
          let uu____17782 = lookup_attr env2 attr  in se1 :: uu____17782  in
        FStar_Util.smap_add (attrtab env2) attr uu____17779  in
      FStar_List.iter
        (fun attr  ->
           let uu____17792 =
             let uu____17793 = FStar_Syntax_Subst.compress attr  in
             uu____17793.FStar_Syntax_Syntax.n  in
           match uu____17792 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17797 =
                 let uu____17799 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17799  in
               add_one env1 se uu____17797
           | uu____17800 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17823) ->
          add_sigelts env1 ses
      | uu____17832 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17840 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17840 se) lids;
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
        (fun uu___4_17874  ->
           match uu___4_17874 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____17884 =
                 let uu____17891 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____17891)  in
               FStar_Pervasives_Native.Some uu____17884
           | uu____17900 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17962,lb::[]),uu____17964) ->
            let uu____17973 =
              let uu____17982 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17991 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17982, uu____17991)  in
            FStar_Pervasives_Native.Some uu____17973
        | FStar_Syntax_Syntax.Sig_let ((uu____18004,lbs),uu____18006) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18038 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18051 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18051
                     then
                       let uu____18064 =
                         let uu____18073 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18082 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18073, uu____18082)  in
                       FStar_Pervasives_Native.Some uu____18064
                     else FStar_Pervasives_Native.None)
        | uu____18105 -> FStar_Pervasives_Native.None
  
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
                    let uu____18197 =
                      let uu____18199 =
                        let uu____18201 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18203 =
                          let uu____18205 =
                            let uu____18207 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18213 =
                              let uu____18215 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18215  in
                            Prims.op_Hat uu____18207 uu____18213  in
                          Prims.op_Hat ", expected " uu____18205  in
                        Prims.op_Hat uu____18201 uu____18203  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18199
                       in
                    failwith uu____18197
                  else ());
             (let uu____18222 =
                let uu____18231 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18231, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18222))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18251,uu____18252) ->
            let uu____18257 =
              let uu____18266 =
                let uu____18271 =
                  let uu____18272 =
                    let uu____18275 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18275  in
                  (us, uu____18272)  in
                inst_ts us_opt uu____18271  in
              (uu____18266, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18257
        | uu____18294 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18383 =
          match uu____18383 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18479,uvs,t,uu____18482,uu____18483,uu____18484);
                      FStar_Syntax_Syntax.sigrng = uu____18485;
                      FStar_Syntax_Syntax.sigquals = uu____18486;
                      FStar_Syntax_Syntax.sigmeta = uu____18487;
                      FStar_Syntax_Syntax.sigattrs = uu____18488;
                      FStar_Syntax_Syntax.sigopts = uu____18489;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18514 =
                     let uu____18523 = inst_tscheme1 (uvs, t)  in
                     (uu____18523, rng)  in
                   FStar_Pervasives_Native.Some uu____18514
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18547;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18549;
                      FStar_Syntax_Syntax.sigattrs = uu____18550;
                      FStar_Syntax_Syntax.sigopts = uu____18551;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18570 =
                     let uu____18572 = in_cur_mod env1 l  in
                     uu____18572 = Yes  in
                   if uu____18570
                   then
                     let uu____18584 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18584
                      then
                        let uu____18600 =
                          let uu____18609 = inst_tscheme1 (uvs, t)  in
                          (uu____18609, rng)  in
                        FStar_Pervasives_Native.Some uu____18600
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18642 =
                        let uu____18651 = inst_tscheme1 (uvs, t)  in
                        (uu____18651, rng)  in
                      FStar_Pervasives_Native.Some uu____18642)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18676,uu____18677);
                      FStar_Syntax_Syntax.sigrng = uu____18678;
                      FStar_Syntax_Syntax.sigquals = uu____18679;
                      FStar_Syntax_Syntax.sigmeta = uu____18680;
                      FStar_Syntax_Syntax.sigattrs = uu____18681;
                      FStar_Syntax_Syntax.sigopts = uu____18682;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18725 =
                          let uu____18734 = inst_tscheme1 (uvs, k)  in
                          (uu____18734, rng)  in
                        FStar_Pervasives_Native.Some uu____18725
                    | uu____18755 ->
                        let uu____18756 =
                          let uu____18765 =
                            let uu____18770 =
                              let uu____18771 =
                                let uu____18774 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18774
                                 in
                              (uvs, uu____18771)  in
                            inst_tscheme1 uu____18770  in
                          (uu____18765, rng)  in
                        FStar_Pervasives_Native.Some uu____18756)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18797,uu____18798);
                      FStar_Syntax_Syntax.sigrng = uu____18799;
                      FStar_Syntax_Syntax.sigquals = uu____18800;
                      FStar_Syntax_Syntax.sigmeta = uu____18801;
                      FStar_Syntax_Syntax.sigattrs = uu____18802;
                      FStar_Syntax_Syntax.sigopts = uu____18803;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18847 =
                          let uu____18856 = inst_tscheme_with (uvs, k) us  in
                          (uu____18856, rng)  in
                        FStar_Pervasives_Native.Some uu____18847
                    | uu____18877 ->
                        let uu____18878 =
                          let uu____18887 =
                            let uu____18892 =
                              let uu____18893 =
                                let uu____18896 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18896
                                 in
                              (uvs, uu____18893)  in
                            inst_tscheme_with uu____18892 us  in
                          (uu____18887, rng)  in
                        FStar_Pervasives_Native.Some uu____18878)
               | FStar_Util.Inr se ->
                   let uu____18932 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18953;
                          FStar_Syntax_Syntax.sigrng = uu____18954;
                          FStar_Syntax_Syntax.sigquals = uu____18955;
                          FStar_Syntax_Syntax.sigmeta = uu____18956;
                          FStar_Syntax_Syntax.sigattrs = uu____18957;
                          FStar_Syntax_Syntax.sigopts = uu____18958;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18975 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____18932
                     (FStar_Util.map_option
                        (fun uu____19023  ->
                           match uu____19023 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19054 =
          let uu____19065 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19065 mapper  in
        match uu____19054 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19139 =
              let uu____19150 =
                let uu____19157 =
                  let uu___857_19160 = t  in
                  let uu____19161 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___857_19160.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19161;
                    FStar_Syntax_Syntax.vars =
                      (uu___857_19160.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19157)  in
              (uu____19150, r)  in
            FStar_Pervasives_Native.Some uu____19139
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19210 = lookup_qname env1 l  in
      match uu____19210 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19231 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19285 = try_lookup_bv env1 bv  in
      match uu____19285 with
      | FStar_Pervasives_Native.None  ->
          let uu____19300 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19300 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19316 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19317 =
            let uu____19318 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19318  in
          (uu____19316, uu____19317)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19340 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19340 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19406 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19406  in
          let uu____19407 =
            let uu____19416 =
              let uu____19421 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19421)  in
            (uu____19416, r1)  in
          FStar_Pervasives_Native.Some uu____19407
  
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
        let uu____19456 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19456 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19489,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19514 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19514  in
            let uu____19515 =
              let uu____19520 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19520, r1)  in
            FStar_Pervasives_Native.Some uu____19515
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19544 = try_lookup_lid env1 l  in
      match uu____19544 with
      | FStar_Pervasives_Native.None  ->
          let uu____19571 = name_not_found l  in
          let uu____19577 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19571 uu____19577
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19622  ->
              match uu___5_19622 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19625 = FStar_Ident.text_of_id x  in
                  let uu____19627 = FStar_Ident.text_of_id y  in
                  uu____19625 = uu____19627
              | uu____19630 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19651 = lookup_qname env1 lid  in
      match uu____19651 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19660,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19663;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19665;
              FStar_Syntax_Syntax.sigattrs = uu____19666;
              FStar_Syntax_Syntax.sigopts = uu____19667;_},FStar_Pervasives_Native.None
            ),uu____19668)
          ->
          let uu____19719 =
            let uu____19726 =
              let uu____19727 =
                let uu____19730 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19730 t  in
              (uvs, uu____19727)  in
            (uu____19726, q)  in
          FStar_Pervasives_Native.Some uu____19719
      | uu____19743 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19765 = lookup_qname env1 lid  in
      match uu____19765 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19770,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19773;
              FStar_Syntax_Syntax.sigquals = uu____19774;
              FStar_Syntax_Syntax.sigmeta = uu____19775;
              FStar_Syntax_Syntax.sigattrs = uu____19776;
              FStar_Syntax_Syntax.sigopts = uu____19777;_},FStar_Pervasives_Native.None
            ),uu____19778)
          ->
          let uu____19829 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19829 (uvs, t)
      | uu____19834 ->
          let uu____19835 = name_not_found lid  in
          let uu____19841 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19835 uu____19841
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19861 = lookup_qname env1 lid  in
      match uu____19861 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19866,uvs,t,uu____19869,uu____19870,uu____19871);
              FStar_Syntax_Syntax.sigrng = uu____19872;
              FStar_Syntax_Syntax.sigquals = uu____19873;
              FStar_Syntax_Syntax.sigmeta = uu____19874;
              FStar_Syntax_Syntax.sigattrs = uu____19875;
              FStar_Syntax_Syntax.sigopts = uu____19876;_},FStar_Pervasives_Native.None
            ),uu____19877)
          ->
          let uu____19934 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19934 (uvs, t)
      | uu____19939 ->
          let uu____19940 = name_not_found lid  in
          let uu____19946 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19940 uu____19946
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____19969 = lookup_qname env1 lid  in
      match uu____19969 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19977,uu____19978,uu____19979,uu____19980,uu____19981,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19983;
              FStar_Syntax_Syntax.sigquals = uu____19984;
              FStar_Syntax_Syntax.sigmeta = uu____19985;
              FStar_Syntax_Syntax.sigattrs = uu____19986;
              FStar_Syntax_Syntax.sigopts = uu____19987;_},uu____19988),uu____19989)
          -> (true, dcs)
      | uu____20054 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20070 = lookup_qname env1 lid  in
      match uu____20070 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20071,uu____20072,uu____20073,l,uu____20075,uu____20076);
              FStar_Syntax_Syntax.sigrng = uu____20077;
              FStar_Syntax_Syntax.sigquals = uu____20078;
              FStar_Syntax_Syntax.sigmeta = uu____20079;
              FStar_Syntax_Syntax.sigattrs = uu____20080;
              FStar_Syntax_Syntax.sigopts = uu____20081;_},uu____20082),uu____20083)
          -> l
      | uu____20142 ->
          let uu____20143 =
            let uu____20145 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20145  in
          failwith uu____20143
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20215)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20272) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20296 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20296
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20331 -> FStar_Pervasives_Native.None)
          | uu____20340 -> FStar_Pervasives_Native.None
  
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
        let uu____20402 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20402
  
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
        let uu____20435 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20435
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20459 =
        let uu____20461 = FStar_Ident.nsstr lid  in uu____20461 = "Prims"  in
      if uu____20459
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20491,uu____20492) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20541),uu____20542) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20591 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20609 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20619 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20636 ->
                  let uu____20643 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20643
              | FStar_Syntax_Syntax.Sig_let ((uu____20644,lbs),uu____20646)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20662 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20662
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20669 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20685 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____20695 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20702 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20703 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20704 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20717 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20718 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20741 =
        let uu____20743 = FStar_Ident.nsstr lid  in uu____20743 = "Prims"  in
      if uu____20741
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20750 =
           let uu____20753 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20753
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20750
           (fun d_opt  ->
              let uu____20765 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20765
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20775 =
                   let uu____20778 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20778  in
                 match uu____20775 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20779 =
                       let uu____20781 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20781
                        in
                     failwith uu____20779
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20786 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20786
                       then
                         let uu____20789 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20791 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20793 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20789 uu____20791 uu____20793
                       else ());
                      (let uu____20799 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20799 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20820),uu____20821) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20870 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20892),uu____20893) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20942 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20964 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20964
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20997 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____20997 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21019 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21028 =
                        let uu____21029 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21029.FStar_Syntax_Syntax.n  in
                      match uu____21028 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21034 -> false))
               in
            (true, uu____21019)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21057 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21057
  
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
          let uu____21129 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21129  in
        let uu____21130 = FStar_Util.smap_try_find tab s  in
        match uu____21130 with
        | FStar_Pervasives_Native.None  ->
            let uu____21133 = f ()  in
            (match uu____21133 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21171 =
        let uu____21172 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21172 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21206 =
        let uu____21207 = FStar_Syntax_Util.unrefine t  in
        uu____21207.FStar_Syntax_Syntax.n  in
      match uu____21206 with
      | FStar_Syntax_Syntax.Tm_type uu____21211 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21215) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21241) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21246,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21268 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21301 =
        let attrs =
          let uu____21307 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21307  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21347 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21347)
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
      let uu____21392 = lookup_qname env1 ftv  in
      match uu____21392 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21396) ->
          let uu____21441 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21441 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21462,t),r) ->
               let uu____21477 =
                 let uu____21478 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21478 t  in
               FStar_Pervasives_Native.Some uu____21477)
      | uu____21479 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21491 = try_lookup_effect_lid env1 ftv  in
      match uu____21491 with
      | FStar_Pervasives_Native.None  ->
          let uu____21494 = name_not_found ftv  in
          let uu____21500 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21494 uu____21500
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
        let uu____21524 = lookup_qname env1 lid0  in
        match uu____21524 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21535);
                FStar_Syntax_Syntax.sigrng = uu____21536;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21538;
                FStar_Syntax_Syntax.sigattrs = uu____21539;
                FStar_Syntax_Syntax.sigopts = uu____21540;_},FStar_Pervasives_Native.None
              ),uu____21541)
            ->
            let lid1 =
              let uu____21597 =
                let uu____21598 = FStar_Ident.range_of_lid lid  in
                let uu____21599 =
                  let uu____21600 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21600  in
                FStar_Range.set_use_range uu____21598 uu____21599  in
              FStar_Ident.set_lid_range lid uu____21597  in
            let uu____21601 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21607  ->
                      match uu___6_21607 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21610 -> false))
               in
            if uu____21601
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21629 =
                      let uu____21631 =
                        let uu____21633 = get_range env1  in
                        FStar_Range.string_of_range uu____21633  in
                      let uu____21634 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21636 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21631 uu____21634 uu____21636
                       in
                    failwith uu____21629)
                  in
               match (binders, univs) with
               | ([],uu____21657) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21683,uu____21684::uu____21685::uu____21686) ->
                   let uu____21707 =
                     let uu____21709 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21711 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21709 uu____21711
                      in
                   failwith uu____21707
               | uu____21722 ->
                   let uu____21737 =
                     let uu____21742 =
                       let uu____21743 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21743)  in
                     inst_tscheme_with uu____21742 insts  in
                   (match uu____21737 with
                    | (uu____21756,t) ->
                        let t1 =
                          let uu____21759 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21759 t  in
                        let uu____21760 =
                          let uu____21761 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21761.FStar_Syntax_Syntax.n  in
                        (match uu____21760 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21796 -> failwith "Impossible")))
        | uu____21804 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21828 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21828 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21841,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21848 = find l2  in
            (match uu____21848 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21855 =
          let uu____21858 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____21858  in
        match uu____21855 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21861 = find l  in
            (match uu____21861 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____21866 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____21866
                     m);
                  m))
         in
      let uu____21868 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21868
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21889 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____21889 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21895) ->
            FStar_List.length bs
        | uu____21934 ->
            let uu____21935 =
              let uu____21941 =
                let uu____21943 = FStar_Ident.string_of_lid name  in
                let uu____21945 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21943 uu____21945
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21941)
               in
            FStar_Errors.raise_error uu____21935 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____21964 = lookup_qname env1 l1  in
      match uu____21964 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21967;
              FStar_Syntax_Syntax.sigrng = uu____21968;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21970;
              FStar_Syntax_Syntax.sigattrs = uu____21971;
              FStar_Syntax_Syntax.sigopts = uu____21972;_},uu____21973),uu____21974)
          -> q
      | uu____22027 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22051 =
          let uu____22052 =
            let uu____22054 = FStar_Util.string_of_int i  in
            let uu____22056 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22054 uu____22056
             in
          failwith uu____22052  in
        let uu____22059 = lookup_datacon env1 lid  in
        match uu____22059 with
        | (uu____22064,t) ->
            let uu____22066 =
              let uu____22067 = FStar_Syntax_Subst.compress t  in
              uu____22067.FStar_Syntax_Syntax.n  in
            (match uu____22066 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22071) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22117 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22131 = lookup_qname env1 l  in
      match uu____22131 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22133,uu____22134,uu____22135);
              FStar_Syntax_Syntax.sigrng = uu____22136;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22138;
              FStar_Syntax_Syntax.sigattrs = uu____22139;
              FStar_Syntax_Syntax.sigopts = uu____22140;_},uu____22141),uu____22142)
          ->
          FStar_Util.for_some
            (fun uu___7_22197  ->
               match uu___7_22197 with
               | FStar_Syntax_Syntax.Projector uu____22199 -> true
               | uu____22205 -> false) quals
      | uu____22207 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22221 = lookup_qname env1 lid  in
      match uu____22221 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22223,uu____22224,uu____22225,uu____22226,uu____22227,uu____22228);
              FStar_Syntax_Syntax.sigrng = uu____22229;
              FStar_Syntax_Syntax.sigquals = uu____22230;
              FStar_Syntax_Syntax.sigmeta = uu____22231;
              FStar_Syntax_Syntax.sigattrs = uu____22232;
              FStar_Syntax_Syntax.sigopts = uu____22233;_},uu____22234),uu____22235)
          -> true
      | uu____22295 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22309 = lookup_qname env1 lid  in
      match uu____22309 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22311,uu____22312,uu____22313,uu____22314,uu____22315,uu____22316);
              FStar_Syntax_Syntax.sigrng = uu____22317;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22319;
              FStar_Syntax_Syntax.sigattrs = uu____22320;
              FStar_Syntax_Syntax.sigopts = uu____22321;_},uu____22322),uu____22323)
          ->
          FStar_Util.for_some
            (fun uu___8_22386  ->
               match uu___8_22386 with
               | FStar_Syntax_Syntax.RecordType uu____22388 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22398 -> true
               | uu____22408 -> false) quals
      | uu____22410 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22420,uu____22421);
            FStar_Syntax_Syntax.sigrng = uu____22422;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22424;
            FStar_Syntax_Syntax.sigattrs = uu____22425;
            FStar_Syntax_Syntax.sigopts = uu____22426;_},uu____22427),uu____22428)
        ->
        FStar_Util.for_some
          (fun uu___9_22487  ->
             match uu___9_22487 with
             | FStar_Syntax_Syntax.Action uu____22489 -> true
             | uu____22491 -> false) quals
    | uu____22493 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22507 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22507
  
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
      let uu____22524 =
        let uu____22525 = FStar_Syntax_Util.un_uinst head  in
        uu____22525.FStar_Syntax_Syntax.n  in
      match uu____22524 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22531 ->
               true
           | uu____22534 -> false)
      | uu____22536 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22550 = lookup_qname env1 l  in
      match uu____22550 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22553),uu____22554) ->
          FStar_Util.for_some
            (fun uu___10_22602  ->
               match uu___10_22602 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22605 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22607 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22683 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22701) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22719 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22727 ->
                 FStar_Pervasives_Native.Some true
             | uu____22746 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22749 =
        let uu____22753 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22753 mapper  in
      match uu____22749 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22813 = lookup_qname env1 lid  in
      match uu____22813 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22817,uu____22818,tps,uu____22820,uu____22821,uu____22822);
              FStar_Syntax_Syntax.sigrng = uu____22823;
              FStar_Syntax_Syntax.sigquals = uu____22824;
              FStar_Syntax_Syntax.sigmeta = uu____22825;
              FStar_Syntax_Syntax.sigattrs = uu____22826;
              FStar_Syntax_Syntax.sigopts = uu____22827;_},uu____22828),uu____22829)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22897 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22943  ->
              match uu____22943 with
              | (d,uu____22952) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____22968 = effect_decl_opt env1 l  in
      match uu____22968 with
      | FStar_Pervasives_Native.None  ->
          let uu____22983 = name_not_found l  in
          let uu____22989 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22983 uu____22989
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23017 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23017 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23024  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23038  ->
            fun uu____23039  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23073 = FStar_Ident.lid_equals l1 l2  in
        if uu____23073
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23092 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23092
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23111 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23164  ->
                        match uu____23164 with
                        | (m1,m2,uu____23178,uu____23179,uu____23180) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23111 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23205,uu____23206,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23254 = join_opt env1 l1 l2  in
        match uu____23254 with
        | FStar_Pervasives_Native.None  ->
            let uu____23275 =
              let uu____23281 =
                let uu____23283 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23285 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23283 uu____23285
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23281)  in
            FStar_Errors.raise_error uu____23275 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23328 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23328
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
  'uuuuuu23348 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23348) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23377 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23403  ->
                match uu____23403 with
                | (d,uu____23410) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23377 with
      | FStar_Pervasives_Native.None  ->
          let uu____23421 =
            let uu____23423 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23423
             in
          failwith uu____23421
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23438 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23438 with
           | (uu____23449,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23467)::(wp,uu____23469)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23525 -> failwith "Impossible"))
  
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
        | uu____23590 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23603 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23603 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23620 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23620 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23645 =
                     let uu____23651 =
                       let uu____23653 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23661 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23672 =
                         let uu____23674 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23674  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23653 uu____23661 uu____23672
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23651)
                      in
                   FStar_Errors.raise_error uu____23645
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23682 =
                     let uu____23693 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23693 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23730  ->
                        fun uu____23731  ->
                          match (uu____23730, uu____23731) with
                          | ((x,uu____23761),(t,uu____23763)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23682
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23794 =
                     let uu___1611_23795 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1611_23795.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1611_23795.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1611_23795.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1611_23795.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23794
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23807 .
    'uuuuuu23807 ->
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
            let uu____23848 =
              let uu____23855 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____23855)  in
            match uu____23848 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23879 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23881 = FStar_Util.string_of_int given  in
                     let uu____23883 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23879 uu____23881 uu____23883
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23888 = effect_decl_opt env1 effect_name  in
          match uu____23888 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23910) ->
              let uu____23921 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23921 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23939 =
                       let uu____23942 = get_range env1  in
                       let uu____23943 =
                         let uu____23950 =
                           let uu____23951 =
                             let uu____23968 =
                               let uu____23979 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23979 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23968)  in
                           FStar_Syntax_Syntax.Tm_app uu____23951  in
                         FStar_Syntax_Syntax.mk uu____23950  in
                       uu____23943 FStar_Pervasives_Native.None uu____23942
                        in
                     FStar_Pervasives_Native.Some uu____23939)))
  
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
           (fun uu___11_24079  ->
              match uu___11_24079 with
              | FStar_Syntax_Syntax.Reflectable uu____24081 -> true
              | uu____24083 -> false))
  
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
      | uu____24143 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24158 =
        let uu____24159 = FStar_Syntax_Subst.compress t  in
        uu____24159.FStar_Syntax_Syntax.n  in
      match uu____24158 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24163,c) ->
          is_reifiable_comp env1 c
      | uu____24185 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24205 =
           let uu____24207 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24207  in
         if uu____24205
         then
           let uu____24210 =
             let uu____24216 =
               let uu____24218 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24218
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24216)  in
           let uu____24222 = get_range env1  in
           FStar_Errors.raise_error uu____24210 uu____24222
         else ());
        (let uu____24225 = effect_repr_aux true env1 c u_c  in
         match uu____24225 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1688_24261 = env1  in
        {
          solver = (uu___1688_24261.solver);
          range = (uu___1688_24261.range);
          curmodule = (uu___1688_24261.curmodule);
          gamma = (uu___1688_24261.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1688_24261.gamma_cache);
          modules = (uu___1688_24261.modules);
          expected_typ = (uu___1688_24261.expected_typ);
          sigtab = (uu___1688_24261.sigtab);
          attrtab = (uu___1688_24261.attrtab);
          instantiate_imp = (uu___1688_24261.instantiate_imp);
          effects = (uu___1688_24261.effects);
          generalize = (uu___1688_24261.generalize);
          letrecs = (uu___1688_24261.letrecs);
          top_level = (uu___1688_24261.top_level);
          check_uvars = (uu___1688_24261.check_uvars);
          use_eq = (uu___1688_24261.use_eq);
          use_eq_strict = (uu___1688_24261.use_eq_strict);
          is_iface = (uu___1688_24261.is_iface);
          admit = (uu___1688_24261.admit);
          lax = (uu___1688_24261.lax);
          lax_universes = (uu___1688_24261.lax_universes);
          phase1 = (uu___1688_24261.phase1);
          failhard = (uu___1688_24261.failhard);
          nosynth = (uu___1688_24261.nosynth);
          uvar_subtyping = (uu___1688_24261.uvar_subtyping);
          tc_term = (uu___1688_24261.tc_term);
          type_of = (uu___1688_24261.type_of);
          universe_of = (uu___1688_24261.universe_of);
          check_type_of = (uu___1688_24261.check_type_of);
          use_bv_sorts = (uu___1688_24261.use_bv_sorts);
          qtbl_name_and_index = (uu___1688_24261.qtbl_name_and_index);
          normalized_eff_names = (uu___1688_24261.normalized_eff_names);
          fv_delta_depths = (uu___1688_24261.fv_delta_depths);
          proof_ns = (uu___1688_24261.proof_ns);
          synth_hook = (uu___1688_24261.synth_hook);
          try_solve_implicits_hook =
            (uu___1688_24261.try_solve_implicits_hook);
          splice = (uu___1688_24261.splice);
          mpreprocess = (uu___1688_24261.mpreprocess);
          postprocess = (uu___1688_24261.postprocess);
          identifier_info = (uu___1688_24261.identifier_info);
          tc_hooks = (uu___1688_24261.tc_hooks);
          dsenv = (uu___1688_24261.dsenv);
          nbe = (uu___1688_24261.nbe);
          strict_args_tab = (uu___1688_24261.strict_args_tab);
          erasable_types_tab = (uu___1688_24261.erasable_types_tab)
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
    fun uu____24280  ->
      match uu____24280 with
      | (ed,quals) ->
          let effects1 =
            let uu___1697_24294 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1697_24294.order);
              joins = (uu___1697_24294.joins);
              polymonadic_binds = (uu___1697_24294.polymonadic_binds);
              polymonadic_subcomps = (uu___1697_24294.polymonadic_subcomps)
            }  in
          let uu___1700_24303 = env1  in
          {
            solver = (uu___1700_24303.solver);
            range = (uu___1700_24303.range);
            curmodule = (uu___1700_24303.curmodule);
            gamma = (uu___1700_24303.gamma);
            gamma_sig = (uu___1700_24303.gamma_sig);
            gamma_cache = (uu___1700_24303.gamma_cache);
            modules = (uu___1700_24303.modules);
            expected_typ = (uu___1700_24303.expected_typ);
            sigtab = (uu___1700_24303.sigtab);
            attrtab = (uu___1700_24303.attrtab);
            instantiate_imp = (uu___1700_24303.instantiate_imp);
            effects = effects1;
            generalize = (uu___1700_24303.generalize);
            letrecs = (uu___1700_24303.letrecs);
            top_level = (uu___1700_24303.top_level);
            check_uvars = (uu___1700_24303.check_uvars);
            use_eq = (uu___1700_24303.use_eq);
            use_eq_strict = (uu___1700_24303.use_eq_strict);
            is_iface = (uu___1700_24303.is_iface);
            admit = (uu___1700_24303.admit);
            lax = (uu___1700_24303.lax);
            lax_universes = (uu___1700_24303.lax_universes);
            phase1 = (uu___1700_24303.phase1);
            failhard = (uu___1700_24303.failhard);
            nosynth = (uu___1700_24303.nosynth);
            uvar_subtyping = (uu___1700_24303.uvar_subtyping);
            tc_term = (uu___1700_24303.tc_term);
            type_of = (uu___1700_24303.type_of);
            universe_of = (uu___1700_24303.universe_of);
            check_type_of = (uu___1700_24303.check_type_of);
            use_bv_sorts = (uu___1700_24303.use_bv_sorts);
            qtbl_name_and_index = (uu___1700_24303.qtbl_name_and_index);
            normalized_eff_names = (uu___1700_24303.normalized_eff_names);
            fv_delta_depths = (uu___1700_24303.fv_delta_depths);
            proof_ns = (uu___1700_24303.proof_ns);
            synth_hook = (uu___1700_24303.synth_hook);
            try_solve_implicits_hook =
              (uu___1700_24303.try_solve_implicits_hook);
            splice = (uu___1700_24303.splice);
            mpreprocess = (uu___1700_24303.mpreprocess);
            postprocess = (uu___1700_24303.postprocess);
            identifier_info = (uu___1700_24303.identifier_info);
            tc_hooks = (uu___1700_24303.tc_hooks);
            dsenv = (uu___1700_24303.dsenv);
            nbe = (uu___1700_24303.nbe);
            strict_args_tab = (uu___1700_24303.strict_args_tab);
            erasable_types_tab = (uu___1700_24303.erasable_types_tab)
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
        let uu____24332 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24400  ->
                  match uu____24400 with
                  | (m1,n1,uu____24418,uu____24419) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24332 with
        | FStar_Pervasives_Native.Some (uu____24444,uu____24445,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24490 -> FStar_Pervasives_Native.None
  
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        let uu____24535 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____24570  ->
                  match uu____24570 with
                  | (m1,n1,uu____24580) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24535 with
        | FStar_Pervasives_Native.Some (uu____24583,uu____24584,ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____24592 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24649 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24649
                  (fun uu____24670  ->
                     match uu____24670 with
                     | (c1,g1) ->
                         let uu____24681 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24681
                           (fun uu____24702  ->
                              match uu____24702 with
                              | (c2,g2) ->
                                  let uu____24713 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24713)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24835 = l1 u t e  in
                              l2 u t uu____24835))
                | uu____24836 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24904  ->
                    match uu____24904 with
                    | (e,uu____24912) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24935 =
            match uu____24935 with
            | (i,j) ->
                let uu____24946 = FStar_Ident.lid_equals i j  in
                if uu____24946
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____24953  ->
                       FStar_Pervasives_Native.Some uu____24953)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24982 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24992 = FStar_Ident.lid_equals i k  in
                        if uu____24992
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25006 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25006
                                  then []
                                  else
                                    (let uu____25013 =
                                       let uu____25022 =
                                         find_edge order1 (i, k)  in
                                       let uu____25025 =
                                         find_edge order1 (k, j)  in
                                       (uu____25022, uu____25025)  in
                                     match uu____25013 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25040 =
                                           compose_edges e1 e2  in
                                         [uu____25040]
                                     | uu____25041 -> [])))))
                 in
              FStar_List.append order1 uu____24982  in
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
                  let uu____25071 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25074 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____25074
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25071
                  then
                    let uu____25081 =
                      let uu____25087 =
                        let uu____25089 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25089
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25087)
                       in
                    let uu____25093 = get_range env1  in
                    FStar_Errors.raise_error uu____25081 uu____25093
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25171 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25171
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25223 =
                                             let uu____25232 =
                                               find_edge order2 (i, k)  in
                                             let uu____25235 =
                                               find_edge order2 (j, k)  in
                                             (uu____25232, uu____25235)  in
                                           match uu____25223 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25277,uu____25278)
                                                    ->
                                                    let uu____25285 =
                                                      let uu____25292 =
                                                        let uu____25294 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25294
                                                         in
                                                      let uu____25297 =
                                                        let uu____25299 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25299
                                                         in
                                                      (uu____25292,
                                                        uu____25297)
                                                       in
                                                    (match uu____25285 with
                                                     | (true ,true ) ->
                                                         let uu____25316 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25316
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
                                           | uu____25359 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25411 =
                                   let uu____25413 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25413
                                     FStar_Util.is_some
                                    in
                                 if uu____25411
                                 then
                                   let uu____25462 =
                                     let uu____25468 =
                                       let uu____25470 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25472 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25474 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25476 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25470 uu____25472 uu____25474
                                         uu____25476
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25468)
                                      in
                                   FStar_Errors.raise_error uu____25462
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1834_25515 = env1.effects  in
             {
               decls = (uu___1834_25515.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1834_25515.polymonadic_binds);
               polymonadic_subcomps = (uu___1834_25515.polymonadic_subcomps)
             }  in
           let uu___1837_25516 = env1  in
           {
             solver = (uu___1837_25516.solver);
             range = (uu___1837_25516.range);
             curmodule = (uu___1837_25516.curmodule);
             gamma = (uu___1837_25516.gamma);
             gamma_sig = (uu___1837_25516.gamma_sig);
             gamma_cache = (uu___1837_25516.gamma_cache);
             modules = (uu___1837_25516.modules);
             expected_typ = (uu___1837_25516.expected_typ);
             sigtab = (uu___1837_25516.sigtab);
             attrtab = (uu___1837_25516.attrtab);
             instantiate_imp = (uu___1837_25516.instantiate_imp);
             effects = effects1;
             generalize = (uu___1837_25516.generalize);
             letrecs = (uu___1837_25516.letrecs);
             top_level = (uu___1837_25516.top_level);
             check_uvars = (uu___1837_25516.check_uvars);
             use_eq = (uu___1837_25516.use_eq);
             use_eq_strict = (uu___1837_25516.use_eq_strict);
             is_iface = (uu___1837_25516.is_iface);
             admit = (uu___1837_25516.admit);
             lax = (uu___1837_25516.lax);
             lax_universes = (uu___1837_25516.lax_universes);
             phase1 = (uu___1837_25516.phase1);
             failhard = (uu___1837_25516.failhard);
             nosynth = (uu___1837_25516.nosynth);
             uvar_subtyping = (uu___1837_25516.uvar_subtyping);
             tc_term = (uu___1837_25516.tc_term);
             type_of = (uu___1837_25516.type_of);
             universe_of = (uu___1837_25516.universe_of);
             check_type_of = (uu___1837_25516.check_type_of);
             use_bv_sorts = (uu___1837_25516.use_bv_sorts);
             qtbl_name_and_index = (uu___1837_25516.qtbl_name_and_index);
             normalized_eff_names = (uu___1837_25516.normalized_eff_names);
             fv_delta_depths = (uu___1837_25516.fv_delta_depths);
             proof_ns = (uu___1837_25516.proof_ns);
             synth_hook = (uu___1837_25516.synth_hook);
             try_solve_implicits_hook =
               (uu___1837_25516.try_solve_implicits_hook);
             splice = (uu___1837_25516.splice);
             mpreprocess = (uu___1837_25516.mpreprocess);
             postprocess = (uu___1837_25516.postprocess);
             identifier_info = (uu___1837_25516.identifier_info);
             tc_hooks = (uu___1837_25516.tc_hooks);
             dsenv = (uu___1837_25516.dsenv);
             nbe = (uu___1837_25516.nbe);
             strict_args_tab = (uu___1837_25516.strict_args_tab);
             erasable_types_tab = (uu___1837_25516.erasable_types_tab)
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
              let uu____25564 = FStar_Ident.string_of_lid m  in
              let uu____25566 = FStar_Ident.string_of_lid n  in
              let uu____25568 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25564 uu____25566 uu____25568
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25577 =
              let uu____25579 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25579 FStar_Util.is_some  in
            if uu____25577
            then
              let uu____25616 =
                let uu____25622 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25622)
                 in
              FStar_Errors.raise_error uu____25616 env1.range
            else
              (let uu____25628 =
                 let uu____25630 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25630 FStar_Util.is_some  in
               if uu____25628
               then
                 let uu____25655 =
                   let uu____25661 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25661)
                    in
                 FStar_Errors.raise_error uu____25655 env1.range
               else
                 (let uu___1852_25667 = env1  in
                  {
                    solver = (uu___1852_25667.solver);
                    range = (uu___1852_25667.range);
                    curmodule = (uu___1852_25667.curmodule);
                    gamma = (uu___1852_25667.gamma);
                    gamma_sig = (uu___1852_25667.gamma_sig);
                    gamma_cache = (uu___1852_25667.gamma_cache);
                    modules = (uu___1852_25667.modules);
                    expected_typ = (uu___1852_25667.expected_typ);
                    sigtab = (uu___1852_25667.sigtab);
                    attrtab = (uu___1852_25667.attrtab);
                    instantiate_imp = (uu___1852_25667.instantiate_imp);
                    effects =
                      (let uu___1854_25669 = env1.effects  in
                       {
                         decls = (uu___1854_25669.decls);
                         order = (uu___1854_25669.order);
                         joins = (uu___1854_25669.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1854_25669.polymonadic_subcomps)
                       });
                    generalize = (uu___1852_25667.generalize);
                    letrecs = (uu___1852_25667.letrecs);
                    top_level = (uu___1852_25667.top_level);
                    check_uvars = (uu___1852_25667.check_uvars);
                    use_eq = (uu___1852_25667.use_eq);
                    use_eq_strict = (uu___1852_25667.use_eq_strict);
                    is_iface = (uu___1852_25667.is_iface);
                    admit = (uu___1852_25667.admit);
                    lax = (uu___1852_25667.lax);
                    lax_universes = (uu___1852_25667.lax_universes);
                    phase1 = (uu___1852_25667.phase1);
                    failhard = (uu___1852_25667.failhard);
                    nosynth = (uu___1852_25667.nosynth);
                    uvar_subtyping = (uu___1852_25667.uvar_subtyping);
                    tc_term = (uu___1852_25667.tc_term);
                    type_of = (uu___1852_25667.type_of);
                    universe_of = (uu___1852_25667.universe_of);
                    check_type_of = (uu___1852_25667.check_type_of);
                    use_bv_sorts = (uu___1852_25667.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1852_25667.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1852_25667.normalized_eff_names);
                    fv_delta_depths = (uu___1852_25667.fv_delta_depths);
                    proof_ns = (uu___1852_25667.proof_ns);
                    synth_hook = (uu___1852_25667.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1852_25667.try_solve_implicits_hook);
                    splice = (uu___1852_25667.splice);
                    mpreprocess = (uu___1852_25667.mpreprocess);
                    postprocess = (uu___1852_25667.postprocess);
                    identifier_info = (uu___1852_25667.identifier_info);
                    tc_hooks = (uu___1852_25667.tc_hooks);
                    dsenv = (uu___1852_25667.dsenv);
                    nbe = (uu___1852_25667.nbe);
                    strict_args_tab = (uu___1852_25667.strict_args_tab);
                    erasable_types_tab = (uu___1852_25667.erasable_types_tab)
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
            let uu____25760 = FStar_Ident.string_of_lid m  in
            let uu____25762 = FStar_Ident.string_of_lid n  in
            FStar_Util.format3
              "Polymonadic subcomp %s <: %s conflicts with an already existing %s"
              uu____25760 uu____25762
              (if poly
               then "polymonadic subcomp"
               else "path in the effect lattice")
             in
          let uu____25771 =
            let uu____25773 = exists_polymonadic_subcomp env1 m n  in
            FStar_All.pipe_right uu____25773 FStar_Util.is_some  in
          if uu____25771
          then
            let uu____25780 =
              let uu____25786 = err_msg true  in
              (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25786)  in
            FStar_Errors.raise_error uu____25780 env1.range
          else
            (let uu____25792 =
               let uu____25794 = join_opt env1 m n  in
               FStar_All.pipe_right uu____25794 FStar_Util.is_some  in
             if uu____25792
             then
               let uu____25819 =
                 let uu____25825 = err_msg false  in
                 (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25825)
                  in
               FStar_Errors.raise_error uu____25819 env1.range
             else
               (let uu___1867_25831 = env1  in
                {
                  solver = (uu___1867_25831.solver);
                  range = (uu___1867_25831.range);
                  curmodule = (uu___1867_25831.curmodule);
                  gamma = (uu___1867_25831.gamma);
                  gamma_sig = (uu___1867_25831.gamma_sig);
                  gamma_cache = (uu___1867_25831.gamma_cache);
                  modules = (uu___1867_25831.modules);
                  expected_typ = (uu___1867_25831.expected_typ);
                  sigtab = (uu___1867_25831.sigtab);
                  attrtab = (uu___1867_25831.attrtab);
                  instantiate_imp = (uu___1867_25831.instantiate_imp);
                  effects =
                    (let uu___1869_25833 = env1.effects  in
                     {
                       decls = (uu___1869_25833.decls);
                       order = (uu___1869_25833.order);
                       joins = (uu___1869_25833.joins);
                       polymonadic_binds =
                         (uu___1869_25833.polymonadic_binds);
                       polymonadic_subcomps = ((m, n, ts) ::
                         ((env1.effects).polymonadic_subcomps))
                     });
                  generalize = (uu___1867_25831.generalize);
                  letrecs = (uu___1867_25831.letrecs);
                  top_level = (uu___1867_25831.top_level);
                  check_uvars = (uu___1867_25831.check_uvars);
                  use_eq = (uu___1867_25831.use_eq);
                  use_eq_strict = (uu___1867_25831.use_eq_strict);
                  is_iface = (uu___1867_25831.is_iface);
                  admit = (uu___1867_25831.admit);
                  lax = (uu___1867_25831.lax);
                  lax_universes = (uu___1867_25831.lax_universes);
                  phase1 = (uu___1867_25831.phase1);
                  failhard = (uu___1867_25831.failhard);
                  nosynth = (uu___1867_25831.nosynth);
                  uvar_subtyping = (uu___1867_25831.uvar_subtyping);
                  tc_term = (uu___1867_25831.tc_term);
                  type_of = (uu___1867_25831.type_of);
                  universe_of = (uu___1867_25831.universe_of);
                  check_type_of = (uu___1867_25831.check_type_of);
                  use_bv_sorts = (uu___1867_25831.use_bv_sorts);
                  qtbl_name_and_index = (uu___1867_25831.qtbl_name_and_index);
                  normalized_eff_names =
                    (uu___1867_25831.normalized_eff_names);
                  fv_delta_depths = (uu___1867_25831.fv_delta_depths);
                  proof_ns = (uu___1867_25831.proof_ns);
                  synth_hook = (uu___1867_25831.synth_hook);
                  try_solve_implicits_hook =
                    (uu___1867_25831.try_solve_implicits_hook);
                  splice = (uu___1867_25831.splice);
                  mpreprocess = (uu___1867_25831.mpreprocess);
                  postprocess = (uu___1867_25831.postprocess);
                  identifier_info = (uu___1867_25831.identifier_info);
                  tc_hooks = (uu___1867_25831.tc_hooks);
                  dsenv = (uu___1867_25831.dsenv);
                  nbe = (uu___1867_25831.nbe);
                  strict_args_tab = (uu___1867_25831.strict_args_tab);
                  erasable_types_tab = (uu___1867_25831.erasable_types_tab)
                }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1873_25851 = env1  in
      {
        solver = (uu___1873_25851.solver);
        range = (uu___1873_25851.range);
        curmodule = (uu___1873_25851.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1873_25851.gamma_sig);
        gamma_cache = (uu___1873_25851.gamma_cache);
        modules = (uu___1873_25851.modules);
        expected_typ = (uu___1873_25851.expected_typ);
        sigtab = (uu___1873_25851.sigtab);
        attrtab = (uu___1873_25851.attrtab);
        instantiate_imp = (uu___1873_25851.instantiate_imp);
        effects = (uu___1873_25851.effects);
        generalize = (uu___1873_25851.generalize);
        letrecs = (uu___1873_25851.letrecs);
        top_level = (uu___1873_25851.top_level);
        check_uvars = (uu___1873_25851.check_uvars);
        use_eq = (uu___1873_25851.use_eq);
        use_eq_strict = (uu___1873_25851.use_eq_strict);
        is_iface = (uu___1873_25851.is_iface);
        admit = (uu___1873_25851.admit);
        lax = (uu___1873_25851.lax);
        lax_universes = (uu___1873_25851.lax_universes);
        phase1 = (uu___1873_25851.phase1);
        failhard = (uu___1873_25851.failhard);
        nosynth = (uu___1873_25851.nosynth);
        uvar_subtyping = (uu___1873_25851.uvar_subtyping);
        tc_term = (uu___1873_25851.tc_term);
        type_of = (uu___1873_25851.type_of);
        universe_of = (uu___1873_25851.universe_of);
        check_type_of = (uu___1873_25851.check_type_of);
        use_bv_sorts = (uu___1873_25851.use_bv_sorts);
        qtbl_name_and_index = (uu___1873_25851.qtbl_name_and_index);
        normalized_eff_names = (uu___1873_25851.normalized_eff_names);
        fv_delta_depths = (uu___1873_25851.fv_delta_depths);
        proof_ns = (uu___1873_25851.proof_ns);
        synth_hook = (uu___1873_25851.synth_hook);
        try_solve_implicits_hook = (uu___1873_25851.try_solve_implicits_hook);
        splice = (uu___1873_25851.splice);
        mpreprocess = (uu___1873_25851.mpreprocess);
        postprocess = (uu___1873_25851.postprocess);
        identifier_info = (uu___1873_25851.identifier_info);
        tc_hooks = (uu___1873_25851.tc_hooks);
        dsenv = (uu___1873_25851.dsenv);
        nbe = (uu___1873_25851.nbe);
        strict_args_tab = (uu___1873_25851.strict_args_tab);
        erasable_types_tab = (uu___1873_25851.erasable_types_tab)
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
            (let uu___1886_25909 = env1  in
             {
               solver = (uu___1886_25909.solver);
               range = (uu___1886_25909.range);
               curmodule = (uu___1886_25909.curmodule);
               gamma = rest;
               gamma_sig = (uu___1886_25909.gamma_sig);
               gamma_cache = (uu___1886_25909.gamma_cache);
               modules = (uu___1886_25909.modules);
               expected_typ = (uu___1886_25909.expected_typ);
               sigtab = (uu___1886_25909.sigtab);
               attrtab = (uu___1886_25909.attrtab);
               instantiate_imp = (uu___1886_25909.instantiate_imp);
               effects = (uu___1886_25909.effects);
               generalize = (uu___1886_25909.generalize);
               letrecs = (uu___1886_25909.letrecs);
               top_level = (uu___1886_25909.top_level);
               check_uvars = (uu___1886_25909.check_uvars);
               use_eq = (uu___1886_25909.use_eq);
               use_eq_strict = (uu___1886_25909.use_eq_strict);
               is_iface = (uu___1886_25909.is_iface);
               admit = (uu___1886_25909.admit);
               lax = (uu___1886_25909.lax);
               lax_universes = (uu___1886_25909.lax_universes);
               phase1 = (uu___1886_25909.phase1);
               failhard = (uu___1886_25909.failhard);
               nosynth = (uu___1886_25909.nosynth);
               uvar_subtyping = (uu___1886_25909.uvar_subtyping);
               tc_term = (uu___1886_25909.tc_term);
               type_of = (uu___1886_25909.type_of);
               universe_of = (uu___1886_25909.universe_of);
               check_type_of = (uu___1886_25909.check_type_of);
               use_bv_sorts = (uu___1886_25909.use_bv_sorts);
               qtbl_name_and_index = (uu___1886_25909.qtbl_name_and_index);
               normalized_eff_names = (uu___1886_25909.normalized_eff_names);
               fv_delta_depths = (uu___1886_25909.fv_delta_depths);
               proof_ns = (uu___1886_25909.proof_ns);
               synth_hook = (uu___1886_25909.synth_hook);
               try_solve_implicits_hook =
                 (uu___1886_25909.try_solve_implicits_hook);
               splice = (uu___1886_25909.splice);
               mpreprocess = (uu___1886_25909.mpreprocess);
               postprocess = (uu___1886_25909.postprocess);
               identifier_info = (uu___1886_25909.identifier_info);
               tc_hooks = (uu___1886_25909.tc_hooks);
               dsenv = (uu___1886_25909.dsenv);
               nbe = (uu___1886_25909.nbe);
               strict_args_tab = (uu___1886_25909.strict_args_tab);
               erasable_types_tab = (uu___1886_25909.erasable_types_tab)
             }))
    | uu____25910 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25939  ->
             match uu____25939 with | (x,uu____25947) -> push_bv env2 x) env1
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
            let uu___1900_25982 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1900_25982.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1900_25982.FStar_Syntax_Syntax.index);
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
        let uu____26055 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26055 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____26083 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26083)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1921_26099 = env1  in
      {
        solver = (uu___1921_26099.solver);
        range = (uu___1921_26099.range);
        curmodule = (uu___1921_26099.curmodule);
        gamma = (uu___1921_26099.gamma);
        gamma_sig = (uu___1921_26099.gamma_sig);
        gamma_cache = (uu___1921_26099.gamma_cache);
        modules = (uu___1921_26099.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1921_26099.sigtab);
        attrtab = (uu___1921_26099.attrtab);
        instantiate_imp = (uu___1921_26099.instantiate_imp);
        effects = (uu___1921_26099.effects);
        generalize = (uu___1921_26099.generalize);
        letrecs = (uu___1921_26099.letrecs);
        top_level = (uu___1921_26099.top_level);
        check_uvars = (uu___1921_26099.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1921_26099.use_eq_strict);
        is_iface = (uu___1921_26099.is_iface);
        admit = (uu___1921_26099.admit);
        lax = (uu___1921_26099.lax);
        lax_universes = (uu___1921_26099.lax_universes);
        phase1 = (uu___1921_26099.phase1);
        failhard = (uu___1921_26099.failhard);
        nosynth = (uu___1921_26099.nosynth);
        uvar_subtyping = (uu___1921_26099.uvar_subtyping);
        tc_term = (uu___1921_26099.tc_term);
        type_of = (uu___1921_26099.type_of);
        universe_of = (uu___1921_26099.universe_of);
        check_type_of = (uu___1921_26099.check_type_of);
        use_bv_sorts = (uu___1921_26099.use_bv_sorts);
        qtbl_name_and_index = (uu___1921_26099.qtbl_name_and_index);
        normalized_eff_names = (uu___1921_26099.normalized_eff_names);
        fv_delta_depths = (uu___1921_26099.fv_delta_depths);
        proof_ns = (uu___1921_26099.proof_ns);
        synth_hook = (uu___1921_26099.synth_hook);
        try_solve_implicits_hook = (uu___1921_26099.try_solve_implicits_hook);
        splice = (uu___1921_26099.splice);
        mpreprocess = (uu___1921_26099.mpreprocess);
        postprocess = (uu___1921_26099.postprocess);
        identifier_info = (uu___1921_26099.identifier_info);
        tc_hooks = (uu___1921_26099.tc_hooks);
        dsenv = (uu___1921_26099.dsenv);
        nbe = (uu___1921_26099.nbe);
        strict_args_tab = (uu___1921_26099.strict_args_tab);
        erasable_types_tab = (uu___1921_26099.erasable_types_tab)
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
    let uu____26130 = expected_typ env_  in
    ((let uu___1928_26136 = env_  in
      {
        solver = (uu___1928_26136.solver);
        range = (uu___1928_26136.range);
        curmodule = (uu___1928_26136.curmodule);
        gamma = (uu___1928_26136.gamma);
        gamma_sig = (uu___1928_26136.gamma_sig);
        gamma_cache = (uu___1928_26136.gamma_cache);
        modules = (uu___1928_26136.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1928_26136.sigtab);
        attrtab = (uu___1928_26136.attrtab);
        instantiate_imp = (uu___1928_26136.instantiate_imp);
        effects = (uu___1928_26136.effects);
        generalize = (uu___1928_26136.generalize);
        letrecs = (uu___1928_26136.letrecs);
        top_level = (uu___1928_26136.top_level);
        check_uvars = (uu___1928_26136.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1928_26136.use_eq_strict);
        is_iface = (uu___1928_26136.is_iface);
        admit = (uu___1928_26136.admit);
        lax = (uu___1928_26136.lax);
        lax_universes = (uu___1928_26136.lax_universes);
        phase1 = (uu___1928_26136.phase1);
        failhard = (uu___1928_26136.failhard);
        nosynth = (uu___1928_26136.nosynth);
        uvar_subtyping = (uu___1928_26136.uvar_subtyping);
        tc_term = (uu___1928_26136.tc_term);
        type_of = (uu___1928_26136.type_of);
        universe_of = (uu___1928_26136.universe_of);
        check_type_of = (uu___1928_26136.check_type_of);
        use_bv_sorts = (uu___1928_26136.use_bv_sorts);
        qtbl_name_and_index = (uu___1928_26136.qtbl_name_and_index);
        normalized_eff_names = (uu___1928_26136.normalized_eff_names);
        fv_delta_depths = (uu___1928_26136.fv_delta_depths);
        proof_ns = (uu___1928_26136.proof_ns);
        synth_hook = (uu___1928_26136.synth_hook);
        try_solve_implicits_hook = (uu___1928_26136.try_solve_implicits_hook);
        splice = (uu___1928_26136.splice);
        mpreprocess = (uu___1928_26136.mpreprocess);
        postprocess = (uu___1928_26136.postprocess);
        identifier_info = (uu___1928_26136.identifier_info);
        tc_hooks = (uu___1928_26136.tc_hooks);
        dsenv = (uu___1928_26136.dsenv);
        nbe = (uu___1928_26136.nbe);
        strict_args_tab = (uu___1928_26136.strict_args_tab);
        erasable_types_tab = (uu___1928_26136.erasable_types_tab)
      }), uu____26130)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26148 =
      let uu____26149 = FStar_Ident.id_of_text ""  in [uu____26149]  in
    FStar_Ident.lid_of_ids uu____26148  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____26156 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26156
        then
          let uu____26161 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26161 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1936_26189 = env1  in
       {
         solver = (uu___1936_26189.solver);
         range = (uu___1936_26189.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1936_26189.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1936_26189.expected_typ);
         sigtab = (uu___1936_26189.sigtab);
         attrtab = (uu___1936_26189.attrtab);
         instantiate_imp = (uu___1936_26189.instantiate_imp);
         effects = (uu___1936_26189.effects);
         generalize = (uu___1936_26189.generalize);
         letrecs = (uu___1936_26189.letrecs);
         top_level = (uu___1936_26189.top_level);
         check_uvars = (uu___1936_26189.check_uvars);
         use_eq = (uu___1936_26189.use_eq);
         use_eq_strict = (uu___1936_26189.use_eq_strict);
         is_iface = (uu___1936_26189.is_iface);
         admit = (uu___1936_26189.admit);
         lax = (uu___1936_26189.lax);
         lax_universes = (uu___1936_26189.lax_universes);
         phase1 = (uu___1936_26189.phase1);
         failhard = (uu___1936_26189.failhard);
         nosynth = (uu___1936_26189.nosynth);
         uvar_subtyping = (uu___1936_26189.uvar_subtyping);
         tc_term = (uu___1936_26189.tc_term);
         type_of = (uu___1936_26189.type_of);
         universe_of = (uu___1936_26189.universe_of);
         check_type_of = (uu___1936_26189.check_type_of);
         use_bv_sorts = (uu___1936_26189.use_bv_sorts);
         qtbl_name_and_index = (uu___1936_26189.qtbl_name_and_index);
         normalized_eff_names = (uu___1936_26189.normalized_eff_names);
         fv_delta_depths = (uu___1936_26189.fv_delta_depths);
         proof_ns = (uu___1936_26189.proof_ns);
         synth_hook = (uu___1936_26189.synth_hook);
         try_solve_implicits_hook =
           (uu___1936_26189.try_solve_implicits_hook);
         splice = (uu___1936_26189.splice);
         mpreprocess = (uu___1936_26189.mpreprocess);
         postprocess = (uu___1936_26189.postprocess);
         identifier_info = (uu___1936_26189.identifier_info);
         tc_hooks = (uu___1936_26189.tc_hooks);
         dsenv = (uu___1936_26189.dsenv);
         nbe = (uu___1936_26189.nbe);
         strict_args_tab = (uu___1936_26189.strict_args_tab);
         erasable_types_tab = (uu___1936_26189.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26241)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26245,(uu____26246,t)))::tl
          ->
          let uu____26267 =
            let uu____26270 = FStar_Syntax_Free.uvars t  in
            ext out uu____26270  in
          aux uu____26267 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26273;
            FStar_Syntax_Syntax.index = uu____26274;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26282 =
            let uu____26285 = FStar_Syntax_Free.uvars t  in
            ext out uu____26285  in
          aux uu____26282 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26343)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26347,(uu____26348,t)))::tl
          ->
          let uu____26369 =
            let uu____26372 = FStar_Syntax_Free.univs t  in
            ext out uu____26372  in
          aux uu____26369 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26375;
            FStar_Syntax_Syntax.index = uu____26376;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26384 =
            let uu____26387 = FStar_Syntax_Free.univs t  in
            ext out uu____26387  in
          aux uu____26384 tl
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
          let uu____26449 = FStar_Util.set_add uname out  in
          aux uu____26449 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26452,(uu____26453,t)))::tl
          ->
          let uu____26474 =
            let uu____26477 = FStar_Syntax_Free.univnames t  in
            ext out uu____26477  in
          aux uu____26474 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26480;
            FStar_Syntax_Syntax.index = uu____26481;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26489 =
            let uu____26492 = FStar_Syntax_Free.univnames t  in
            ext out uu____26492  in
          aux uu____26489 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26513  ->
            match uu___12_26513 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26517 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26530 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26541 =
      let uu____26550 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26550
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26541 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26598 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26611  ->
              match uu___13_26611 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26614 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26614
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26618 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26618
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26622) ->
                  let uu____26639 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26639))
       in
    FStar_All.pipe_right uu____26598 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26653  ->
    match uu___14_26653 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26659 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26659
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26682  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26737) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26770,uu____26771) -> false  in
      let uu____26785 =
        FStar_List.tryFind
          (fun uu____26807  ->
             match uu____26807 with | (p,uu____26818) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26785 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26837,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26867 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26867
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2079_26889 = e  in
        {
          solver = (uu___2079_26889.solver);
          range = (uu___2079_26889.range);
          curmodule = (uu___2079_26889.curmodule);
          gamma = (uu___2079_26889.gamma);
          gamma_sig = (uu___2079_26889.gamma_sig);
          gamma_cache = (uu___2079_26889.gamma_cache);
          modules = (uu___2079_26889.modules);
          expected_typ = (uu___2079_26889.expected_typ);
          sigtab = (uu___2079_26889.sigtab);
          attrtab = (uu___2079_26889.attrtab);
          instantiate_imp = (uu___2079_26889.instantiate_imp);
          effects = (uu___2079_26889.effects);
          generalize = (uu___2079_26889.generalize);
          letrecs = (uu___2079_26889.letrecs);
          top_level = (uu___2079_26889.top_level);
          check_uvars = (uu___2079_26889.check_uvars);
          use_eq = (uu___2079_26889.use_eq);
          use_eq_strict = (uu___2079_26889.use_eq_strict);
          is_iface = (uu___2079_26889.is_iface);
          admit = (uu___2079_26889.admit);
          lax = (uu___2079_26889.lax);
          lax_universes = (uu___2079_26889.lax_universes);
          phase1 = (uu___2079_26889.phase1);
          failhard = (uu___2079_26889.failhard);
          nosynth = (uu___2079_26889.nosynth);
          uvar_subtyping = (uu___2079_26889.uvar_subtyping);
          tc_term = (uu___2079_26889.tc_term);
          type_of = (uu___2079_26889.type_of);
          universe_of = (uu___2079_26889.universe_of);
          check_type_of = (uu___2079_26889.check_type_of);
          use_bv_sorts = (uu___2079_26889.use_bv_sorts);
          qtbl_name_and_index = (uu___2079_26889.qtbl_name_and_index);
          normalized_eff_names = (uu___2079_26889.normalized_eff_names);
          fv_delta_depths = (uu___2079_26889.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2079_26889.synth_hook);
          try_solve_implicits_hook =
            (uu___2079_26889.try_solve_implicits_hook);
          splice = (uu___2079_26889.splice);
          mpreprocess = (uu___2079_26889.mpreprocess);
          postprocess = (uu___2079_26889.postprocess);
          identifier_info = (uu___2079_26889.identifier_info);
          tc_hooks = (uu___2079_26889.tc_hooks);
          dsenv = (uu___2079_26889.dsenv);
          nbe = (uu___2079_26889.nbe);
          strict_args_tab = (uu___2079_26889.strict_args_tab);
          erasable_types_tab = (uu___2079_26889.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2088_26937 = e  in
      {
        solver = (uu___2088_26937.solver);
        range = (uu___2088_26937.range);
        curmodule = (uu___2088_26937.curmodule);
        gamma = (uu___2088_26937.gamma);
        gamma_sig = (uu___2088_26937.gamma_sig);
        gamma_cache = (uu___2088_26937.gamma_cache);
        modules = (uu___2088_26937.modules);
        expected_typ = (uu___2088_26937.expected_typ);
        sigtab = (uu___2088_26937.sigtab);
        attrtab = (uu___2088_26937.attrtab);
        instantiate_imp = (uu___2088_26937.instantiate_imp);
        effects = (uu___2088_26937.effects);
        generalize = (uu___2088_26937.generalize);
        letrecs = (uu___2088_26937.letrecs);
        top_level = (uu___2088_26937.top_level);
        check_uvars = (uu___2088_26937.check_uvars);
        use_eq = (uu___2088_26937.use_eq);
        use_eq_strict = (uu___2088_26937.use_eq_strict);
        is_iface = (uu___2088_26937.is_iface);
        admit = (uu___2088_26937.admit);
        lax = (uu___2088_26937.lax);
        lax_universes = (uu___2088_26937.lax_universes);
        phase1 = (uu___2088_26937.phase1);
        failhard = (uu___2088_26937.failhard);
        nosynth = (uu___2088_26937.nosynth);
        uvar_subtyping = (uu___2088_26937.uvar_subtyping);
        tc_term = (uu___2088_26937.tc_term);
        type_of = (uu___2088_26937.type_of);
        universe_of = (uu___2088_26937.universe_of);
        check_type_of = (uu___2088_26937.check_type_of);
        use_bv_sorts = (uu___2088_26937.use_bv_sorts);
        qtbl_name_and_index = (uu___2088_26937.qtbl_name_and_index);
        normalized_eff_names = (uu___2088_26937.normalized_eff_names);
        fv_delta_depths = (uu___2088_26937.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2088_26937.synth_hook);
        try_solve_implicits_hook = (uu___2088_26937.try_solve_implicits_hook);
        splice = (uu___2088_26937.splice);
        mpreprocess = (uu___2088_26937.mpreprocess);
        postprocess = (uu___2088_26937.postprocess);
        identifier_info = (uu___2088_26937.identifier_info);
        tc_hooks = (uu___2088_26937.tc_hooks);
        dsenv = (uu___2088_26937.dsenv);
        nbe = (uu___2088_26937.nbe);
        strict_args_tab = (uu___2088_26937.strict_args_tab);
        erasable_types_tab = (uu___2088_26937.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26953 = FStar_Syntax_Free.names t  in
      let uu____26956 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26953 uu____26956
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26979 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26979
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26989 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26989
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____27010 =
      match uu____27010 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____27030 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____27030)
       in
    let uu____27038 =
      let uu____27042 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____27042 FStar_List.rev  in
    FStar_All.pipe_right uu____27038 (FStar_String.concat " ")
  
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
                  (let uu____27110 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27110 with
                   | FStar_Pervasives_Native.Some uu____27114 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27117 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27127;
        FStar_TypeChecker_Common.univ_ineqs = uu____27128;
        FStar_TypeChecker_Common.implicits = uu____27129;_} -> true
    | uu____27139 -> false
  
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
          let uu___2132_27161 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2132_27161.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2132_27161.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2132_27161.FStar_TypeChecker_Common.implicits)
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
          let uu____27200 = FStar_Options.defensive ()  in
          if uu____27200
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27206 =
              let uu____27208 =
                let uu____27210 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27210  in
              Prims.op_Negation uu____27208  in
            (if uu____27206
             then
               let uu____27217 =
                 let uu____27223 =
                   let uu____27225 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27227 =
                     let uu____27229 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27229
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27225 uu____27227
                    in
                 (FStar_Errors.Warning_Defensive, uu____27223)  in
               FStar_Errors.log_issue rng uu____27217
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
          let uu____27269 =
            let uu____27271 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27271  in
          if uu____27269
          then ()
          else
            (let uu____27276 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27276 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27302 =
            let uu____27304 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27304  in
          if uu____27302
          then ()
          else
            (let uu____27309 = bound_vars e  in
             def_check_closed_in rng msg uu____27309 t)
  
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
          let uu___2169_27348 = g  in
          let uu____27349 =
            let uu____27350 =
              let uu____27351 =
                let uu____27358 =
                  let uu____27359 =
                    let uu____27376 =
                      let uu____27387 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27387]  in
                    (f, uu____27376)  in
                  FStar_Syntax_Syntax.Tm_app uu____27359  in
                FStar_Syntax_Syntax.mk uu____27358  in
              uu____27351 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27424  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27424) uu____27350
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27349;
            FStar_TypeChecker_Common.deferred =
              (uu___2169_27348.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2169_27348.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2169_27348.FStar_TypeChecker_Common.implicits)
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
          let uu___2176_27442 = g  in
          let uu____27443 =
            let uu____27444 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27444  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27443;
            FStar_TypeChecker_Common.deferred =
              (uu___2176_27442.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2176_27442.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2176_27442.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2181_27461 = g  in
          let uu____27462 =
            let uu____27463 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27463  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27462;
            FStar_TypeChecker_Common.deferred =
              (uu___2181_27461.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2181_27461.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2181_27461.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2185_27465 = g  in
          let uu____27466 =
            let uu____27467 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27467  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27466;
            FStar_TypeChecker_Common.deferred =
              (uu___2185_27465.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2185_27465.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2185_27465.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27474 ->
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
                       let uu____27551 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27551
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2208_27558 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2208_27558.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2208_27558.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2208_27558.FStar_TypeChecker_Common.implicits)
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
               let uu____27592 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27592
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
            let uu___2223_27619 = g  in
            let uu____27620 =
              let uu____27621 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27621  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27620;
              FStar_TypeChecker_Common.deferred =
                (uu___2223_27619.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2223_27619.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2223_27619.FStar_TypeChecker_Common.implicits)
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
              let uu____27679 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27679 with
              | FStar_Pervasives_Native.Some
                  (uu____27704::(tm,uu____27706)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27770 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27788 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27788;
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
                    (let uu____27822 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27822
                     then
                       let uu____27826 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27826
                     else ());
                    (let g =
                       let uu___2247_27832 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2247_27832.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2247_27832.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2247_27832.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27886 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27943  ->
                      fun b  ->
                        match uu____27943 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27985 =
                              let uu____27998 = reason b  in
                              new_implicit_var_aux uu____27998 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27985 with
                             | (t,uu____28015,g_t) ->
                                 let uu____28029 =
                                   let uu____28032 =
                                     let uu____28035 =
                                       let uu____28036 =
                                         let uu____28043 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28043, t)  in
                                       FStar_Syntax_Syntax.NT uu____28036  in
                                     [uu____28035]  in
                                   FStar_List.append substs1 uu____28032  in
                                 let uu____28054 = conj_guard g g_t  in
                                 (uu____28029, (FStar_List.append uvars [t]),
                                   uu____28054))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27886
              (fun uu____28083  ->
                 match uu____28083 with | (uu____28100,uvars,g) -> (uvars, g))
  
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
                let uu____28141 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28141 FStar_Util.must  in
              let uu____28158 = inst_tscheme_with post_ts [u]  in
              match uu____28158 with
              | (uu____28163,post) ->
                  let uu____28165 =
                    let uu____28170 =
                      let uu____28171 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28171]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28170  in
                  uu____28165 FStar_Pervasives_Native.None r
               in
            let uu____28204 =
              let uu____28209 =
                let uu____28210 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28210]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28209  in
            uu____28204 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28246  -> ());
    push = (fun uu____28248  -> ());
    pop = (fun uu____28251  -> ());
    snapshot =
      (fun uu____28254  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28273  -> fun uu____28274  -> ());
    encode_sig = (fun uu____28289  -> fun uu____28290  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28296 =
             let uu____28303 = FStar_Options.peek ()  in (e, g, uu____28303)
              in
           [uu____28296]);
    solve = (fun uu____28319  -> fun uu____28320  -> fun uu____28321  -> ());
    finish = (fun uu____28328  -> ());
    refresh = (fun uu____28330  -> ())
  } 