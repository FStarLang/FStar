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
    let uu____16541 = FStar_Syntax_Unionfind.univ_fresh ()  in
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
      | ((formals,t),uu____16641) ->
          let vs = mk_univ_subst formals us  in
          let uu____16665 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16665)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16682  ->
    match uu___1_16682 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16708  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16728 = inst_tscheme t  in
      match uu____16728 with
      | (us,t1) ->
          let uu____16739 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16739)
  
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
          let uu____16764 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16766 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16764 uu____16766
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
        fun uu____16793  ->
          match uu____16793 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16807 =
                    let uu____16809 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16813 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16817 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16819 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16809 uu____16813 uu____16817 uu____16819
                     in
                  failwith uu____16807)
               else ();
               (let uu____16824 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16824))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16842 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16853 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16864 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____16878 =
        let uu____16880 = FStar_Ident.nsstr l  in
        let uu____16882 = FStar_Ident.string_of_lid cur  in
        uu____16880 = uu____16882  in
      if uu____16878
      then Yes
      else
        (let uu____16888 =
           let uu____16890 = FStar_Ident.nsstr l  in
           let uu____16892 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____16890 uu____16892  in
         if uu____16888
         then
           let lns =
             let uu____16898 = FStar_Ident.ns_of_lid l  in
             let uu____16901 =
               let uu____16904 = FStar_Ident.ident_of_lid l  in [uu____16904]
                in
             FStar_List.append uu____16898 uu____16901  in
           let cur1 =
             let uu____16908 = FStar_Ident.ns_of_lid cur  in
             let uu____16911 =
               let uu____16914 = FStar_Ident.ident_of_lid cur  in
               [uu____16914]  in
             FStar_List.append uu____16908 uu____16911  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____16938) -> Maybe
             | (uu____16945,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____16964 = FStar_Ident.text_of_id hd  in
                 let uu____16966 = FStar_Ident.text_of_id hd'  in
                 uu____16964 = uu____16966 -> aux tl tl'
             | uu____16969 -> No  in
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
        (let uu____17021 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17021 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17065 =
            let uu____17068 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17068  in
          match uu____17065 with
          | FStar_Pervasives_Native.None  ->
              let uu____17090 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17134  ->
                     match uu___2_17134 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17173 = FStar_Ident.lid_equals lid l  in
                         if uu____17173
                         then
                           let uu____17196 =
                             let uu____17215 =
                               let uu____17230 = inst_tscheme t  in
                               FStar_Util.Inl uu____17230  in
                             let uu____17245 = FStar_Ident.range_of_lid l  in
                             (uu____17215, uu____17245)  in
                           FStar_Pervasives_Native.Some uu____17196
                         else FStar_Pervasives_Native.None
                     | uu____17298 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17090
                (fun uu____17336  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17346  ->
                        match uu___3_17346 with
                        | (uu____17349,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17351);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17352;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17353;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17354;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17355;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17356;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17378 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17378
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
                                  uu____17430 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17437 -> cache t  in
                            let uu____17438 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17438 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17444 =
                                   let uu____17445 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17445)
                                    in
                                 maybe_cache uu____17444)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17516 = find_in_sigtab env1 lid  in
         match uu____17516 with
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
      let uu____17597 = lookup_qname env1 lid  in
      match uu____17597 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17618,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17732 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17732 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17777 =
          let uu____17780 = lookup_attr env2 attr  in se1 :: uu____17780  in
        FStar_Util.smap_add (attrtab env2) attr uu____17777  in
      FStar_List.iter
        (fun attr  ->
           let uu____17790 =
             let uu____17791 = FStar_Syntax_Subst.compress attr  in
             uu____17791.FStar_Syntax_Syntax.n  in
           match uu____17790 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17795 =
                 let uu____17797 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17797  in
               add_one env1 se uu____17795
           | uu____17798 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17821) ->
          add_sigelts env1 ses
      | uu____17830 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17838 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17838 se) lids;
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
        (fun uu___4_17872  ->
           match uu___4_17872 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____17882 =
                 let uu____17889 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____17889)  in
               FStar_Pervasives_Native.Some uu____17882
           | uu____17898 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17960,lb::[]),uu____17962) ->
            let uu____17971 =
              let uu____17980 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17989 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17980, uu____17989)  in
            FStar_Pervasives_Native.Some uu____17971
        | FStar_Syntax_Syntax.Sig_let ((uu____18002,lbs),uu____18004) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18036 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18049 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18049
                     then
                       let uu____18062 =
                         let uu____18071 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18080 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18071, uu____18080)  in
                       FStar_Pervasives_Native.Some uu____18062
                     else FStar_Pervasives_Native.None)
        | uu____18103 -> FStar_Pervasives_Native.None
  
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
                    let uu____18195 =
                      let uu____18197 =
                        let uu____18199 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18201 =
                          let uu____18203 =
                            let uu____18205 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18211 =
                              let uu____18213 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18213  in
                            Prims.op_Hat uu____18205 uu____18211  in
                          Prims.op_Hat ", expected " uu____18203  in
                        Prims.op_Hat uu____18199 uu____18201  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18197
                       in
                    failwith uu____18195
                  else ());
             (let uu____18220 =
                let uu____18229 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18229, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18220))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18249,uu____18250) ->
            let uu____18255 =
              let uu____18264 =
                let uu____18269 =
                  let uu____18270 =
                    let uu____18273 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18273  in
                  (us, uu____18270)  in
                inst_ts us_opt uu____18269  in
              (uu____18264, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18255
        | uu____18292 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18381 =
          match uu____18381 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18477,uvs,t,uu____18480,uu____18481,uu____18482);
                      FStar_Syntax_Syntax.sigrng = uu____18483;
                      FStar_Syntax_Syntax.sigquals = uu____18484;
                      FStar_Syntax_Syntax.sigmeta = uu____18485;
                      FStar_Syntax_Syntax.sigattrs = uu____18486;
                      FStar_Syntax_Syntax.sigopts = uu____18487;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18512 =
                     let uu____18521 = inst_tscheme1 (uvs, t)  in
                     (uu____18521, rng)  in
                   FStar_Pervasives_Native.Some uu____18512
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18545;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18547;
                      FStar_Syntax_Syntax.sigattrs = uu____18548;
                      FStar_Syntax_Syntax.sigopts = uu____18549;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18568 =
                     let uu____18570 = in_cur_mod env1 l  in
                     uu____18570 = Yes  in
                   if uu____18568
                   then
                     let uu____18582 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18582
                      then
                        let uu____18598 =
                          let uu____18607 = inst_tscheme1 (uvs, t)  in
                          (uu____18607, rng)  in
                        FStar_Pervasives_Native.Some uu____18598
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18640 =
                        let uu____18649 = inst_tscheme1 (uvs, t)  in
                        (uu____18649, rng)  in
                      FStar_Pervasives_Native.Some uu____18640)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18674,uu____18675);
                      FStar_Syntax_Syntax.sigrng = uu____18676;
                      FStar_Syntax_Syntax.sigquals = uu____18677;
                      FStar_Syntax_Syntax.sigmeta = uu____18678;
                      FStar_Syntax_Syntax.sigattrs = uu____18679;
                      FStar_Syntax_Syntax.sigopts = uu____18680;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18723 =
                          let uu____18732 = inst_tscheme1 (uvs, k)  in
                          (uu____18732, rng)  in
                        FStar_Pervasives_Native.Some uu____18723
                    | uu____18753 ->
                        let uu____18754 =
                          let uu____18763 =
                            let uu____18768 =
                              let uu____18769 =
                                let uu____18772 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18772
                                 in
                              (uvs, uu____18769)  in
                            inst_tscheme1 uu____18768  in
                          (uu____18763, rng)  in
                        FStar_Pervasives_Native.Some uu____18754)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18795,uu____18796);
                      FStar_Syntax_Syntax.sigrng = uu____18797;
                      FStar_Syntax_Syntax.sigquals = uu____18798;
                      FStar_Syntax_Syntax.sigmeta = uu____18799;
                      FStar_Syntax_Syntax.sigattrs = uu____18800;
                      FStar_Syntax_Syntax.sigopts = uu____18801;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18845 =
                          let uu____18854 = inst_tscheme_with (uvs, k) us  in
                          (uu____18854, rng)  in
                        FStar_Pervasives_Native.Some uu____18845
                    | uu____18875 ->
                        let uu____18876 =
                          let uu____18885 =
                            let uu____18890 =
                              let uu____18891 =
                                let uu____18894 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18894
                                 in
                              (uvs, uu____18891)  in
                            inst_tscheme_with uu____18890 us  in
                          (uu____18885, rng)  in
                        FStar_Pervasives_Native.Some uu____18876)
               | FStar_Util.Inr se ->
                   let uu____18930 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18951;
                          FStar_Syntax_Syntax.sigrng = uu____18952;
                          FStar_Syntax_Syntax.sigquals = uu____18953;
                          FStar_Syntax_Syntax.sigmeta = uu____18954;
                          FStar_Syntax_Syntax.sigattrs = uu____18955;
                          FStar_Syntax_Syntax.sigopts = uu____18956;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18973 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____18930
                     (FStar_Util.map_option
                        (fun uu____19021  ->
                           match uu____19021 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19052 =
          let uu____19063 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19063 mapper  in
        match uu____19052 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19137 =
              let uu____19148 =
                let uu____19155 =
                  let uu___857_19158 = t  in
                  let uu____19159 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___857_19158.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19159;
                    FStar_Syntax_Syntax.vars =
                      (uu___857_19158.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19155)  in
              (uu____19148, r)  in
            FStar_Pervasives_Native.Some uu____19137
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19208 = lookup_qname env1 l  in
      match uu____19208 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19229 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19283 = try_lookup_bv env1 bv  in
      match uu____19283 with
      | FStar_Pervasives_Native.None  ->
          let uu____19298 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19298 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19314 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19315 =
            let uu____19316 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19316  in
          (uu____19314, uu____19315)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19338 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19338 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19404 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19404  in
          let uu____19405 =
            let uu____19414 =
              let uu____19419 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19419)  in
            (uu____19414, r1)  in
          FStar_Pervasives_Native.Some uu____19405
  
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
        let uu____19454 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19454 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19487,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19512 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19512  in
            let uu____19513 =
              let uu____19518 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19518, r1)  in
            FStar_Pervasives_Native.Some uu____19513
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19542 = try_lookup_lid env1 l  in
      match uu____19542 with
      | FStar_Pervasives_Native.None  ->
          let uu____19569 = name_not_found l  in
          let uu____19575 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19569 uu____19575
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19620  ->
              match uu___5_19620 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19623 = FStar_Ident.text_of_id x  in
                  let uu____19625 = FStar_Ident.text_of_id y  in
                  uu____19623 = uu____19625
              | uu____19628 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19649 = lookup_qname env1 lid  in
      match uu____19649 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19658,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19661;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19663;
              FStar_Syntax_Syntax.sigattrs = uu____19664;
              FStar_Syntax_Syntax.sigopts = uu____19665;_},FStar_Pervasives_Native.None
            ),uu____19666)
          ->
          let uu____19717 =
            let uu____19724 =
              let uu____19725 =
                let uu____19728 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19728 t  in
              (uvs, uu____19725)  in
            (uu____19724, q)  in
          FStar_Pervasives_Native.Some uu____19717
      | uu____19741 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19763 = lookup_qname env1 lid  in
      match uu____19763 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19768,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19771;
              FStar_Syntax_Syntax.sigquals = uu____19772;
              FStar_Syntax_Syntax.sigmeta = uu____19773;
              FStar_Syntax_Syntax.sigattrs = uu____19774;
              FStar_Syntax_Syntax.sigopts = uu____19775;_},FStar_Pervasives_Native.None
            ),uu____19776)
          ->
          let uu____19827 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19827 (uvs, t)
      | uu____19832 ->
          let uu____19833 = name_not_found lid  in
          let uu____19839 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19833 uu____19839
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19859 = lookup_qname env1 lid  in
      match uu____19859 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19864,uvs,t,uu____19867,uu____19868,uu____19869);
              FStar_Syntax_Syntax.sigrng = uu____19870;
              FStar_Syntax_Syntax.sigquals = uu____19871;
              FStar_Syntax_Syntax.sigmeta = uu____19872;
              FStar_Syntax_Syntax.sigattrs = uu____19873;
              FStar_Syntax_Syntax.sigopts = uu____19874;_},FStar_Pervasives_Native.None
            ),uu____19875)
          ->
          let uu____19932 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19932 (uvs, t)
      | uu____19937 ->
          let uu____19938 = name_not_found lid  in
          let uu____19944 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19938 uu____19944
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____19967 = lookup_qname env1 lid  in
      match uu____19967 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19975,uu____19976,uu____19977,uu____19978,uu____19979,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19981;
              FStar_Syntax_Syntax.sigquals = uu____19982;
              FStar_Syntax_Syntax.sigmeta = uu____19983;
              FStar_Syntax_Syntax.sigattrs = uu____19984;
              FStar_Syntax_Syntax.sigopts = uu____19985;_},uu____19986),uu____19987)
          -> (true, dcs)
      | uu____20052 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20068 = lookup_qname env1 lid  in
      match uu____20068 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20069,uu____20070,uu____20071,l,uu____20073,uu____20074);
              FStar_Syntax_Syntax.sigrng = uu____20075;
              FStar_Syntax_Syntax.sigquals = uu____20076;
              FStar_Syntax_Syntax.sigmeta = uu____20077;
              FStar_Syntax_Syntax.sigattrs = uu____20078;
              FStar_Syntax_Syntax.sigopts = uu____20079;_},uu____20080),uu____20081)
          -> l
      | uu____20140 ->
          let uu____20141 =
            let uu____20143 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20143  in
          failwith uu____20141
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20213)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20270) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20294 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20294
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20329 -> FStar_Pervasives_Native.None)
          | uu____20338 -> FStar_Pervasives_Native.None
  
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
        let uu____20400 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20400
  
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
        let uu____20433 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20433
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20457 =
        let uu____20459 = FStar_Ident.nsstr lid  in uu____20459 = "Prims"  in
      if uu____20457
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20489,uu____20490) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20539),uu____20540) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20589 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20607 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20617 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20634 ->
                  let uu____20641 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20641
              | FStar_Syntax_Syntax.Sig_let ((uu____20642,lbs),uu____20644)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20660 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20660
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20667 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20683 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20693 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20694 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20701 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20702 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20703 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20716 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20717 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20740 =
        let uu____20742 = FStar_Ident.nsstr lid  in uu____20742 = "Prims"  in
      if uu____20740
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20749 =
           let uu____20752 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20752
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20749
           (fun d_opt  ->
              let uu____20764 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20764
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20774 =
                   let uu____20777 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20777  in
                 match uu____20774 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20778 =
                       let uu____20780 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20780
                        in
                     failwith uu____20778
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20785 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20785
                       then
                         let uu____20788 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20790 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20792 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20788 uu____20790 uu____20792
                       else ());
                      (let uu____20798 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20798 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20819),uu____20820) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20869 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20891),uu____20892) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20941 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20963 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20963
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20996 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____20996 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21018 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21027 =
                        let uu____21028 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21028.FStar_Syntax_Syntax.n  in
                      match uu____21027 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21033 -> false))
               in
            (true, uu____21018)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21056 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21056
  
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
          let uu____21128 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21128  in
        let uu____21129 = FStar_Util.smap_try_find tab s  in
        match uu____21129 with
        | FStar_Pervasives_Native.None  ->
            let uu____21132 = f ()  in
            (match uu____21132 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21170 =
        let uu____21171 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21171 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21205 =
        let uu____21206 = FStar_Syntax_Util.unrefine t  in
        uu____21206.FStar_Syntax_Syntax.n  in
      match uu____21205 with
      | FStar_Syntax_Syntax.Tm_type uu____21210 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21214) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21240) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21245,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21267 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21300 =
        let attrs =
          let uu____21306 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21306  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21346 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21346)
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
      let uu____21391 = lookup_qname env1 ftv  in
      match uu____21391 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21395) ->
          let uu____21440 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21440 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21461,t),r) ->
               let uu____21476 =
                 let uu____21477 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21477 t  in
               FStar_Pervasives_Native.Some uu____21476)
      | uu____21478 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21490 = try_lookup_effect_lid env1 ftv  in
      match uu____21490 with
      | FStar_Pervasives_Native.None  ->
          let uu____21493 = name_not_found ftv  in
          let uu____21499 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21493 uu____21499
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
        let uu____21523 = lookup_qname env1 lid0  in
        match uu____21523 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21534);
                FStar_Syntax_Syntax.sigrng = uu____21535;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21537;
                FStar_Syntax_Syntax.sigattrs = uu____21538;
                FStar_Syntax_Syntax.sigopts = uu____21539;_},FStar_Pervasives_Native.None
              ),uu____21540)
            ->
            let lid1 =
              let uu____21596 =
                let uu____21597 = FStar_Ident.range_of_lid lid  in
                let uu____21598 =
                  let uu____21599 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21599  in
                FStar_Range.set_use_range uu____21597 uu____21598  in
              FStar_Ident.set_lid_range lid uu____21596  in
            let uu____21600 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21606  ->
                      match uu___6_21606 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21609 -> false))
               in
            if uu____21600
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21628 =
                      let uu____21630 =
                        let uu____21632 = get_range env1  in
                        FStar_Range.string_of_range uu____21632  in
                      let uu____21633 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21635 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21630 uu____21633 uu____21635
                       in
                    failwith uu____21628)
                  in
               match (binders, univs) with
               | ([],uu____21656) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21682,uu____21683::uu____21684::uu____21685) ->
                   let uu____21706 =
                     let uu____21708 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21710 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21708 uu____21710
                      in
                   failwith uu____21706
               | uu____21721 ->
                   let uu____21736 =
                     let uu____21741 =
                       let uu____21742 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21742)  in
                     inst_tscheme_with uu____21741 insts  in
                   (match uu____21736 with
                    | (uu____21755,t) ->
                        let t1 =
                          let uu____21758 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21758 t  in
                        let uu____21759 =
                          let uu____21760 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21760.FStar_Syntax_Syntax.n  in
                        (match uu____21759 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21795 -> failwith "Impossible")))
        | uu____21803 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21827 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21827 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21840,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21847 = find l2  in
            (match uu____21847 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21854 =
          let uu____21857 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____21857  in
        match uu____21854 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21860 = find l  in
            (match uu____21860 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____21865 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____21865
                     m);
                  m))
         in
      let uu____21867 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21867
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21888 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____21888 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21894) ->
            FStar_List.length bs
        | uu____21933 ->
            let uu____21934 =
              let uu____21940 =
                let uu____21942 = FStar_Ident.string_of_lid name  in
                let uu____21944 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21942 uu____21944
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21940)
               in
            FStar_Errors.raise_error uu____21934 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____21963 = lookup_qname env1 l1  in
      match uu____21963 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21966;
              FStar_Syntax_Syntax.sigrng = uu____21967;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21969;
              FStar_Syntax_Syntax.sigattrs = uu____21970;
              FStar_Syntax_Syntax.sigopts = uu____21971;_},uu____21972),uu____21973)
          -> q
      | uu____22026 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22050 =
          let uu____22051 =
            let uu____22053 = FStar_Util.string_of_int i  in
            let uu____22055 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22053 uu____22055
             in
          failwith uu____22051  in
        let uu____22058 = lookup_datacon env1 lid  in
        match uu____22058 with
        | (uu____22063,t) ->
            let uu____22065 =
              let uu____22066 = FStar_Syntax_Subst.compress t  in
              uu____22066.FStar_Syntax_Syntax.n  in
            (match uu____22065 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22070) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22116 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22130 = lookup_qname env1 l  in
      match uu____22130 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22132,uu____22133,uu____22134);
              FStar_Syntax_Syntax.sigrng = uu____22135;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22137;
              FStar_Syntax_Syntax.sigattrs = uu____22138;
              FStar_Syntax_Syntax.sigopts = uu____22139;_},uu____22140),uu____22141)
          ->
          FStar_Util.for_some
            (fun uu___7_22196  ->
               match uu___7_22196 with
               | FStar_Syntax_Syntax.Projector uu____22198 -> true
               | uu____22204 -> false) quals
      | uu____22206 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22220 = lookup_qname env1 lid  in
      match uu____22220 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22222,uu____22223,uu____22224,uu____22225,uu____22226,uu____22227);
              FStar_Syntax_Syntax.sigrng = uu____22228;
              FStar_Syntax_Syntax.sigquals = uu____22229;
              FStar_Syntax_Syntax.sigmeta = uu____22230;
              FStar_Syntax_Syntax.sigattrs = uu____22231;
              FStar_Syntax_Syntax.sigopts = uu____22232;_},uu____22233),uu____22234)
          -> true
      | uu____22294 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22308 = lookup_qname env1 lid  in
      match uu____22308 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22310,uu____22311,uu____22312,uu____22313,uu____22314,uu____22315);
              FStar_Syntax_Syntax.sigrng = uu____22316;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22318;
              FStar_Syntax_Syntax.sigattrs = uu____22319;
              FStar_Syntax_Syntax.sigopts = uu____22320;_},uu____22321),uu____22322)
          ->
          FStar_Util.for_some
            (fun uu___8_22385  ->
               match uu___8_22385 with
               | FStar_Syntax_Syntax.RecordType uu____22387 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22397 -> true
               | uu____22407 -> false) quals
      | uu____22409 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22419,uu____22420);
            FStar_Syntax_Syntax.sigrng = uu____22421;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22423;
            FStar_Syntax_Syntax.sigattrs = uu____22424;
            FStar_Syntax_Syntax.sigopts = uu____22425;_},uu____22426),uu____22427)
        ->
        FStar_Util.for_some
          (fun uu___9_22486  ->
             match uu___9_22486 with
             | FStar_Syntax_Syntax.Action uu____22488 -> true
             | uu____22490 -> false) quals
    | uu____22492 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22506 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22506
  
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
      let uu____22523 =
        let uu____22524 = FStar_Syntax_Util.un_uinst head  in
        uu____22524.FStar_Syntax_Syntax.n  in
      match uu____22523 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22530 ->
               true
           | uu____22533 -> false)
      | uu____22535 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22549 = lookup_qname env1 l  in
      match uu____22549 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22552),uu____22553) ->
          FStar_Util.for_some
            (fun uu___10_22601  ->
               match uu___10_22601 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22604 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22606 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22682 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22700) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22718 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22726 ->
                 FStar_Pervasives_Native.Some true
             | uu____22745 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22748 =
        let uu____22752 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22752 mapper  in
      match uu____22748 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22812 = lookup_qname env1 lid  in
      match uu____22812 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22816,uu____22817,tps,uu____22819,uu____22820,uu____22821);
              FStar_Syntax_Syntax.sigrng = uu____22822;
              FStar_Syntax_Syntax.sigquals = uu____22823;
              FStar_Syntax_Syntax.sigmeta = uu____22824;
              FStar_Syntax_Syntax.sigattrs = uu____22825;
              FStar_Syntax_Syntax.sigopts = uu____22826;_},uu____22827),uu____22828)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22896 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22942  ->
              match uu____22942 with
              | (d,uu____22951) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____22967 = effect_decl_opt env1 l  in
      match uu____22967 with
      | FStar_Pervasives_Native.None  ->
          let uu____22982 = name_not_found l  in
          let uu____22988 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22982 uu____22988
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23016 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23016 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23023  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23037  ->
            fun uu____23038  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23072 = FStar_Ident.lid_equals l1 l2  in
        if uu____23072
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23091 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23091
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23110 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23163  ->
                        match uu____23163 with
                        | (m1,m2,uu____23177,uu____23178,uu____23179) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23110 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23204,uu____23205,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23253 = join_opt env1 l1 l2  in
        match uu____23253 with
        | FStar_Pervasives_Native.None  ->
            let uu____23274 =
              let uu____23280 =
                let uu____23282 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23284 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23282 uu____23284
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23280)  in
            FStar_Errors.raise_error uu____23274 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23327 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23327
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
  'uuuuuu23347 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23347) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23376 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23402  ->
                match uu____23402 with
                | (d,uu____23409) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23376 with
      | FStar_Pervasives_Native.None  ->
          let uu____23420 =
            let uu____23422 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23422
             in
          failwith uu____23420
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23437 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23437 with
           | (uu____23448,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23466)::(wp,uu____23468)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23524 -> failwith "Impossible"))
  
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
        | uu____23589 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23602 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23602 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23619 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23619 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23644 =
                     let uu____23650 =
                       let uu____23652 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23660 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23671 =
                         let uu____23673 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23673  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23652 uu____23660 uu____23671
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23650)
                      in
                   FStar_Errors.raise_error uu____23644
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23681 =
                     let uu____23692 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23692 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23729  ->
                        fun uu____23730  ->
                          match (uu____23729, uu____23730) with
                          | ((x,uu____23760),(t,uu____23762)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23681
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23793 =
                     let uu___1613_23794 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1613_23794.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1613_23794.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1613_23794.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1613_23794.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23793
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23806 .
    'uuuuuu23806 ->
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
            let uu____23847 =
              let uu____23854 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____23854)  in
            match uu____23847 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23878 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23880 = FStar_Util.string_of_int given  in
                     let uu____23882 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23878 uu____23880 uu____23882
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23887 = effect_decl_opt env1 effect_name  in
          match uu____23887 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23909) ->
              let uu____23920 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23920 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23938 =
                       let uu____23941 = get_range env1  in
                       let uu____23942 =
                         let uu____23949 =
                           let uu____23950 =
                             let uu____23967 =
                               let uu____23978 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23978 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23967)  in
                           FStar_Syntax_Syntax.Tm_app uu____23950  in
                         FStar_Syntax_Syntax.mk uu____23949  in
                       uu____23942 FStar_Pervasives_Native.None uu____23941
                        in
                     FStar_Pervasives_Native.Some uu____23938)))
  
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
           (fun uu___11_24078  ->
              match uu___11_24078 with
              | FStar_Syntax_Syntax.Reflectable uu____24080 -> true
              | uu____24082 -> false))
  
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
      | uu____24142 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24157 =
        let uu____24158 = FStar_Syntax_Subst.compress t  in
        uu____24158.FStar_Syntax_Syntax.n  in
      match uu____24157 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24162,c) ->
          is_reifiable_comp env1 c
      | uu____24184 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24204 =
           let uu____24206 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24206  in
         if uu____24204
         then
           let uu____24209 =
             let uu____24215 =
               let uu____24217 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24217
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24215)  in
           let uu____24221 = get_range env1  in
           FStar_Errors.raise_error uu____24209 uu____24221
         else ());
        (let uu____24224 = effect_repr_aux true env1 c u_c  in
         match uu____24224 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1690_24260 = env1  in
        {
          solver = (uu___1690_24260.solver);
          range = (uu___1690_24260.range);
          curmodule = (uu___1690_24260.curmodule);
          gamma = (uu___1690_24260.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1690_24260.gamma_cache);
          modules = (uu___1690_24260.modules);
          expected_typ = (uu___1690_24260.expected_typ);
          sigtab = (uu___1690_24260.sigtab);
          attrtab = (uu___1690_24260.attrtab);
          instantiate_imp = (uu___1690_24260.instantiate_imp);
          effects = (uu___1690_24260.effects);
          generalize = (uu___1690_24260.generalize);
          letrecs = (uu___1690_24260.letrecs);
          top_level = (uu___1690_24260.top_level);
          check_uvars = (uu___1690_24260.check_uvars);
          use_eq = (uu___1690_24260.use_eq);
          use_eq_strict = (uu___1690_24260.use_eq_strict);
          is_iface = (uu___1690_24260.is_iface);
          admit = (uu___1690_24260.admit);
          lax = (uu___1690_24260.lax);
          lax_universes = (uu___1690_24260.lax_universes);
          phase1 = (uu___1690_24260.phase1);
          failhard = (uu___1690_24260.failhard);
          nosynth = (uu___1690_24260.nosynth);
          uvar_subtyping = (uu___1690_24260.uvar_subtyping);
          tc_term = (uu___1690_24260.tc_term);
          type_of = (uu___1690_24260.type_of);
          universe_of = (uu___1690_24260.universe_of);
          check_type_of = (uu___1690_24260.check_type_of);
          use_bv_sorts = (uu___1690_24260.use_bv_sorts);
          qtbl_name_and_index = (uu___1690_24260.qtbl_name_and_index);
          normalized_eff_names = (uu___1690_24260.normalized_eff_names);
          fv_delta_depths = (uu___1690_24260.fv_delta_depths);
          proof_ns = (uu___1690_24260.proof_ns);
          synth_hook = (uu___1690_24260.synth_hook);
          try_solve_implicits_hook =
            (uu___1690_24260.try_solve_implicits_hook);
          splice = (uu___1690_24260.splice);
          mpreprocess = (uu___1690_24260.mpreprocess);
          postprocess = (uu___1690_24260.postprocess);
          identifier_info = (uu___1690_24260.identifier_info);
          tc_hooks = (uu___1690_24260.tc_hooks);
          dsenv = (uu___1690_24260.dsenv);
          nbe = (uu___1690_24260.nbe);
          strict_args_tab = (uu___1690_24260.strict_args_tab);
          erasable_types_tab = (uu___1690_24260.erasable_types_tab)
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
    fun uu____24279  ->
      match uu____24279 with
      | (ed,quals) ->
          let effects1 =
            let uu___1699_24293 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1699_24293.order);
              joins = (uu___1699_24293.joins);
              polymonadic_binds = (uu___1699_24293.polymonadic_binds);
              polymonadic_subcomps = (uu___1699_24293.polymonadic_subcomps)
            }  in
          let uu___1702_24302 = env1  in
          {
            solver = (uu___1702_24302.solver);
            range = (uu___1702_24302.range);
            curmodule = (uu___1702_24302.curmodule);
            gamma = (uu___1702_24302.gamma);
            gamma_sig = (uu___1702_24302.gamma_sig);
            gamma_cache = (uu___1702_24302.gamma_cache);
            modules = (uu___1702_24302.modules);
            expected_typ = (uu___1702_24302.expected_typ);
            sigtab = (uu___1702_24302.sigtab);
            attrtab = (uu___1702_24302.attrtab);
            instantiate_imp = (uu___1702_24302.instantiate_imp);
            effects = effects1;
            generalize = (uu___1702_24302.generalize);
            letrecs = (uu___1702_24302.letrecs);
            top_level = (uu___1702_24302.top_level);
            check_uvars = (uu___1702_24302.check_uvars);
            use_eq = (uu___1702_24302.use_eq);
            use_eq_strict = (uu___1702_24302.use_eq_strict);
            is_iface = (uu___1702_24302.is_iface);
            admit = (uu___1702_24302.admit);
            lax = (uu___1702_24302.lax);
            lax_universes = (uu___1702_24302.lax_universes);
            phase1 = (uu___1702_24302.phase1);
            failhard = (uu___1702_24302.failhard);
            nosynth = (uu___1702_24302.nosynth);
            uvar_subtyping = (uu___1702_24302.uvar_subtyping);
            tc_term = (uu___1702_24302.tc_term);
            type_of = (uu___1702_24302.type_of);
            universe_of = (uu___1702_24302.universe_of);
            check_type_of = (uu___1702_24302.check_type_of);
            use_bv_sorts = (uu___1702_24302.use_bv_sorts);
            qtbl_name_and_index = (uu___1702_24302.qtbl_name_and_index);
            normalized_eff_names = (uu___1702_24302.normalized_eff_names);
            fv_delta_depths = (uu___1702_24302.fv_delta_depths);
            proof_ns = (uu___1702_24302.proof_ns);
            synth_hook = (uu___1702_24302.synth_hook);
            try_solve_implicits_hook =
              (uu___1702_24302.try_solve_implicits_hook);
            splice = (uu___1702_24302.splice);
            mpreprocess = (uu___1702_24302.mpreprocess);
            postprocess = (uu___1702_24302.postprocess);
            identifier_info = (uu___1702_24302.identifier_info);
            tc_hooks = (uu___1702_24302.tc_hooks);
            dsenv = (uu___1702_24302.dsenv);
            nbe = (uu___1702_24302.nbe);
            strict_args_tab = (uu___1702_24302.strict_args_tab);
            erasable_types_tab = (uu___1702_24302.erasable_types_tab)
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
        let uu____24331 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24399  ->
                  match uu____24399 with
                  | (m1,n1,uu____24417,uu____24418) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24331 with
        | FStar_Pervasives_Native.Some (uu____24443,uu____24444,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24489 -> FStar_Pervasives_Native.None
  
let (exists_polymonadic_subcomp :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun m  ->
      fun n  ->
        let uu____24534 =
          FStar_All.pipe_right (env1.effects).polymonadic_subcomps
            (FStar_Util.find_opt
               (fun uu____24569  ->
                  match uu____24569 with
                  | (m1,n1,uu____24579) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24534 with
        | FStar_Pervasives_Native.Some (uu____24582,uu____24583,ts) ->
            FStar_Pervasives_Native.Some ts
        | uu____24591 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24648 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24648
                  (fun uu____24669  ->
                     match uu____24669 with
                     | (c1,g1) ->
                         let uu____24680 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24680
                           (fun uu____24701  ->
                              match uu____24701 with
                              | (c2,g2) ->
                                  let uu____24712 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24712)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24834 = l1 u t e  in
                              l2 u t uu____24834))
                | uu____24835 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24903  ->
                    match uu____24903 with
                    | (e,uu____24911) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24934 =
            match uu____24934 with
            | (i,j) ->
                let uu____24945 = FStar_Ident.lid_equals i j  in
                if uu____24945
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____24952  ->
                       FStar_Pervasives_Native.Some uu____24952)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24981 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24991 = FStar_Ident.lid_equals i k  in
                        if uu____24991
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25005 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25005
                                  then []
                                  else
                                    (let uu____25012 =
                                       let uu____25021 =
                                         find_edge order1 (i, k)  in
                                       let uu____25024 =
                                         find_edge order1 (k, j)  in
                                       (uu____25021, uu____25024)  in
                                     match uu____25012 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25039 =
                                           compose_edges e1 e2  in
                                         [uu____25039]
                                     | uu____25040 -> [])))))
                 in
              FStar_List.append order1 uu____24981  in
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
                  let uu____25070 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25073 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____25073
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25070
                  then
                    let uu____25080 =
                      let uu____25086 =
                        let uu____25088 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25088
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25086)
                       in
                    let uu____25092 = get_range env1  in
                    FStar_Errors.raise_error uu____25080 uu____25092
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25170 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25170
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25222 =
                                             let uu____25231 =
                                               find_edge order2 (i, k)  in
                                             let uu____25234 =
                                               find_edge order2 (j, k)  in
                                             (uu____25231, uu____25234)  in
                                           match uu____25222 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25276,uu____25277)
                                                    ->
                                                    let uu____25284 =
                                                      let uu____25291 =
                                                        let uu____25293 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25293
                                                         in
                                                      let uu____25296 =
                                                        let uu____25298 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25298
                                                         in
                                                      (uu____25291,
                                                        uu____25296)
                                                       in
                                                    (match uu____25284 with
                                                     | (true ,true ) ->
                                                         let uu____25315 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25315
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
                                           | uu____25358 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25410 =
                                   let uu____25412 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25412
                                     FStar_Util.is_some
                                    in
                                 if uu____25410
                                 then
                                   let uu____25461 =
                                     let uu____25467 =
                                       let uu____25469 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25471 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25473 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25475 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25469 uu____25471 uu____25473
                                         uu____25475
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25467)
                                      in
                                   FStar_Errors.raise_error uu____25461
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1836_25514 = env1.effects  in
             {
               decls = (uu___1836_25514.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1836_25514.polymonadic_binds);
               polymonadic_subcomps = (uu___1836_25514.polymonadic_subcomps)
             }  in
           let uu___1839_25515 = env1  in
           {
             solver = (uu___1839_25515.solver);
             range = (uu___1839_25515.range);
             curmodule = (uu___1839_25515.curmodule);
             gamma = (uu___1839_25515.gamma);
             gamma_sig = (uu___1839_25515.gamma_sig);
             gamma_cache = (uu___1839_25515.gamma_cache);
             modules = (uu___1839_25515.modules);
             expected_typ = (uu___1839_25515.expected_typ);
             sigtab = (uu___1839_25515.sigtab);
             attrtab = (uu___1839_25515.attrtab);
             instantiate_imp = (uu___1839_25515.instantiate_imp);
             effects = effects1;
             generalize = (uu___1839_25515.generalize);
             letrecs = (uu___1839_25515.letrecs);
             top_level = (uu___1839_25515.top_level);
             check_uvars = (uu___1839_25515.check_uvars);
             use_eq = (uu___1839_25515.use_eq);
             use_eq_strict = (uu___1839_25515.use_eq_strict);
             is_iface = (uu___1839_25515.is_iface);
             admit = (uu___1839_25515.admit);
             lax = (uu___1839_25515.lax);
             lax_universes = (uu___1839_25515.lax_universes);
             phase1 = (uu___1839_25515.phase1);
             failhard = (uu___1839_25515.failhard);
             nosynth = (uu___1839_25515.nosynth);
             uvar_subtyping = (uu___1839_25515.uvar_subtyping);
             tc_term = (uu___1839_25515.tc_term);
             type_of = (uu___1839_25515.type_of);
             universe_of = (uu___1839_25515.universe_of);
             check_type_of = (uu___1839_25515.check_type_of);
             use_bv_sorts = (uu___1839_25515.use_bv_sorts);
             qtbl_name_and_index = (uu___1839_25515.qtbl_name_and_index);
             normalized_eff_names = (uu___1839_25515.normalized_eff_names);
             fv_delta_depths = (uu___1839_25515.fv_delta_depths);
             proof_ns = (uu___1839_25515.proof_ns);
             synth_hook = (uu___1839_25515.synth_hook);
             try_solve_implicits_hook =
               (uu___1839_25515.try_solve_implicits_hook);
             splice = (uu___1839_25515.splice);
             mpreprocess = (uu___1839_25515.mpreprocess);
             postprocess = (uu___1839_25515.postprocess);
             identifier_info = (uu___1839_25515.identifier_info);
             tc_hooks = (uu___1839_25515.tc_hooks);
             dsenv = (uu___1839_25515.dsenv);
             nbe = (uu___1839_25515.nbe);
             strict_args_tab = (uu___1839_25515.strict_args_tab);
             erasable_types_tab = (uu___1839_25515.erasable_types_tab)
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
              let uu____25563 = FStar_Ident.string_of_lid m  in
              let uu____25565 = FStar_Ident.string_of_lid n  in
              let uu____25567 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25563 uu____25565 uu____25567
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25576 =
              let uu____25578 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25578 FStar_Util.is_some  in
            if uu____25576
            then
              let uu____25615 =
                let uu____25621 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25621)
                 in
              FStar_Errors.raise_error uu____25615 env1.range
            else
              (let uu____25627 =
                 let uu____25629 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25629 FStar_Util.is_some  in
               if uu____25627
               then
                 let uu____25654 =
                   let uu____25660 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25660)
                    in
                 FStar_Errors.raise_error uu____25654 env1.range
               else
                 (let uu___1854_25666 = env1  in
                  {
                    solver = (uu___1854_25666.solver);
                    range = (uu___1854_25666.range);
                    curmodule = (uu___1854_25666.curmodule);
                    gamma = (uu___1854_25666.gamma);
                    gamma_sig = (uu___1854_25666.gamma_sig);
                    gamma_cache = (uu___1854_25666.gamma_cache);
                    modules = (uu___1854_25666.modules);
                    expected_typ = (uu___1854_25666.expected_typ);
                    sigtab = (uu___1854_25666.sigtab);
                    attrtab = (uu___1854_25666.attrtab);
                    instantiate_imp = (uu___1854_25666.instantiate_imp);
                    effects =
                      (let uu___1856_25668 = env1.effects  in
                       {
                         decls = (uu___1856_25668.decls);
                         order = (uu___1856_25668.order);
                         joins = (uu___1856_25668.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds));
                         polymonadic_subcomps =
                           (uu___1856_25668.polymonadic_subcomps)
                       });
                    generalize = (uu___1854_25666.generalize);
                    letrecs = (uu___1854_25666.letrecs);
                    top_level = (uu___1854_25666.top_level);
                    check_uvars = (uu___1854_25666.check_uvars);
                    use_eq = (uu___1854_25666.use_eq);
                    use_eq_strict = (uu___1854_25666.use_eq_strict);
                    is_iface = (uu___1854_25666.is_iface);
                    admit = (uu___1854_25666.admit);
                    lax = (uu___1854_25666.lax);
                    lax_universes = (uu___1854_25666.lax_universes);
                    phase1 = (uu___1854_25666.phase1);
                    failhard = (uu___1854_25666.failhard);
                    nosynth = (uu___1854_25666.nosynth);
                    uvar_subtyping = (uu___1854_25666.uvar_subtyping);
                    tc_term = (uu___1854_25666.tc_term);
                    type_of = (uu___1854_25666.type_of);
                    universe_of = (uu___1854_25666.universe_of);
                    check_type_of = (uu___1854_25666.check_type_of);
                    use_bv_sorts = (uu___1854_25666.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1854_25666.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1854_25666.normalized_eff_names);
                    fv_delta_depths = (uu___1854_25666.fv_delta_depths);
                    proof_ns = (uu___1854_25666.proof_ns);
                    synth_hook = (uu___1854_25666.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1854_25666.try_solve_implicits_hook);
                    splice = (uu___1854_25666.splice);
                    mpreprocess = (uu___1854_25666.mpreprocess);
                    postprocess = (uu___1854_25666.postprocess);
                    identifier_info = (uu___1854_25666.identifier_info);
                    tc_hooks = (uu___1854_25666.tc_hooks);
                    dsenv = (uu___1854_25666.dsenv);
                    nbe = (uu___1854_25666.nbe);
                    strict_args_tab = (uu___1854_25666.strict_args_tab);
                    erasable_types_tab = (uu___1854_25666.erasable_types_tab)
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
          let uu___1864_25750 = env1  in
          {
            solver = (uu___1864_25750.solver);
            range = (uu___1864_25750.range);
            curmodule = (uu___1864_25750.curmodule);
            gamma = (uu___1864_25750.gamma);
            gamma_sig = (uu___1864_25750.gamma_sig);
            gamma_cache = (uu___1864_25750.gamma_cache);
            modules = (uu___1864_25750.modules);
            expected_typ = (uu___1864_25750.expected_typ);
            sigtab = (uu___1864_25750.sigtab);
            attrtab = (uu___1864_25750.attrtab);
            instantiate_imp = (uu___1864_25750.instantiate_imp);
            effects =
              (let uu___1866_25752 = env1.effects  in
               {
                 decls = (uu___1866_25752.decls);
                 order = (uu___1866_25752.order);
                 joins = (uu___1866_25752.joins);
                 polymonadic_binds = (uu___1866_25752.polymonadic_binds);
                 polymonadic_subcomps = ((m, n, ts) ::
                   ((env1.effects).polymonadic_subcomps))
               });
            generalize = (uu___1864_25750.generalize);
            letrecs = (uu___1864_25750.letrecs);
            top_level = (uu___1864_25750.top_level);
            check_uvars = (uu___1864_25750.check_uvars);
            use_eq = (uu___1864_25750.use_eq);
            use_eq_strict = (uu___1864_25750.use_eq_strict);
            is_iface = (uu___1864_25750.is_iface);
            admit = (uu___1864_25750.admit);
            lax = (uu___1864_25750.lax);
            lax_universes = (uu___1864_25750.lax_universes);
            phase1 = (uu___1864_25750.phase1);
            failhard = (uu___1864_25750.failhard);
            nosynth = (uu___1864_25750.nosynth);
            uvar_subtyping = (uu___1864_25750.uvar_subtyping);
            tc_term = (uu___1864_25750.tc_term);
            type_of = (uu___1864_25750.type_of);
            universe_of = (uu___1864_25750.universe_of);
            check_type_of = (uu___1864_25750.check_type_of);
            use_bv_sorts = (uu___1864_25750.use_bv_sorts);
            qtbl_name_and_index = (uu___1864_25750.qtbl_name_and_index);
            normalized_eff_names = (uu___1864_25750.normalized_eff_names);
            fv_delta_depths = (uu___1864_25750.fv_delta_depths);
            proof_ns = (uu___1864_25750.proof_ns);
            synth_hook = (uu___1864_25750.synth_hook);
            try_solve_implicits_hook =
              (uu___1864_25750.try_solve_implicits_hook);
            splice = (uu___1864_25750.splice);
            mpreprocess = (uu___1864_25750.mpreprocess);
            postprocess = (uu___1864_25750.postprocess);
            identifier_info = (uu___1864_25750.identifier_info);
            tc_hooks = (uu___1864_25750.tc_hooks);
            dsenv = (uu___1864_25750.dsenv);
            nbe = (uu___1864_25750.nbe);
            strict_args_tab = (uu___1864_25750.strict_args_tab);
            erasable_types_tab = (uu___1864_25750.erasable_types_tab)
          }
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1870_25770 = env1  in
      {
        solver = (uu___1870_25770.solver);
        range = (uu___1870_25770.range);
        curmodule = (uu___1870_25770.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1870_25770.gamma_sig);
        gamma_cache = (uu___1870_25770.gamma_cache);
        modules = (uu___1870_25770.modules);
        expected_typ = (uu___1870_25770.expected_typ);
        sigtab = (uu___1870_25770.sigtab);
        attrtab = (uu___1870_25770.attrtab);
        instantiate_imp = (uu___1870_25770.instantiate_imp);
        effects = (uu___1870_25770.effects);
        generalize = (uu___1870_25770.generalize);
        letrecs = (uu___1870_25770.letrecs);
        top_level = (uu___1870_25770.top_level);
        check_uvars = (uu___1870_25770.check_uvars);
        use_eq = (uu___1870_25770.use_eq);
        use_eq_strict = (uu___1870_25770.use_eq_strict);
        is_iface = (uu___1870_25770.is_iface);
        admit = (uu___1870_25770.admit);
        lax = (uu___1870_25770.lax);
        lax_universes = (uu___1870_25770.lax_universes);
        phase1 = (uu___1870_25770.phase1);
        failhard = (uu___1870_25770.failhard);
        nosynth = (uu___1870_25770.nosynth);
        uvar_subtyping = (uu___1870_25770.uvar_subtyping);
        tc_term = (uu___1870_25770.tc_term);
        type_of = (uu___1870_25770.type_of);
        universe_of = (uu___1870_25770.universe_of);
        check_type_of = (uu___1870_25770.check_type_of);
        use_bv_sorts = (uu___1870_25770.use_bv_sorts);
        qtbl_name_and_index = (uu___1870_25770.qtbl_name_and_index);
        normalized_eff_names = (uu___1870_25770.normalized_eff_names);
        fv_delta_depths = (uu___1870_25770.fv_delta_depths);
        proof_ns = (uu___1870_25770.proof_ns);
        synth_hook = (uu___1870_25770.synth_hook);
        try_solve_implicits_hook = (uu___1870_25770.try_solve_implicits_hook);
        splice = (uu___1870_25770.splice);
        mpreprocess = (uu___1870_25770.mpreprocess);
        postprocess = (uu___1870_25770.postprocess);
        identifier_info = (uu___1870_25770.identifier_info);
        tc_hooks = (uu___1870_25770.tc_hooks);
        dsenv = (uu___1870_25770.dsenv);
        nbe = (uu___1870_25770.nbe);
        strict_args_tab = (uu___1870_25770.strict_args_tab);
        erasable_types_tab = (uu___1870_25770.erasable_types_tab)
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
            (let uu___1883_25828 = env1  in
             {
               solver = (uu___1883_25828.solver);
               range = (uu___1883_25828.range);
               curmodule = (uu___1883_25828.curmodule);
               gamma = rest;
               gamma_sig = (uu___1883_25828.gamma_sig);
               gamma_cache = (uu___1883_25828.gamma_cache);
               modules = (uu___1883_25828.modules);
               expected_typ = (uu___1883_25828.expected_typ);
               sigtab = (uu___1883_25828.sigtab);
               attrtab = (uu___1883_25828.attrtab);
               instantiate_imp = (uu___1883_25828.instantiate_imp);
               effects = (uu___1883_25828.effects);
               generalize = (uu___1883_25828.generalize);
               letrecs = (uu___1883_25828.letrecs);
               top_level = (uu___1883_25828.top_level);
               check_uvars = (uu___1883_25828.check_uvars);
               use_eq = (uu___1883_25828.use_eq);
               use_eq_strict = (uu___1883_25828.use_eq_strict);
               is_iface = (uu___1883_25828.is_iface);
               admit = (uu___1883_25828.admit);
               lax = (uu___1883_25828.lax);
               lax_universes = (uu___1883_25828.lax_universes);
               phase1 = (uu___1883_25828.phase1);
               failhard = (uu___1883_25828.failhard);
               nosynth = (uu___1883_25828.nosynth);
               uvar_subtyping = (uu___1883_25828.uvar_subtyping);
               tc_term = (uu___1883_25828.tc_term);
               type_of = (uu___1883_25828.type_of);
               universe_of = (uu___1883_25828.universe_of);
               check_type_of = (uu___1883_25828.check_type_of);
               use_bv_sorts = (uu___1883_25828.use_bv_sorts);
               qtbl_name_and_index = (uu___1883_25828.qtbl_name_and_index);
               normalized_eff_names = (uu___1883_25828.normalized_eff_names);
               fv_delta_depths = (uu___1883_25828.fv_delta_depths);
               proof_ns = (uu___1883_25828.proof_ns);
               synth_hook = (uu___1883_25828.synth_hook);
               try_solve_implicits_hook =
                 (uu___1883_25828.try_solve_implicits_hook);
               splice = (uu___1883_25828.splice);
               mpreprocess = (uu___1883_25828.mpreprocess);
               postprocess = (uu___1883_25828.postprocess);
               identifier_info = (uu___1883_25828.identifier_info);
               tc_hooks = (uu___1883_25828.tc_hooks);
               dsenv = (uu___1883_25828.dsenv);
               nbe = (uu___1883_25828.nbe);
               strict_args_tab = (uu___1883_25828.strict_args_tab);
               erasable_types_tab = (uu___1883_25828.erasable_types_tab)
             }))
    | uu____25829 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25858  ->
             match uu____25858 with | (x,uu____25866) -> push_bv env2 x) env1
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
            let uu___1897_25901 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1897_25901.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1897_25901.FStar_Syntax_Syntax.index);
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
        let uu____25974 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25974 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____26002 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26002)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1918_26018 = env1  in
      {
        solver = (uu___1918_26018.solver);
        range = (uu___1918_26018.range);
        curmodule = (uu___1918_26018.curmodule);
        gamma = (uu___1918_26018.gamma);
        gamma_sig = (uu___1918_26018.gamma_sig);
        gamma_cache = (uu___1918_26018.gamma_cache);
        modules = (uu___1918_26018.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1918_26018.sigtab);
        attrtab = (uu___1918_26018.attrtab);
        instantiate_imp = (uu___1918_26018.instantiate_imp);
        effects = (uu___1918_26018.effects);
        generalize = (uu___1918_26018.generalize);
        letrecs = (uu___1918_26018.letrecs);
        top_level = (uu___1918_26018.top_level);
        check_uvars = (uu___1918_26018.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1918_26018.use_eq_strict);
        is_iface = (uu___1918_26018.is_iface);
        admit = (uu___1918_26018.admit);
        lax = (uu___1918_26018.lax);
        lax_universes = (uu___1918_26018.lax_universes);
        phase1 = (uu___1918_26018.phase1);
        failhard = (uu___1918_26018.failhard);
        nosynth = (uu___1918_26018.nosynth);
        uvar_subtyping = (uu___1918_26018.uvar_subtyping);
        tc_term = (uu___1918_26018.tc_term);
        type_of = (uu___1918_26018.type_of);
        universe_of = (uu___1918_26018.universe_of);
        check_type_of = (uu___1918_26018.check_type_of);
        use_bv_sorts = (uu___1918_26018.use_bv_sorts);
        qtbl_name_and_index = (uu___1918_26018.qtbl_name_and_index);
        normalized_eff_names = (uu___1918_26018.normalized_eff_names);
        fv_delta_depths = (uu___1918_26018.fv_delta_depths);
        proof_ns = (uu___1918_26018.proof_ns);
        synth_hook = (uu___1918_26018.synth_hook);
        try_solve_implicits_hook = (uu___1918_26018.try_solve_implicits_hook);
        splice = (uu___1918_26018.splice);
        mpreprocess = (uu___1918_26018.mpreprocess);
        postprocess = (uu___1918_26018.postprocess);
        identifier_info = (uu___1918_26018.identifier_info);
        tc_hooks = (uu___1918_26018.tc_hooks);
        dsenv = (uu___1918_26018.dsenv);
        nbe = (uu___1918_26018.nbe);
        strict_args_tab = (uu___1918_26018.strict_args_tab);
        erasable_types_tab = (uu___1918_26018.erasable_types_tab)
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
    let uu____26049 = expected_typ env_  in
    ((let uu___1925_26055 = env_  in
      {
        solver = (uu___1925_26055.solver);
        range = (uu___1925_26055.range);
        curmodule = (uu___1925_26055.curmodule);
        gamma = (uu___1925_26055.gamma);
        gamma_sig = (uu___1925_26055.gamma_sig);
        gamma_cache = (uu___1925_26055.gamma_cache);
        modules = (uu___1925_26055.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1925_26055.sigtab);
        attrtab = (uu___1925_26055.attrtab);
        instantiate_imp = (uu___1925_26055.instantiate_imp);
        effects = (uu___1925_26055.effects);
        generalize = (uu___1925_26055.generalize);
        letrecs = (uu___1925_26055.letrecs);
        top_level = (uu___1925_26055.top_level);
        check_uvars = (uu___1925_26055.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1925_26055.use_eq_strict);
        is_iface = (uu___1925_26055.is_iface);
        admit = (uu___1925_26055.admit);
        lax = (uu___1925_26055.lax);
        lax_universes = (uu___1925_26055.lax_universes);
        phase1 = (uu___1925_26055.phase1);
        failhard = (uu___1925_26055.failhard);
        nosynth = (uu___1925_26055.nosynth);
        uvar_subtyping = (uu___1925_26055.uvar_subtyping);
        tc_term = (uu___1925_26055.tc_term);
        type_of = (uu___1925_26055.type_of);
        universe_of = (uu___1925_26055.universe_of);
        check_type_of = (uu___1925_26055.check_type_of);
        use_bv_sorts = (uu___1925_26055.use_bv_sorts);
        qtbl_name_and_index = (uu___1925_26055.qtbl_name_and_index);
        normalized_eff_names = (uu___1925_26055.normalized_eff_names);
        fv_delta_depths = (uu___1925_26055.fv_delta_depths);
        proof_ns = (uu___1925_26055.proof_ns);
        synth_hook = (uu___1925_26055.synth_hook);
        try_solve_implicits_hook = (uu___1925_26055.try_solve_implicits_hook);
        splice = (uu___1925_26055.splice);
        mpreprocess = (uu___1925_26055.mpreprocess);
        postprocess = (uu___1925_26055.postprocess);
        identifier_info = (uu___1925_26055.identifier_info);
        tc_hooks = (uu___1925_26055.tc_hooks);
        dsenv = (uu___1925_26055.dsenv);
        nbe = (uu___1925_26055.nbe);
        strict_args_tab = (uu___1925_26055.strict_args_tab);
        erasable_types_tab = (uu___1925_26055.erasable_types_tab)
      }), uu____26049)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26067 =
      let uu____26068 = FStar_Ident.id_of_text ""  in [uu____26068]  in
    FStar_Ident.lid_of_ids uu____26067  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____26075 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26075
        then
          let uu____26080 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26080 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1933_26108 = env1  in
       {
         solver = (uu___1933_26108.solver);
         range = (uu___1933_26108.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1933_26108.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1933_26108.expected_typ);
         sigtab = (uu___1933_26108.sigtab);
         attrtab = (uu___1933_26108.attrtab);
         instantiate_imp = (uu___1933_26108.instantiate_imp);
         effects = (uu___1933_26108.effects);
         generalize = (uu___1933_26108.generalize);
         letrecs = (uu___1933_26108.letrecs);
         top_level = (uu___1933_26108.top_level);
         check_uvars = (uu___1933_26108.check_uvars);
         use_eq = (uu___1933_26108.use_eq);
         use_eq_strict = (uu___1933_26108.use_eq_strict);
         is_iface = (uu___1933_26108.is_iface);
         admit = (uu___1933_26108.admit);
         lax = (uu___1933_26108.lax);
         lax_universes = (uu___1933_26108.lax_universes);
         phase1 = (uu___1933_26108.phase1);
         failhard = (uu___1933_26108.failhard);
         nosynth = (uu___1933_26108.nosynth);
         uvar_subtyping = (uu___1933_26108.uvar_subtyping);
         tc_term = (uu___1933_26108.tc_term);
         type_of = (uu___1933_26108.type_of);
         universe_of = (uu___1933_26108.universe_of);
         check_type_of = (uu___1933_26108.check_type_of);
         use_bv_sorts = (uu___1933_26108.use_bv_sorts);
         qtbl_name_and_index = (uu___1933_26108.qtbl_name_and_index);
         normalized_eff_names = (uu___1933_26108.normalized_eff_names);
         fv_delta_depths = (uu___1933_26108.fv_delta_depths);
         proof_ns = (uu___1933_26108.proof_ns);
         synth_hook = (uu___1933_26108.synth_hook);
         try_solve_implicits_hook =
           (uu___1933_26108.try_solve_implicits_hook);
         splice = (uu___1933_26108.splice);
         mpreprocess = (uu___1933_26108.mpreprocess);
         postprocess = (uu___1933_26108.postprocess);
         identifier_info = (uu___1933_26108.identifier_info);
         tc_hooks = (uu___1933_26108.tc_hooks);
         dsenv = (uu___1933_26108.dsenv);
         nbe = (uu___1933_26108.nbe);
         strict_args_tab = (uu___1933_26108.strict_args_tab);
         erasable_types_tab = (uu___1933_26108.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26160)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26164,(uu____26165,t)))::tl
          ->
          let uu____26186 =
            let uu____26189 = FStar_Syntax_Free.uvars t  in
            ext out uu____26189  in
          aux uu____26186 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26192;
            FStar_Syntax_Syntax.index = uu____26193;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26201 =
            let uu____26204 = FStar_Syntax_Free.uvars t  in
            ext out uu____26204  in
          aux uu____26201 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26262)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26266,(uu____26267,t)))::tl
          ->
          let uu____26288 =
            let uu____26291 = FStar_Syntax_Free.univs t  in
            ext out uu____26291  in
          aux uu____26288 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26294;
            FStar_Syntax_Syntax.index = uu____26295;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26303 =
            let uu____26306 = FStar_Syntax_Free.univs t  in
            ext out uu____26306  in
          aux uu____26303 tl
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
          let uu____26368 = FStar_Util.set_add uname out  in
          aux uu____26368 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26371,(uu____26372,t)))::tl
          ->
          let uu____26393 =
            let uu____26396 = FStar_Syntax_Free.univnames t  in
            ext out uu____26396  in
          aux uu____26393 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26399;
            FStar_Syntax_Syntax.index = uu____26400;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26408 =
            let uu____26411 = FStar_Syntax_Free.univnames t  in
            ext out uu____26411  in
          aux uu____26408 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26432  ->
            match uu___12_26432 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26436 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26449 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26460 =
      let uu____26469 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26469
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26460 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26517 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26530  ->
              match uu___13_26530 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26533 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26533
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26537 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26537
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26541) ->
                  let uu____26558 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26558))
       in
    FStar_All.pipe_right uu____26517 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26572  ->
    match uu___14_26572 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26578 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26578
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26601  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26656) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26689,uu____26690) -> false  in
      let uu____26704 =
        FStar_List.tryFind
          (fun uu____26726  ->
             match uu____26726 with | (p,uu____26737) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26704 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26756,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26786 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26786
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2076_26808 = e  in
        {
          solver = (uu___2076_26808.solver);
          range = (uu___2076_26808.range);
          curmodule = (uu___2076_26808.curmodule);
          gamma = (uu___2076_26808.gamma);
          gamma_sig = (uu___2076_26808.gamma_sig);
          gamma_cache = (uu___2076_26808.gamma_cache);
          modules = (uu___2076_26808.modules);
          expected_typ = (uu___2076_26808.expected_typ);
          sigtab = (uu___2076_26808.sigtab);
          attrtab = (uu___2076_26808.attrtab);
          instantiate_imp = (uu___2076_26808.instantiate_imp);
          effects = (uu___2076_26808.effects);
          generalize = (uu___2076_26808.generalize);
          letrecs = (uu___2076_26808.letrecs);
          top_level = (uu___2076_26808.top_level);
          check_uvars = (uu___2076_26808.check_uvars);
          use_eq = (uu___2076_26808.use_eq);
          use_eq_strict = (uu___2076_26808.use_eq_strict);
          is_iface = (uu___2076_26808.is_iface);
          admit = (uu___2076_26808.admit);
          lax = (uu___2076_26808.lax);
          lax_universes = (uu___2076_26808.lax_universes);
          phase1 = (uu___2076_26808.phase1);
          failhard = (uu___2076_26808.failhard);
          nosynth = (uu___2076_26808.nosynth);
          uvar_subtyping = (uu___2076_26808.uvar_subtyping);
          tc_term = (uu___2076_26808.tc_term);
          type_of = (uu___2076_26808.type_of);
          universe_of = (uu___2076_26808.universe_of);
          check_type_of = (uu___2076_26808.check_type_of);
          use_bv_sorts = (uu___2076_26808.use_bv_sorts);
          qtbl_name_and_index = (uu___2076_26808.qtbl_name_and_index);
          normalized_eff_names = (uu___2076_26808.normalized_eff_names);
          fv_delta_depths = (uu___2076_26808.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2076_26808.synth_hook);
          try_solve_implicits_hook =
            (uu___2076_26808.try_solve_implicits_hook);
          splice = (uu___2076_26808.splice);
          mpreprocess = (uu___2076_26808.mpreprocess);
          postprocess = (uu___2076_26808.postprocess);
          identifier_info = (uu___2076_26808.identifier_info);
          tc_hooks = (uu___2076_26808.tc_hooks);
          dsenv = (uu___2076_26808.dsenv);
          nbe = (uu___2076_26808.nbe);
          strict_args_tab = (uu___2076_26808.strict_args_tab);
          erasable_types_tab = (uu___2076_26808.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2085_26856 = e  in
      {
        solver = (uu___2085_26856.solver);
        range = (uu___2085_26856.range);
        curmodule = (uu___2085_26856.curmodule);
        gamma = (uu___2085_26856.gamma);
        gamma_sig = (uu___2085_26856.gamma_sig);
        gamma_cache = (uu___2085_26856.gamma_cache);
        modules = (uu___2085_26856.modules);
        expected_typ = (uu___2085_26856.expected_typ);
        sigtab = (uu___2085_26856.sigtab);
        attrtab = (uu___2085_26856.attrtab);
        instantiate_imp = (uu___2085_26856.instantiate_imp);
        effects = (uu___2085_26856.effects);
        generalize = (uu___2085_26856.generalize);
        letrecs = (uu___2085_26856.letrecs);
        top_level = (uu___2085_26856.top_level);
        check_uvars = (uu___2085_26856.check_uvars);
        use_eq = (uu___2085_26856.use_eq);
        use_eq_strict = (uu___2085_26856.use_eq_strict);
        is_iface = (uu___2085_26856.is_iface);
        admit = (uu___2085_26856.admit);
        lax = (uu___2085_26856.lax);
        lax_universes = (uu___2085_26856.lax_universes);
        phase1 = (uu___2085_26856.phase1);
        failhard = (uu___2085_26856.failhard);
        nosynth = (uu___2085_26856.nosynth);
        uvar_subtyping = (uu___2085_26856.uvar_subtyping);
        tc_term = (uu___2085_26856.tc_term);
        type_of = (uu___2085_26856.type_of);
        universe_of = (uu___2085_26856.universe_of);
        check_type_of = (uu___2085_26856.check_type_of);
        use_bv_sorts = (uu___2085_26856.use_bv_sorts);
        qtbl_name_and_index = (uu___2085_26856.qtbl_name_and_index);
        normalized_eff_names = (uu___2085_26856.normalized_eff_names);
        fv_delta_depths = (uu___2085_26856.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2085_26856.synth_hook);
        try_solve_implicits_hook = (uu___2085_26856.try_solve_implicits_hook);
        splice = (uu___2085_26856.splice);
        mpreprocess = (uu___2085_26856.mpreprocess);
        postprocess = (uu___2085_26856.postprocess);
        identifier_info = (uu___2085_26856.identifier_info);
        tc_hooks = (uu___2085_26856.tc_hooks);
        dsenv = (uu___2085_26856.dsenv);
        nbe = (uu___2085_26856.nbe);
        strict_args_tab = (uu___2085_26856.strict_args_tab);
        erasable_types_tab = (uu___2085_26856.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26872 = FStar_Syntax_Free.names t  in
      let uu____26875 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26872 uu____26875
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26898 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26898
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26908 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26908
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____26929 =
      match uu____26929 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26949 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26949)
       in
    let uu____26957 =
      let uu____26961 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____26961 FStar_List.rev  in
    FStar_All.pipe_right uu____26957 (FStar_String.concat " ")
  
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
                  (let uu____27029 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27029 with
                   | FStar_Pervasives_Native.Some uu____27033 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27036 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27046;
        FStar_TypeChecker_Common.univ_ineqs = uu____27047;
        FStar_TypeChecker_Common.implicits = uu____27048;_} -> true
    | uu____27058 -> false
  
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
          let uu___2129_27080 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2129_27080.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2129_27080.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2129_27080.FStar_TypeChecker_Common.implicits)
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
          let uu____27119 = FStar_Options.defensive ()  in
          if uu____27119
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27125 =
              let uu____27127 =
                let uu____27129 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27129  in
              Prims.op_Negation uu____27127  in
            (if uu____27125
             then
               let uu____27136 =
                 let uu____27142 =
                   let uu____27144 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27146 =
                     let uu____27148 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27148
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27144 uu____27146
                    in
                 (FStar_Errors.Warning_Defensive, uu____27142)  in
               FStar_Errors.log_issue rng uu____27136
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
          let uu____27188 =
            let uu____27190 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27190  in
          if uu____27188
          then ()
          else
            (let uu____27195 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27195 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27221 =
            let uu____27223 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27223  in
          if uu____27221
          then ()
          else
            (let uu____27228 = bound_vars e  in
             def_check_closed_in rng msg uu____27228 t)
  
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
          let uu___2166_27267 = g  in
          let uu____27268 =
            let uu____27269 =
              let uu____27270 =
                let uu____27277 =
                  let uu____27278 =
                    let uu____27295 =
                      let uu____27306 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27306]  in
                    (f, uu____27295)  in
                  FStar_Syntax_Syntax.Tm_app uu____27278  in
                FStar_Syntax_Syntax.mk uu____27277  in
              uu____27270 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27343  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27343) uu____27269
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27268;
            FStar_TypeChecker_Common.deferred =
              (uu___2166_27267.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2166_27267.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2166_27267.FStar_TypeChecker_Common.implicits)
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
          let uu___2173_27361 = g  in
          let uu____27362 =
            let uu____27363 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27363  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27362;
            FStar_TypeChecker_Common.deferred =
              (uu___2173_27361.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2173_27361.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2173_27361.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2178_27380 = g  in
          let uu____27381 =
            let uu____27382 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27382  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27381;
            FStar_TypeChecker_Common.deferred =
              (uu___2178_27380.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2178_27380.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2178_27380.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2182_27384 = g  in
          let uu____27385 =
            let uu____27386 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27386  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27385;
            FStar_TypeChecker_Common.deferred =
              (uu___2182_27384.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2182_27384.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2182_27384.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27393 ->
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
                       let uu____27470 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27470
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2205_27477 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2205_27477.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2205_27477.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2205_27477.FStar_TypeChecker_Common.implicits)
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
               let uu____27511 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27511
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
            let uu___2220_27538 = g  in
            let uu____27539 =
              let uu____27540 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27540  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27539;
              FStar_TypeChecker_Common.deferred =
                (uu___2220_27538.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2220_27538.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2220_27538.FStar_TypeChecker_Common.implicits)
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
              let uu____27598 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27598 with
              | FStar_Pervasives_Native.Some
                  (uu____27623::(tm,uu____27625)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27689 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27707 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27707;
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
                    (let uu____27739 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27739
                     then
                       let uu____27743 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27743
                     else ());
                    (let g =
                       let uu___2244_27749 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2244_27749.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2244_27749.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2244_27749.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27803 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27860  ->
                      fun b  ->
                        match uu____27860 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27902 =
                              let uu____27915 = reason b  in
                              new_implicit_var_aux uu____27915 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27902 with
                             | (t,uu____27932,g_t) ->
                                 let uu____27946 =
                                   let uu____27949 =
                                     let uu____27952 =
                                       let uu____27953 =
                                         let uu____27960 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27960, t)  in
                                       FStar_Syntax_Syntax.NT uu____27953  in
                                     [uu____27952]  in
                                   FStar_List.append substs1 uu____27949  in
                                 let uu____27971 = conj_guard g g_t  in
                                 (uu____27946, (FStar_List.append uvars [t]),
                                   uu____27971))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27803
              (fun uu____28000  ->
                 match uu____28000 with | (uu____28017,uvars,g) -> (uvars, g))
  
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
                let uu____28058 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28058 FStar_Util.must  in
              let uu____28075 = inst_tscheme_with post_ts [u]  in
              match uu____28075 with
              | (uu____28080,post) ->
                  let uu____28082 =
                    let uu____28087 =
                      let uu____28088 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28088]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28087  in
                  uu____28082 FStar_Pervasives_Native.None r
               in
            let uu____28121 =
              let uu____28126 =
                let uu____28127 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28127]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28126  in
            uu____28121 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28163  -> ());
    push = (fun uu____28165  -> ());
    pop = (fun uu____28168  -> ());
    snapshot =
      (fun uu____28171  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28190  -> fun uu____28191  -> ());
    encode_sig = (fun uu____28206  -> fun uu____28207  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28213 =
             let uu____28220 = FStar_Options.peek ()  in (e, g, uu____28220)
              in
           [uu____28213]);
    solve = (fun uu____28236  -> fun uu____28237  -> fun uu____28238  -> ());
    finish = (fun uu____28245  -> ());
    refresh = (fun uu____28247  -> ())
  } 