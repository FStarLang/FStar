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
  fun projectee  -> match projectee with | Beta  -> true | uu____105 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____116 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____127 -> false 
let (uu___is_ZetaFull : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ZetaFull  -> true | uu____138 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____150 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____168 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____179 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____190 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____201 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____212 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____223 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____235 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____256 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____283 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____310 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____334 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____345 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____356 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____367 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____378 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____389 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____400 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____411 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____422 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____433 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____444 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____455 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____466 -> false
  
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
      | uu____527 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____553 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____564 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____575 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____587 -> false
  
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
           (fun uu___0_14193  ->
              match uu___0_14193 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14196 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____14196  in
                  let uu____14197 =
                    let uu____14198 = FStar_Syntax_Subst.compress y  in
                    uu____14198.FStar_Syntax_Syntax.n  in
                  (match uu____14197 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14202 =
                         let uu___324_14203 = y1  in
                         let uu____14204 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___324_14203.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___324_14203.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14204
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14202
                   | uu____14207 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst  ->
    fun env1  ->
      let uu___330_14221 = env1  in
      let uu____14222 = rename_gamma subst env1.gamma  in
      {
        solver = (uu___330_14221.solver);
        range = (uu___330_14221.range);
        curmodule = (uu___330_14221.curmodule);
        gamma = uu____14222;
        gamma_sig = (uu___330_14221.gamma_sig);
        gamma_cache = (uu___330_14221.gamma_cache);
        modules = (uu___330_14221.modules);
        expected_typ = (uu___330_14221.expected_typ);
        sigtab = (uu___330_14221.sigtab);
        attrtab = (uu___330_14221.attrtab);
        instantiate_imp = (uu___330_14221.instantiate_imp);
        effects = (uu___330_14221.effects);
        generalize = (uu___330_14221.generalize);
        letrecs = (uu___330_14221.letrecs);
        top_level = (uu___330_14221.top_level);
        check_uvars = (uu___330_14221.check_uvars);
        use_eq = (uu___330_14221.use_eq);
        use_eq_strict = (uu___330_14221.use_eq_strict);
        is_iface = (uu___330_14221.is_iface);
        admit = (uu___330_14221.admit);
        lax = (uu___330_14221.lax);
        lax_universes = (uu___330_14221.lax_universes);
        phase1 = (uu___330_14221.phase1);
        failhard = (uu___330_14221.failhard);
        nosynth = (uu___330_14221.nosynth);
        uvar_subtyping = (uu___330_14221.uvar_subtyping);
        tc_term = (uu___330_14221.tc_term);
        type_of = (uu___330_14221.type_of);
        universe_of = (uu___330_14221.universe_of);
        check_type_of = (uu___330_14221.check_type_of);
        use_bv_sorts = (uu___330_14221.use_bv_sorts);
        qtbl_name_and_index = (uu___330_14221.qtbl_name_and_index);
        normalized_eff_names = (uu___330_14221.normalized_eff_names);
        fv_delta_depths = (uu___330_14221.fv_delta_depths);
        proof_ns = (uu___330_14221.proof_ns);
        synth_hook = (uu___330_14221.synth_hook);
        try_solve_implicits_hook = (uu___330_14221.try_solve_implicits_hook);
        splice = (uu___330_14221.splice);
        mpreprocess = (uu___330_14221.mpreprocess);
        postprocess = (uu___330_14221.postprocess);
        identifier_info = (uu___330_14221.identifier_info);
        tc_hooks = (uu___330_14221.tc_hooks);
        dsenv = (uu___330_14221.dsenv);
        nbe = (uu___330_14221.nbe);
        strict_args_tab = (uu___330_14221.strict_args_tab);
        erasable_types_tab = (uu___330_14221.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14230  -> fun uu____14231  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___337_14253 = env1  in
      {
        solver = (uu___337_14253.solver);
        range = (uu___337_14253.range);
        curmodule = (uu___337_14253.curmodule);
        gamma = (uu___337_14253.gamma);
        gamma_sig = (uu___337_14253.gamma_sig);
        gamma_cache = (uu___337_14253.gamma_cache);
        modules = (uu___337_14253.modules);
        expected_typ = (uu___337_14253.expected_typ);
        sigtab = (uu___337_14253.sigtab);
        attrtab = (uu___337_14253.attrtab);
        instantiate_imp = (uu___337_14253.instantiate_imp);
        effects = (uu___337_14253.effects);
        generalize = (uu___337_14253.generalize);
        letrecs = (uu___337_14253.letrecs);
        top_level = (uu___337_14253.top_level);
        check_uvars = (uu___337_14253.check_uvars);
        use_eq = (uu___337_14253.use_eq);
        use_eq_strict = (uu___337_14253.use_eq_strict);
        is_iface = (uu___337_14253.is_iface);
        admit = (uu___337_14253.admit);
        lax = (uu___337_14253.lax);
        lax_universes = (uu___337_14253.lax_universes);
        phase1 = (uu___337_14253.phase1);
        failhard = (uu___337_14253.failhard);
        nosynth = (uu___337_14253.nosynth);
        uvar_subtyping = (uu___337_14253.uvar_subtyping);
        tc_term = (uu___337_14253.tc_term);
        type_of = (uu___337_14253.type_of);
        universe_of = (uu___337_14253.universe_of);
        check_type_of = (uu___337_14253.check_type_of);
        use_bv_sorts = (uu___337_14253.use_bv_sorts);
        qtbl_name_and_index = (uu___337_14253.qtbl_name_and_index);
        normalized_eff_names = (uu___337_14253.normalized_eff_names);
        fv_delta_depths = (uu___337_14253.fv_delta_depths);
        proof_ns = (uu___337_14253.proof_ns);
        synth_hook = (uu___337_14253.synth_hook);
        try_solve_implicits_hook = (uu___337_14253.try_solve_implicits_hook);
        splice = (uu___337_14253.splice);
        mpreprocess = (uu___337_14253.mpreprocess);
        postprocess = (uu___337_14253.postprocess);
        identifier_info = (uu___337_14253.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___337_14253.dsenv);
        nbe = (uu___337_14253.nbe);
        strict_args_tab = (uu___337_14253.strict_args_tab);
        erasable_types_tab = (uu___337_14253.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___341_14265 = e  in
      let uu____14266 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___341_14265.solver);
        range = (uu___341_14265.range);
        curmodule = (uu___341_14265.curmodule);
        gamma = (uu___341_14265.gamma);
        gamma_sig = (uu___341_14265.gamma_sig);
        gamma_cache = (uu___341_14265.gamma_cache);
        modules = (uu___341_14265.modules);
        expected_typ = (uu___341_14265.expected_typ);
        sigtab = (uu___341_14265.sigtab);
        attrtab = (uu___341_14265.attrtab);
        instantiate_imp = (uu___341_14265.instantiate_imp);
        effects = (uu___341_14265.effects);
        generalize = (uu___341_14265.generalize);
        letrecs = (uu___341_14265.letrecs);
        top_level = (uu___341_14265.top_level);
        check_uvars = (uu___341_14265.check_uvars);
        use_eq = (uu___341_14265.use_eq);
        use_eq_strict = (uu___341_14265.use_eq_strict);
        is_iface = (uu___341_14265.is_iface);
        admit = (uu___341_14265.admit);
        lax = (uu___341_14265.lax);
        lax_universes = (uu___341_14265.lax_universes);
        phase1 = (uu___341_14265.phase1);
        failhard = (uu___341_14265.failhard);
        nosynth = (uu___341_14265.nosynth);
        uvar_subtyping = (uu___341_14265.uvar_subtyping);
        tc_term = (uu___341_14265.tc_term);
        type_of = (uu___341_14265.type_of);
        universe_of = (uu___341_14265.universe_of);
        check_type_of = (uu___341_14265.check_type_of);
        use_bv_sorts = (uu___341_14265.use_bv_sorts);
        qtbl_name_and_index = (uu___341_14265.qtbl_name_and_index);
        normalized_eff_names = (uu___341_14265.normalized_eff_names);
        fv_delta_depths = (uu___341_14265.fv_delta_depths);
        proof_ns = (uu___341_14265.proof_ns);
        synth_hook = (uu___341_14265.synth_hook);
        try_solve_implicits_hook = (uu___341_14265.try_solve_implicits_hook);
        splice = (uu___341_14265.splice);
        mpreprocess = (uu___341_14265.mpreprocess);
        postprocess = (uu___341_14265.postprocess);
        identifier_info = (uu___341_14265.identifier_info);
        tc_hooks = (uu___341_14265.tc_hooks);
        dsenv = uu____14266;
        nbe = (uu___341_14265.nbe);
        strict_args_tab = (uu___341_14265.strict_args_tab);
        erasable_types_tab = (uu___341_14265.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14283 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____14283)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14298) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14301,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14303,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14306 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14320 . unit -> 'uuuuuu14320 FStar_Util.smap =
  fun uu____14327  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14333 . unit -> 'uuuuuu14333 FStar_Util.smap =
  fun uu____14340  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14478 = new_gamma_cache ()  in
                  let uu____14481 = new_sigtab ()  in
                  let uu____14484 = new_sigtab ()  in
                  let uu____14491 =
                    let uu____14506 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14506, FStar_Pervasives_Native.None)  in
                  let uu____14527 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14531 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14535 = FStar_Options.using_facts_from ()  in
                  let uu____14536 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14539 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14540 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14554 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14478;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14481;
                    attrtab = uu____14484;
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
                    qtbl_name_and_index = uu____14491;
                    normalized_eff_names = uu____14527;
                    fv_delta_depths = uu____14531;
                    proof_ns = uu____14535;
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
                    identifier_info = uu____14536;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14539;
                    nbe;
                    strict_args_tab = uu____14540;
                    erasable_types_tab = uu____14554
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
  fun uu____14750  ->
    let uu____14751 = FStar_ST.op_Bang query_indices  in
    match uu____14751 with
    | [] -> failwith "Empty query indices!"
    | uu____14806 ->
        let uu____14816 =
          let uu____14826 =
            let uu____14834 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14834  in
          let uu____14888 = FStar_ST.op_Bang query_indices  in uu____14826 ::
            uu____14888
           in
        FStar_ST.op_Colon_Equals query_indices uu____14816
  
let (pop_query_indices : unit -> unit) =
  fun uu____14984  ->
    let uu____14985 = FStar_ST.op_Bang query_indices  in
    match uu____14985 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____15112  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____15149  ->
    match uu____15149 with
    | (l,n) ->
        let uu____15159 = FStar_ST.op_Bang query_indices  in
        (match uu____15159 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15281 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15304  ->
    let uu____15305 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15305
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15373 =
       let uu____15376 = FStar_ST.op_Bang stack  in env1 :: uu____15376  in
     FStar_ST.op_Colon_Equals stack uu____15373);
    (let uu___415_15425 = env1  in
     let uu____15426 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15429 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15432 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15439 =
       let uu____15454 =
         let uu____15458 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15458  in
       let uu____15490 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15454, uu____15490)  in
     let uu____15539 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15542 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15545 =
       let uu____15548 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15548  in
     let uu____15568 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15581 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___415_15425.solver);
       range = (uu___415_15425.range);
       curmodule = (uu___415_15425.curmodule);
       gamma = (uu___415_15425.gamma);
       gamma_sig = (uu___415_15425.gamma_sig);
       gamma_cache = uu____15426;
       modules = (uu___415_15425.modules);
       expected_typ = (uu___415_15425.expected_typ);
       sigtab = uu____15429;
       attrtab = uu____15432;
       instantiate_imp = (uu___415_15425.instantiate_imp);
       effects = (uu___415_15425.effects);
       generalize = (uu___415_15425.generalize);
       letrecs = (uu___415_15425.letrecs);
       top_level = (uu___415_15425.top_level);
       check_uvars = (uu___415_15425.check_uvars);
       use_eq = (uu___415_15425.use_eq);
       use_eq_strict = (uu___415_15425.use_eq_strict);
       is_iface = (uu___415_15425.is_iface);
       admit = (uu___415_15425.admit);
       lax = (uu___415_15425.lax);
       lax_universes = (uu___415_15425.lax_universes);
       phase1 = (uu___415_15425.phase1);
       failhard = (uu___415_15425.failhard);
       nosynth = (uu___415_15425.nosynth);
       uvar_subtyping = (uu___415_15425.uvar_subtyping);
       tc_term = (uu___415_15425.tc_term);
       type_of = (uu___415_15425.type_of);
       universe_of = (uu___415_15425.universe_of);
       check_type_of = (uu___415_15425.check_type_of);
       use_bv_sorts = (uu___415_15425.use_bv_sorts);
       qtbl_name_and_index = uu____15439;
       normalized_eff_names = uu____15539;
       fv_delta_depths = uu____15542;
       proof_ns = (uu___415_15425.proof_ns);
       synth_hook = (uu___415_15425.synth_hook);
       try_solve_implicits_hook = (uu___415_15425.try_solve_implicits_hook);
       splice = (uu___415_15425.splice);
       mpreprocess = (uu___415_15425.mpreprocess);
       postprocess = (uu___415_15425.postprocess);
       identifier_info = uu____15545;
       tc_hooks = (uu___415_15425.tc_hooks);
       dsenv = (uu___415_15425.dsenv);
       nbe = (uu___415_15425.nbe);
       strict_args_tab = uu____15568;
       erasable_types_tab = uu____15581
     })
  
let (pop_stack : unit -> env) =
  fun uu____15591  ->
    let uu____15592 = FStar_ST.op_Bang stack  in
    match uu____15592 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15646 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15736  ->
           let uu____15737 = snapshot_stack env1  in
           match uu____15737 with
           | (stack_depth,env2) ->
               let uu____15771 = snapshot_query_indices ()  in
               (match uu____15771 with
                | (query_indices_depth,()) ->
                    let uu____15804 = (env2.solver).snapshot msg  in
                    (match uu____15804 with
                     | (solver_depth,()) ->
                         let uu____15861 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____15861 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___440_15928 = env2  in
                                 {
                                   solver = (uu___440_15928.solver);
                                   range = (uu___440_15928.range);
                                   curmodule = (uu___440_15928.curmodule);
                                   gamma = (uu___440_15928.gamma);
                                   gamma_sig = (uu___440_15928.gamma_sig);
                                   gamma_cache = (uu___440_15928.gamma_cache);
                                   modules = (uu___440_15928.modules);
                                   expected_typ =
                                     (uu___440_15928.expected_typ);
                                   sigtab = (uu___440_15928.sigtab);
                                   attrtab = (uu___440_15928.attrtab);
                                   instantiate_imp =
                                     (uu___440_15928.instantiate_imp);
                                   effects = (uu___440_15928.effects);
                                   generalize = (uu___440_15928.generalize);
                                   letrecs = (uu___440_15928.letrecs);
                                   top_level = (uu___440_15928.top_level);
                                   check_uvars = (uu___440_15928.check_uvars);
                                   use_eq = (uu___440_15928.use_eq);
                                   use_eq_strict =
                                     (uu___440_15928.use_eq_strict);
                                   is_iface = (uu___440_15928.is_iface);
                                   admit = (uu___440_15928.admit);
                                   lax = (uu___440_15928.lax);
                                   lax_universes =
                                     (uu___440_15928.lax_universes);
                                   phase1 = (uu___440_15928.phase1);
                                   failhard = (uu___440_15928.failhard);
                                   nosynth = (uu___440_15928.nosynth);
                                   uvar_subtyping =
                                     (uu___440_15928.uvar_subtyping);
                                   tc_term = (uu___440_15928.tc_term);
                                   type_of = (uu___440_15928.type_of);
                                   universe_of = (uu___440_15928.universe_of);
                                   check_type_of =
                                     (uu___440_15928.check_type_of);
                                   use_bv_sorts =
                                     (uu___440_15928.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___440_15928.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___440_15928.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___440_15928.fv_delta_depths);
                                   proof_ns = (uu___440_15928.proof_ns);
                                   synth_hook = (uu___440_15928.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___440_15928.try_solve_implicits_hook);
                                   splice = (uu___440_15928.splice);
                                   mpreprocess = (uu___440_15928.mpreprocess);
                                   postprocess = (uu___440_15928.postprocess);
                                   identifier_info =
                                     (uu___440_15928.identifier_info);
                                   tc_hooks = (uu___440_15928.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___440_15928.nbe);
                                   strict_args_tab =
                                     (uu___440_15928.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___440_15928.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15962  ->
             let uu____15963 =
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
             match uu____15963 with
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
                             ((let uu____16143 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____16143
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____16159 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____16159
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____16191,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____16233 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16263  ->
                  match uu____16263 with
                  | (m,uu____16271) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16233 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16285 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16285 next);
              (let uu___485_16288 = env1  in
               {
                 solver = (uu___485_16288.solver);
                 range = (uu___485_16288.range);
                 curmodule = (uu___485_16288.curmodule);
                 gamma = (uu___485_16288.gamma);
                 gamma_sig = (uu___485_16288.gamma_sig);
                 gamma_cache = (uu___485_16288.gamma_cache);
                 modules = (uu___485_16288.modules);
                 expected_typ = (uu___485_16288.expected_typ);
                 sigtab = (uu___485_16288.sigtab);
                 attrtab = (uu___485_16288.attrtab);
                 instantiate_imp = (uu___485_16288.instantiate_imp);
                 effects = (uu___485_16288.effects);
                 generalize = (uu___485_16288.generalize);
                 letrecs = (uu___485_16288.letrecs);
                 top_level = (uu___485_16288.top_level);
                 check_uvars = (uu___485_16288.check_uvars);
                 use_eq = (uu___485_16288.use_eq);
                 use_eq_strict = (uu___485_16288.use_eq_strict);
                 is_iface = (uu___485_16288.is_iface);
                 admit = (uu___485_16288.admit);
                 lax = (uu___485_16288.lax);
                 lax_universes = (uu___485_16288.lax_universes);
                 phase1 = (uu___485_16288.phase1);
                 failhard = (uu___485_16288.failhard);
                 nosynth = (uu___485_16288.nosynth);
                 uvar_subtyping = (uu___485_16288.uvar_subtyping);
                 tc_term = (uu___485_16288.tc_term);
                 type_of = (uu___485_16288.type_of);
                 universe_of = (uu___485_16288.universe_of);
                 check_type_of = (uu___485_16288.check_type_of);
                 use_bv_sorts = (uu___485_16288.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___485_16288.normalized_eff_names);
                 fv_delta_depths = (uu___485_16288.fv_delta_depths);
                 proof_ns = (uu___485_16288.proof_ns);
                 synth_hook = (uu___485_16288.synth_hook);
                 try_solve_implicits_hook =
                   (uu___485_16288.try_solve_implicits_hook);
                 splice = (uu___485_16288.splice);
                 mpreprocess = (uu___485_16288.mpreprocess);
                 postprocess = (uu___485_16288.postprocess);
                 identifier_info = (uu___485_16288.identifier_info);
                 tc_hooks = (uu___485_16288.tc_hooks);
                 dsenv = (uu___485_16288.dsenv);
                 nbe = (uu___485_16288.nbe);
                 strict_args_tab = (uu___485_16288.strict_args_tab);
                 erasable_types_tab = (uu___485_16288.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16305,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16320 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16320 next);
              (let uu___494_16323 = env1  in
               {
                 solver = (uu___494_16323.solver);
                 range = (uu___494_16323.range);
                 curmodule = (uu___494_16323.curmodule);
                 gamma = (uu___494_16323.gamma);
                 gamma_sig = (uu___494_16323.gamma_sig);
                 gamma_cache = (uu___494_16323.gamma_cache);
                 modules = (uu___494_16323.modules);
                 expected_typ = (uu___494_16323.expected_typ);
                 sigtab = (uu___494_16323.sigtab);
                 attrtab = (uu___494_16323.attrtab);
                 instantiate_imp = (uu___494_16323.instantiate_imp);
                 effects = (uu___494_16323.effects);
                 generalize = (uu___494_16323.generalize);
                 letrecs = (uu___494_16323.letrecs);
                 top_level = (uu___494_16323.top_level);
                 check_uvars = (uu___494_16323.check_uvars);
                 use_eq = (uu___494_16323.use_eq);
                 use_eq_strict = (uu___494_16323.use_eq_strict);
                 is_iface = (uu___494_16323.is_iface);
                 admit = (uu___494_16323.admit);
                 lax = (uu___494_16323.lax);
                 lax_universes = (uu___494_16323.lax_universes);
                 phase1 = (uu___494_16323.phase1);
                 failhard = (uu___494_16323.failhard);
                 nosynth = (uu___494_16323.nosynth);
                 uvar_subtyping = (uu___494_16323.uvar_subtyping);
                 tc_term = (uu___494_16323.tc_term);
                 type_of = (uu___494_16323.type_of);
                 universe_of = (uu___494_16323.universe_of);
                 check_type_of = (uu___494_16323.check_type_of);
                 use_bv_sorts = (uu___494_16323.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___494_16323.normalized_eff_names);
                 fv_delta_depths = (uu___494_16323.fv_delta_depths);
                 proof_ns = (uu___494_16323.proof_ns);
                 synth_hook = (uu___494_16323.synth_hook);
                 try_solve_implicits_hook =
                   (uu___494_16323.try_solve_implicits_hook);
                 splice = (uu___494_16323.splice);
                 mpreprocess = (uu___494_16323.mpreprocess);
                 postprocess = (uu___494_16323.postprocess);
                 identifier_info = (uu___494_16323.identifier_info);
                 tc_hooks = (uu___494_16323.tc_hooks);
                 dsenv = (uu___494_16323.dsenv);
                 nbe = (uu___494_16323.nbe);
                 strict_args_tab = (uu___494_16323.strict_args_tab);
                 erasable_types_tab = (uu___494_16323.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16352 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16352 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___501_16368 = e  in
         {
           solver = (uu___501_16368.solver);
           range = r;
           curmodule = (uu___501_16368.curmodule);
           gamma = (uu___501_16368.gamma);
           gamma_sig = (uu___501_16368.gamma_sig);
           gamma_cache = (uu___501_16368.gamma_cache);
           modules = (uu___501_16368.modules);
           expected_typ = (uu___501_16368.expected_typ);
           sigtab = (uu___501_16368.sigtab);
           attrtab = (uu___501_16368.attrtab);
           instantiate_imp = (uu___501_16368.instantiate_imp);
           effects = (uu___501_16368.effects);
           generalize = (uu___501_16368.generalize);
           letrecs = (uu___501_16368.letrecs);
           top_level = (uu___501_16368.top_level);
           check_uvars = (uu___501_16368.check_uvars);
           use_eq = (uu___501_16368.use_eq);
           use_eq_strict = (uu___501_16368.use_eq_strict);
           is_iface = (uu___501_16368.is_iface);
           admit = (uu___501_16368.admit);
           lax = (uu___501_16368.lax);
           lax_universes = (uu___501_16368.lax_universes);
           phase1 = (uu___501_16368.phase1);
           failhard = (uu___501_16368.failhard);
           nosynth = (uu___501_16368.nosynth);
           uvar_subtyping = (uu___501_16368.uvar_subtyping);
           tc_term = (uu___501_16368.tc_term);
           type_of = (uu___501_16368.type_of);
           universe_of = (uu___501_16368.universe_of);
           check_type_of = (uu___501_16368.check_type_of);
           use_bv_sorts = (uu___501_16368.use_bv_sorts);
           qtbl_name_and_index = (uu___501_16368.qtbl_name_and_index);
           normalized_eff_names = (uu___501_16368.normalized_eff_names);
           fv_delta_depths = (uu___501_16368.fv_delta_depths);
           proof_ns = (uu___501_16368.proof_ns);
           synth_hook = (uu___501_16368.synth_hook);
           try_solve_implicits_hook =
             (uu___501_16368.try_solve_implicits_hook);
           splice = (uu___501_16368.splice);
           mpreprocess = (uu___501_16368.mpreprocess);
           postprocess = (uu___501_16368.postprocess);
           identifier_info = (uu___501_16368.identifier_info);
           tc_hooks = (uu___501_16368.tc_hooks);
           dsenv = (uu___501_16368.dsenv);
           nbe = (uu___501_16368.nbe);
           strict_args_tab = (uu___501_16368.strict_args_tab);
           erasable_types_tab = (uu___501_16368.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16388 =
        let uu____16389 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16389 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16388
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16444 =
          let uu____16445 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16445 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16444
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16500 =
          let uu____16501 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16501 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16500
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16556 =
        let uu____16557 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16557 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16556
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___518_16621 = env1  in
      {
        solver = (uu___518_16621.solver);
        range = (uu___518_16621.range);
        curmodule = lid;
        gamma = (uu___518_16621.gamma);
        gamma_sig = (uu___518_16621.gamma_sig);
        gamma_cache = (uu___518_16621.gamma_cache);
        modules = (uu___518_16621.modules);
        expected_typ = (uu___518_16621.expected_typ);
        sigtab = (uu___518_16621.sigtab);
        attrtab = (uu___518_16621.attrtab);
        instantiate_imp = (uu___518_16621.instantiate_imp);
        effects = (uu___518_16621.effects);
        generalize = (uu___518_16621.generalize);
        letrecs = (uu___518_16621.letrecs);
        top_level = (uu___518_16621.top_level);
        check_uvars = (uu___518_16621.check_uvars);
        use_eq = (uu___518_16621.use_eq);
        use_eq_strict = (uu___518_16621.use_eq_strict);
        is_iface = (uu___518_16621.is_iface);
        admit = (uu___518_16621.admit);
        lax = (uu___518_16621.lax);
        lax_universes = (uu___518_16621.lax_universes);
        phase1 = (uu___518_16621.phase1);
        failhard = (uu___518_16621.failhard);
        nosynth = (uu___518_16621.nosynth);
        uvar_subtyping = (uu___518_16621.uvar_subtyping);
        tc_term = (uu___518_16621.tc_term);
        type_of = (uu___518_16621.type_of);
        universe_of = (uu___518_16621.universe_of);
        check_type_of = (uu___518_16621.check_type_of);
        use_bv_sorts = (uu___518_16621.use_bv_sorts);
        qtbl_name_and_index = (uu___518_16621.qtbl_name_and_index);
        normalized_eff_names = (uu___518_16621.normalized_eff_names);
        fv_delta_depths = (uu___518_16621.fv_delta_depths);
        proof_ns = (uu___518_16621.proof_ns);
        synth_hook = (uu___518_16621.synth_hook);
        try_solve_implicits_hook = (uu___518_16621.try_solve_implicits_hook);
        splice = (uu___518_16621.splice);
        mpreprocess = (uu___518_16621.mpreprocess);
        postprocess = (uu___518_16621.postprocess);
        identifier_info = (uu___518_16621.identifier_info);
        tc_hooks = (uu___518_16621.tc_hooks);
        dsenv = (uu___518_16621.dsenv);
        nbe = (uu___518_16621.nbe);
        strict_args_tab = (uu___518_16621.strict_args_tab);
        erasable_types_tab = (uu___518_16621.erasable_types_tab)
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
      let uu____16652 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16652
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16665 =
      let uu____16667 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____16667  in
    (FStar_Errors.Fatal_NameNotFound, uu____16665)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16682 =
      let uu____16684 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16684  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16682)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16693  ->
    let uu____16694 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
    FStar_Syntax_Syntax.U_unif uu____16694
  
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
      | ((formals,t),uu____16796) ->
          let vs = mk_univ_subst formals us  in
          let uu____16820 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16820)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16837  ->
    match uu___1_16837 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16863  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16883 = inst_tscheme t  in
      match uu____16883 with
      | (us,t1) ->
          let uu____16894 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16894)
  
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
          let uu____16919 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16921 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16919 uu____16921
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
        fun uu____16948  ->
          match uu____16948 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16962 =
                    let uu____16964 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16968 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16972 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16974 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16964 uu____16968 uu____16972 uu____16974
                     in
                  failwith uu____16962)
               else ();
               (let uu____16979 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16979))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16997 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____17008 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____17019 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____17033 =
        let uu____17035 = FStar_Ident.nsstr l  in
        let uu____17037 = FStar_Ident.string_of_lid cur  in
        uu____17035 = uu____17037  in
      if uu____17033
      then Yes
      else
        (let uu____17043 =
           let uu____17045 = FStar_Ident.nsstr l  in
           let uu____17047 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____17045 uu____17047  in
         if uu____17043
         then
           let lns =
             let uu____17053 = FStar_Ident.ns_of_lid l  in
             let uu____17056 =
               let uu____17059 = FStar_Ident.ident_of_lid l  in [uu____17059]
                in
             FStar_List.append uu____17053 uu____17056  in
           let cur1 =
             let uu____17063 = FStar_Ident.ns_of_lid cur  in
             let uu____17066 =
               let uu____17069 = FStar_Ident.ident_of_lid cur  in
               [uu____17069]  in
             FStar_List.append uu____17063 uu____17066  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____17093) -> Maybe
             | (uu____17100,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____17119 = FStar_Ident.text_of_id hd  in
                 let uu____17121 = FStar_Ident.text_of_id hd'  in
                 uu____17119 = uu____17121 -> aux tl tl'
             | uu____17124 -> No  in
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
        (let uu____17176 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17176 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17220 =
            let uu____17223 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17223  in
          match uu____17220 with
          | FStar_Pervasives_Native.None  ->
              let uu____17245 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17289  ->
                     match uu___2_17289 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17328 = FStar_Ident.lid_equals lid l  in
                         if uu____17328
                         then
                           let uu____17351 =
                             let uu____17370 =
                               let uu____17385 = inst_tscheme t  in
                               FStar_Util.Inl uu____17385  in
                             let uu____17400 = FStar_Ident.range_of_lid l  in
                             (uu____17370, uu____17400)  in
                           FStar_Pervasives_Native.Some uu____17351
                         else FStar_Pervasives_Native.None
                     | uu____17453 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17245
                (fun uu____17491  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17501  ->
                        match uu___3_17501 with
                        | (uu____17504,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17506);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17507;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17508;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17509;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17510;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17511;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17533 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17533
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
                                  uu____17585 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17592 -> cache t  in
                            let uu____17593 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17593 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17599 =
                                   let uu____17600 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17600)
                                    in
                                 maybe_cache uu____17599)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17671 = find_in_sigtab env1 lid  in
         match uu____17671 with
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
      let uu____17752 = lookup_qname env1 lid  in
      match uu____17752 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17773,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17887 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17887 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17932 =
          let uu____17935 = lookup_attr env2 attr  in se1 :: uu____17935  in
        FStar_Util.smap_add (attrtab env2) attr uu____17932  in
      FStar_List.iter
        (fun attr  ->
           let uu____17945 =
             let uu____17946 = FStar_Syntax_Subst.compress attr  in
             uu____17946.FStar_Syntax_Syntax.n  in
           match uu____17945 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17950 =
                 let uu____17952 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17952  in
               add_one env1 se uu____17950
           | uu____17953 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17976) ->
          add_sigelts env1 ses
      | uu____17985 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17993 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17993 se) lids;
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
        (fun uu___4_18027  ->
           match uu___4_18027 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____18037 =
                 let uu____18044 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____18044)  in
               FStar_Pervasives_Native.Some uu____18037
           | uu____18053 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____18115,lb::[]),uu____18117) ->
            let uu____18126 =
              let uu____18135 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____18144 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____18135, uu____18144)  in
            FStar_Pervasives_Native.Some uu____18126
        | FStar_Syntax_Syntax.Sig_let ((uu____18157,lbs),uu____18159) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18191 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18204 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18204
                     then
                       let uu____18217 =
                         let uu____18226 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18235 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18226, uu____18235)  in
                       FStar_Pervasives_Native.Some uu____18217
                     else FStar_Pervasives_Native.None)
        | uu____18258 -> FStar_Pervasives_Native.None
  
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
                    let uu____18350 =
                      let uu____18352 =
                        let uu____18354 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18356 =
                          let uu____18358 =
                            let uu____18360 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18366 =
                              let uu____18368 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18368  in
                            Prims.op_Hat uu____18360 uu____18366  in
                          Prims.op_Hat ", expected " uu____18358  in
                        Prims.op_Hat uu____18354 uu____18356  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18352
                       in
                    failwith uu____18350
                  else ());
             (let uu____18375 =
                let uu____18384 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18384, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18375))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18404,uu____18405) ->
            let uu____18410 =
              let uu____18419 =
                let uu____18424 =
                  let uu____18425 =
                    let uu____18428 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18428  in
                  (us, uu____18425)  in
                inst_ts us_opt uu____18424  in
              (uu____18419, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18410
        | uu____18447 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18536 =
          match uu____18536 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18632,uvs,t,uu____18635,uu____18636,uu____18637);
                      FStar_Syntax_Syntax.sigrng = uu____18638;
                      FStar_Syntax_Syntax.sigquals = uu____18639;
                      FStar_Syntax_Syntax.sigmeta = uu____18640;
                      FStar_Syntax_Syntax.sigattrs = uu____18641;
                      FStar_Syntax_Syntax.sigopts = uu____18642;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18667 =
                     let uu____18676 = inst_tscheme1 (uvs, t)  in
                     (uu____18676, rng)  in
                   FStar_Pervasives_Native.Some uu____18667
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18700;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18702;
                      FStar_Syntax_Syntax.sigattrs = uu____18703;
                      FStar_Syntax_Syntax.sigopts = uu____18704;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18723 =
                     let uu____18725 = in_cur_mod env1 l  in
                     uu____18725 = Yes  in
                   if uu____18723
                   then
                     let uu____18737 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18737
                      then
                        let uu____18753 =
                          let uu____18762 = inst_tscheme1 (uvs, t)  in
                          (uu____18762, rng)  in
                        FStar_Pervasives_Native.Some uu____18753
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18795 =
                        let uu____18804 = inst_tscheme1 (uvs, t)  in
                        (uu____18804, rng)  in
                      FStar_Pervasives_Native.Some uu____18795)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18829,uu____18830);
                      FStar_Syntax_Syntax.sigrng = uu____18831;
                      FStar_Syntax_Syntax.sigquals = uu____18832;
                      FStar_Syntax_Syntax.sigmeta = uu____18833;
                      FStar_Syntax_Syntax.sigattrs = uu____18834;
                      FStar_Syntax_Syntax.sigopts = uu____18835;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18878 =
                          let uu____18887 = inst_tscheme1 (uvs, k)  in
                          (uu____18887, rng)  in
                        FStar_Pervasives_Native.Some uu____18878
                    | uu____18908 ->
                        let uu____18909 =
                          let uu____18918 =
                            let uu____18923 =
                              let uu____18924 =
                                let uu____18927 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18927
                                 in
                              (uvs, uu____18924)  in
                            inst_tscheme1 uu____18923  in
                          (uu____18918, rng)  in
                        FStar_Pervasives_Native.Some uu____18909)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18950,uu____18951);
                      FStar_Syntax_Syntax.sigrng = uu____18952;
                      FStar_Syntax_Syntax.sigquals = uu____18953;
                      FStar_Syntax_Syntax.sigmeta = uu____18954;
                      FStar_Syntax_Syntax.sigattrs = uu____18955;
                      FStar_Syntax_Syntax.sigopts = uu____18956;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____19000 =
                          let uu____19009 = inst_tscheme_with (uvs, k) us  in
                          (uu____19009, rng)  in
                        FStar_Pervasives_Native.Some uu____19000
                    | uu____19030 ->
                        let uu____19031 =
                          let uu____19040 =
                            let uu____19045 =
                              let uu____19046 =
                                let uu____19049 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____19049
                                 in
                              (uvs, uu____19046)  in
                            inst_tscheme_with uu____19045 us  in
                          (uu____19040, rng)  in
                        FStar_Pervasives_Native.Some uu____19031)
               | FStar_Util.Inr se ->
                   let uu____19085 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____19106;
                          FStar_Syntax_Syntax.sigrng = uu____19107;
                          FStar_Syntax_Syntax.sigquals = uu____19108;
                          FStar_Syntax_Syntax.sigmeta = uu____19109;
                          FStar_Syntax_Syntax.sigattrs = uu____19110;
                          FStar_Syntax_Syntax.sigopts = uu____19111;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____19128 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____19085
                     (FStar_Util.map_option
                        (fun uu____19176  ->
                           match uu____19176 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19207 =
          let uu____19218 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19218 mapper  in
        match uu____19207 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19292 =
              let uu____19303 =
                let uu____19310 =
                  let uu___855_19313 = t  in
                  let uu____19314 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_19313.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19314;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_19313.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19310)  in
              (uu____19303, r)  in
            FStar_Pervasives_Native.Some uu____19292
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19363 = lookup_qname env1 l  in
      match uu____19363 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19384 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19438 = try_lookup_bv env1 bv  in
      match uu____19438 with
      | FStar_Pervasives_Native.None  ->
          let uu____19453 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19453 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19469 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19470 =
            let uu____19471 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19471  in
          (uu____19469, uu____19470)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19493 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19493 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19559 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19559  in
          let uu____19560 =
            let uu____19569 =
              let uu____19574 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19574)  in
            (uu____19569, r1)  in
          FStar_Pervasives_Native.Some uu____19560
  
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
        let uu____19609 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19609 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19642,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19667 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19667  in
            let uu____19668 =
              let uu____19673 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19673, r1)  in
            FStar_Pervasives_Native.Some uu____19668
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19697 = try_lookup_lid env1 l  in
      match uu____19697 with
      | FStar_Pervasives_Native.None  ->
          let uu____19724 = name_not_found l  in
          let uu____19730 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19724 uu____19730
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19775  ->
              match uu___5_19775 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19778 = FStar_Ident.text_of_id x  in
                  let uu____19780 = FStar_Ident.text_of_id y  in
                  uu____19778 = uu____19780
              | uu____19783 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19804 = lookup_qname env1 lid  in
      match uu____19804 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19813,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19816;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19818;
              FStar_Syntax_Syntax.sigattrs = uu____19819;
              FStar_Syntax_Syntax.sigopts = uu____19820;_},FStar_Pervasives_Native.None
            ),uu____19821)
          ->
          let uu____19872 =
            let uu____19879 =
              let uu____19880 =
                let uu____19883 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19883 t  in
              (uvs, uu____19880)  in
            (uu____19879, q)  in
          FStar_Pervasives_Native.Some uu____19872
      | uu____19896 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19918 = lookup_qname env1 lid  in
      match uu____19918 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19923,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19926;
              FStar_Syntax_Syntax.sigquals = uu____19927;
              FStar_Syntax_Syntax.sigmeta = uu____19928;
              FStar_Syntax_Syntax.sigattrs = uu____19929;
              FStar_Syntax_Syntax.sigopts = uu____19930;_},FStar_Pervasives_Native.None
            ),uu____19931)
          ->
          let uu____19982 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19982 (uvs, t)
      | uu____19987 ->
          let uu____19988 = name_not_found lid  in
          let uu____19994 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19988 uu____19994
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____20014 = lookup_qname env1 lid  in
      match uu____20014 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20019,uvs,t,uu____20022,uu____20023,uu____20024);
              FStar_Syntax_Syntax.sigrng = uu____20025;
              FStar_Syntax_Syntax.sigquals = uu____20026;
              FStar_Syntax_Syntax.sigmeta = uu____20027;
              FStar_Syntax_Syntax.sigattrs = uu____20028;
              FStar_Syntax_Syntax.sigopts = uu____20029;_},FStar_Pervasives_Native.None
            ),uu____20030)
          ->
          let uu____20087 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____20087 (uvs, t)
      | uu____20092 ->
          let uu____20093 = name_not_found lid  in
          let uu____20099 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____20093 uu____20099
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____20122 = lookup_qname env1 lid  in
      match uu____20122 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20130,uu____20131,uu____20132,uu____20133,uu____20134,dcs);
              FStar_Syntax_Syntax.sigrng = uu____20136;
              FStar_Syntax_Syntax.sigquals = uu____20137;
              FStar_Syntax_Syntax.sigmeta = uu____20138;
              FStar_Syntax_Syntax.sigattrs = uu____20139;
              FStar_Syntax_Syntax.sigopts = uu____20140;_},uu____20141),uu____20142)
          -> (true, dcs)
      | uu____20207 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20223 = lookup_qname env1 lid  in
      match uu____20223 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20224,uu____20225,uu____20226,l,uu____20228,uu____20229);
              FStar_Syntax_Syntax.sigrng = uu____20230;
              FStar_Syntax_Syntax.sigquals = uu____20231;
              FStar_Syntax_Syntax.sigmeta = uu____20232;
              FStar_Syntax_Syntax.sigattrs = uu____20233;
              FStar_Syntax_Syntax.sigopts = uu____20234;_},uu____20235),uu____20236)
          -> l
      | uu____20295 ->
          let uu____20296 =
            let uu____20298 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20298  in
          failwith uu____20296
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20368)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20425) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20449 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20449
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20484 -> FStar_Pervasives_Native.None)
          | uu____20493 -> FStar_Pervasives_Native.None
  
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
        let uu____20555 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20555
  
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
        let uu____20588 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20588
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20612 =
        let uu____20614 = FStar_Ident.nsstr lid  in uu____20614 = "Prims"  in
      if uu____20612
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20644,uu____20645) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20694),uu____20695) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20744 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20762 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20772 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20789 ->
                  let uu____20796 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20796
              | FStar_Syntax_Syntax.Sig_let ((uu____20797,lbs),uu____20799)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20815 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20815
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20822 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20838 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____20848 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20855 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20856 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20857 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20870 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20871 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20894 =
        let uu____20896 = FStar_Ident.nsstr lid  in uu____20896 = "Prims"  in
      if uu____20894
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20903 =
           let uu____20906 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20906
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20903
           (fun d_opt  ->
              let uu____20918 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20918
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20928 =
                   let uu____20931 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20931  in
                 match uu____20928 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20932 =
                       let uu____20934 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20934
                        in
                     failwith uu____20932
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20939 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20939
                       then
                         let uu____20942 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20944 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20946 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20942 uu____20944 uu____20946
                       else ());
                      (let uu____20952 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20952 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20973),uu____20974) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____21023 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____21045),uu____21046) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____21095 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____21117 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____21117
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21150 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____21150 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21172 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21181 =
                        let uu____21182 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21182.FStar_Syntax_Syntax.n  in
                      match uu____21181 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21187 -> false))
               in
            (true, uu____21172)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21210 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21210
  
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
          let uu____21282 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21282  in
        let uu____21283 = FStar_Util.smap_try_find tab s  in
        match uu____21283 with
        | FStar_Pervasives_Native.None  ->
            let uu____21286 = f ()  in
            (match uu____21286 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21324 =
        let uu____21325 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21325 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21359 =
        let uu____21360 = FStar_Syntax_Util.unrefine t  in
        uu____21360.FStar_Syntax_Syntax.n  in
      match uu____21359 with
      | FStar_Syntax_Syntax.Tm_type uu____21364 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21368) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21394) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21399,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21421 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21454 =
        let attrs =
          let uu____21460 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21460  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21500 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21500)
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
      let uu____21545 = lookup_qname env1 ftv  in
      match uu____21545 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21549) ->
          let uu____21594 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21594 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21615,t),r) ->
               let uu____21630 =
                 let uu____21631 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21631 t  in
               FStar_Pervasives_Native.Some uu____21630)
      | uu____21632 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21644 = try_lookup_effect_lid env1 ftv  in
      match uu____21644 with
      | FStar_Pervasives_Native.None  ->
          let uu____21647 = name_not_found ftv  in
          let uu____21653 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21647 uu____21653
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
        let uu____21677 = lookup_qname env1 lid0  in
        match uu____21677 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21688);
                FStar_Syntax_Syntax.sigrng = uu____21689;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21691;
                FStar_Syntax_Syntax.sigattrs = uu____21692;
                FStar_Syntax_Syntax.sigopts = uu____21693;_},FStar_Pervasives_Native.None
              ),uu____21694)
            ->
            let lid1 =
              let uu____21750 =
                let uu____21751 = FStar_Ident.range_of_lid lid  in
                let uu____21752 =
                  let uu____21753 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21753  in
                FStar_Range.set_use_range uu____21751 uu____21752  in
              FStar_Ident.set_lid_range lid uu____21750  in
            let uu____21754 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21760  ->
                      match uu___6_21760 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21763 -> false))
               in
            if uu____21754
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21782 =
                      let uu____21784 =
                        let uu____21786 = get_range env1  in
                        FStar_Range.string_of_range uu____21786  in
                      let uu____21787 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21789 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21784 uu____21787 uu____21789
                       in
                    failwith uu____21782)
                  in
               match (binders, univs) with
               | ([],uu____21810) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21836,uu____21837::uu____21838::uu____21839) ->
                   let uu____21860 =
                     let uu____21862 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21864 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21862 uu____21864
                      in
                   failwith uu____21860
               | uu____21875 ->
                   let uu____21890 =
                     let uu____21895 =
                       let uu____21896 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21896)  in
                     inst_tscheme_with uu____21895 insts  in
                   (match uu____21890 with
                    | (uu____21909,t) ->
                        let t1 =
                          let uu____21912 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21912 t  in
                        let uu____21913 =
                          let uu____21914 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21914.FStar_Syntax_Syntax.n  in
                        (match uu____21913 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21949 -> failwith "Impossible")))
        | uu____21957 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21981 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21981 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21994,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____22001 = find l2  in
            (match uu____22001 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____22008 =
          let uu____22011 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____22011  in
        match uu____22008 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____22014 = find l  in
            (match uu____22014 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____22019 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____22019
                     m);
                  m))
         in
      let uu____22021 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____22021
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____22042 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____22042 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____22048) ->
            FStar_List.length bs
        | uu____22087 ->
            let uu____22088 =
              let uu____22094 =
                let uu____22096 = FStar_Ident.string_of_lid name  in
                let uu____22098 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____22096 uu____22098
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____22094)
               in
            FStar_Errors.raise_error uu____22088 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____22117 = lookup_qname env1 l1  in
      match uu____22117 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____22120;
              FStar_Syntax_Syntax.sigrng = uu____22121;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____22123;
              FStar_Syntax_Syntax.sigattrs = uu____22124;
              FStar_Syntax_Syntax.sigopts = uu____22125;_},uu____22126),uu____22127)
          -> q
      | uu____22180 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22204 =
          let uu____22205 =
            let uu____22207 = FStar_Util.string_of_int i  in
            let uu____22209 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22207 uu____22209
             in
          failwith uu____22205  in
        let uu____22212 = lookup_datacon env1 lid  in
        match uu____22212 with
        | (uu____22217,t) ->
            let uu____22219 =
              let uu____22220 = FStar_Syntax_Subst.compress t  in
              uu____22220.FStar_Syntax_Syntax.n  in
            (match uu____22219 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22224) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22270 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22284 = lookup_qname env1 l  in
      match uu____22284 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22286,uu____22287,uu____22288);
              FStar_Syntax_Syntax.sigrng = uu____22289;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22291;
              FStar_Syntax_Syntax.sigattrs = uu____22292;
              FStar_Syntax_Syntax.sigopts = uu____22293;_},uu____22294),uu____22295)
          ->
          FStar_Util.for_some
            (fun uu___7_22350  ->
               match uu___7_22350 with
               | FStar_Syntax_Syntax.Projector uu____22352 -> true
               | uu____22358 -> false) quals
      | uu____22360 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22374 = lookup_qname env1 lid  in
      match uu____22374 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22376,uu____22377,uu____22378,uu____22379,uu____22380,uu____22381);
              FStar_Syntax_Syntax.sigrng = uu____22382;
              FStar_Syntax_Syntax.sigquals = uu____22383;
              FStar_Syntax_Syntax.sigmeta = uu____22384;
              FStar_Syntax_Syntax.sigattrs = uu____22385;
              FStar_Syntax_Syntax.sigopts = uu____22386;_},uu____22387),uu____22388)
          -> true
      | uu____22448 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22462 = lookup_qname env1 lid  in
      match uu____22462 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22464,uu____22465,uu____22466,uu____22467,uu____22468,uu____22469);
              FStar_Syntax_Syntax.sigrng = uu____22470;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22472;
              FStar_Syntax_Syntax.sigattrs = uu____22473;
              FStar_Syntax_Syntax.sigopts = uu____22474;_},uu____22475),uu____22476)
          ->
          FStar_Util.for_some
            (fun uu___8_22539  ->
               match uu___8_22539 with
               | FStar_Syntax_Syntax.RecordType uu____22541 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22551 -> true
               | uu____22561 -> false) quals
      | uu____22563 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22573,uu____22574);
            FStar_Syntax_Syntax.sigrng = uu____22575;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22577;
            FStar_Syntax_Syntax.sigattrs = uu____22578;
            FStar_Syntax_Syntax.sigopts = uu____22579;_},uu____22580),uu____22581)
        ->
        FStar_Util.for_some
          (fun uu___9_22640  ->
             match uu___9_22640 with
             | FStar_Syntax_Syntax.Action uu____22642 -> true
             | uu____22644 -> false) quals
    | uu____22646 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22660 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22660
  
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
      let uu____22677 =
        let uu____22678 = FStar_Syntax_Util.un_uinst head  in
        uu____22678.FStar_Syntax_Syntax.n  in
      match uu____22677 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22684 ->
               true
           | uu____22687 -> false)
      | uu____22689 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22703 = lookup_qname env1 l  in
      match uu____22703 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22706),uu____22707) ->
          FStar_Util.for_some
            (fun uu___10_22755  ->
               match uu___10_22755 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22758 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22760 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22836 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22854) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22872 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22880 ->
                 FStar_Pervasives_Native.Some true
             | uu____22899 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22902 =
        let uu____22906 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22906 mapper  in
      match uu____22902 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22966 = lookup_qname env1 lid  in
      match uu____22966 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22970,uu____22971,tps,uu____22973,uu____22974,uu____22975);
              FStar_Syntax_Syntax.sigrng = uu____22976;
              FStar_Syntax_Syntax.sigquals = uu____22977;
              FStar_Syntax_Syntax.sigmeta = uu____22978;
              FStar_Syntax_Syntax.sigattrs = uu____22979;
              FStar_Syntax_Syntax.sigopts = uu____22980;_},uu____22981),uu____22982)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____23050 -> FStar_Pervasives_Native.None
  
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
           (fun uu____23096  ->
              match uu____23096 with
              | (d,uu____23105) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____23121 = effect_decl_opt env1 l  in
      match uu____23121 with
      | FStar_Pervasives_Native.None  ->
          let uu____23136 = name_not_found l  in
          let uu____23142 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____23136 uu____23142
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23170 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23170 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23177  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23191  ->
            fun uu____23192  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23226 = FStar_Ident.lid_equals l1 l2  in
        if uu____23226
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23245 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23245
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23264 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23317  ->
                        match uu____23317 with
                        | (m1,m2,uu____23331,uu____23332,uu____23333) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23264 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23358,uu____23359,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23407 = join_opt env1 l1 l2  in
        match uu____23407 with
        | FStar_Pervasives_Native.None  ->
            let uu____23428 =
              let uu____23434 =
                let uu____23436 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23438 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23436 uu____23438
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23434)  in
            FStar_Errors.raise_error uu____23428 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23481 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23481
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
  'uuuuuu23501 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23501) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23530 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23556  ->
                match uu____23556 with
                | (d,uu____23563) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23530 with
      | FStar_Pervasives_Native.None  ->
          let uu____23574 =
            let uu____23576 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23576
             in
          failwith uu____23574
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23591 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23591 with
           | (uu____23602,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23620)::(wp,uu____23622)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23678 -> failwith "Impossible"))
  
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
        | uu____23743 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23756 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23756 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23773 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23773 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23798 =
                     let uu____23804 =
                       let uu____23806 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23814 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23825 =
                         let uu____23827 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23827  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23806 uu____23814 uu____23825
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23804)
                      in
                   FStar_Errors.raise_error uu____23798
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23835 =
                     let uu____23846 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23846 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23883  ->
                        fun uu____23884  ->
                          match (uu____23883, uu____23884) with
                          | ((x,uu____23914),(t,uu____23916)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23835
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23947 =
                     let uu___1609_23948 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1609_23948.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1609_23948.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1609_23948.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1609_23948.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23947
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23960 .
    'uuuuuu23960 ->
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
            let uu____24001 =
              let uu____24008 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____24008)  in
            match uu____24001 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____24032 = FStar_Ident.string_of_lid eff_name  in
                     let uu____24034 = FStar_Util.string_of_int given  in
                     let uu____24036 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____24032 uu____24034 uu____24036
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____24041 = effect_decl_opt env1 effect_name  in
          match uu____24041 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____24063) ->
              let uu____24074 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____24074 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____24092 =
                       let uu____24095 = get_range env1  in
                       let uu____24096 =
                         let uu____24103 =
                           let uu____24104 =
                             let uu____24121 =
                               let uu____24132 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____24132 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____24121)  in
                           FStar_Syntax_Syntax.Tm_app uu____24104  in
                         FStar_Syntax_Syntax.mk uu____24103  in
                       uu____24096 FStar_Pervasives_Native.None uu____24095
                        in
                     FStar_Pervasives_Native.Some uu____24092)))
  
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
           (fun uu___11_24232  ->
              match uu___11_24232 with
              | FStar_Syntax_Syntax.Reflectable uu____24234 -> true
              | uu____24236 -> false))
  
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
      | uu____24296 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24311 =
        let uu____24312 = FStar_Syntax_Subst.compress t  in
        uu____24312.FStar_Syntax_Syntax.n  in
      match uu____24311 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24316,c) ->
          is_reifiable_comp env1 c
      | uu____24338 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24358 =
           let uu____24360 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24360  in
         if uu____24358
         then
           let uu____24363 =
             let uu____24369 =
               let uu____24371 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24371
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24369)  in
           let uu____24375 = get_range env1  in
           FStar_Errors.raise_error uu____24363 uu____24375
         else ());
        (let uu____24378 = effect_repr_aux true env1 c u_c  in
         match uu____24378 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1686_24414 = env1  in
        {
          solver = (uu___1686_24414.solver);
          range = (uu___1686_24414.range);
          curmodule = (uu___1686_24414.curmodule);
          gamma = (uu___1686_24414.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1686_24414.gamma_cache);
          modules = (uu___1686_24414.modules);
          expected_typ = (uu___1686_24414.expected_typ);
          sigtab = (uu___1686_24414.sigtab);
          attrtab = (uu___1686_24414.attrtab);
          instantiate_imp = (uu___1686_24414.instantiate_imp);
          effects = (uu___1686_24414.effects);
          generalize = (uu___1686_24414.generalize);
          letrecs = (uu___1686_24414.letrecs);
          top_level = (uu___1686_24414.top_level);
          check_uvars = (uu___1686_24414.check_uvars);
          use_eq = (uu___1686_24414.use_eq);
          use_eq_strict = (uu___1686_24414.use_eq_strict);
          is_iface = (uu___1686_24414.is_iface);
          admit = (uu___1686_24414.admit);
          lax = (uu___1686_24414.lax);
          lax_universes = (uu___1686_24414.lax_universes);
          phase1 = (uu___1686_24414.phase1);
          failhard = (uu___1686_24414.failhard);
          nosynth = (uu___1686_24414.nosynth);
          uvar_subtyping = (uu___1686_24414.uvar_subtyping);
          tc_term = (uu___1686_24414.tc_term);
          type_of = (uu___1686_24414.type_of);
          universe_of = (uu___1686_24414.universe_of);
          check_type_of = (uu___1686_24414.check_type_of);
          use_bv_sorts = (uu___1686_24414.use_bv_sorts);
          qtbl_name_and_index = (uu___1686_24414.qtbl_name_and_index);
          normalized_eff_names = (uu___1686_24414.normalized_eff_names);
          fv_delta_depths = (uu___1686_24414.fv_delta_depths);
          proof_ns = (uu___1686_24414.proof_ns);
          synth_hook = (uu___1686_24414.synth_hook);
          try_solve_implicits_hook =
            (uu___1686_24414.try_solve_implicits_hook);
          splice = (uu___1686_24414.splice);
          mpreprocess = (uu___1686_24414.mpreprocess);
          postprocess = (uu___1686_24414.postprocess);
          identifier_info = (uu___1686_24414.identifier_info);
          tc_hooks = (uu___1686_24414.tc_hooks);
          dsenv = (uu___1686_24414.dsenv);
          nbe = (uu___1686_24414.nbe);
          strict_args_tab = (uu___1686_24414.strict_args_tab);
          erasable_types_tab = (uu___1686_24414.erasable_types_tab)
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
    fun uu____24433  ->
      match uu____24433 with
      | (ed,quals) ->
          let effects1 =
            let uu___1695_24447 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1695_24447.order);
              joins = (uu___1695_24447.joins);
              polymonadic_binds = (uu___1695_24447.polymonadic_binds)
            }  in
          let uu___1698_24456 = env1  in
          {
            solver = (uu___1698_24456.solver);
            range = (uu___1698_24456.range);
            curmodule = (uu___1698_24456.curmodule);
            gamma = (uu___1698_24456.gamma);
            gamma_sig = (uu___1698_24456.gamma_sig);
            gamma_cache = (uu___1698_24456.gamma_cache);
            modules = (uu___1698_24456.modules);
            expected_typ = (uu___1698_24456.expected_typ);
            sigtab = (uu___1698_24456.sigtab);
            attrtab = (uu___1698_24456.attrtab);
            instantiate_imp = (uu___1698_24456.instantiate_imp);
            effects = effects1;
            generalize = (uu___1698_24456.generalize);
            letrecs = (uu___1698_24456.letrecs);
            top_level = (uu___1698_24456.top_level);
            check_uvars = (uu___1698_24456.check_uvars);
            use_eq = (uu___1698_24456.use_eq);
            use_eq_strict = (uu___1698_24456.use_eq_strict);
            is_iface = (uu___1698_24456.is_iface);
            admit = (uu___1698_24456.admit);
            lax = (uu___1698_24456.lax);
            lax_universes = (uu___1698_24456.lax_universes);
            phase1 = (uu___1698_24456.phase1);
            failhard = (uu___1698_24456.failhard);
            nosynth = (uu___1698_24456.nosynth);
            uvar_subtyping = (uu___1698_24456.uvar_subtyping);
            tc_term = (uu___1698_24456.tc_term);
            type_of = (uu___1698_24456.type_of);
            universe_of = (uu___1698_24456.universe_of);
            check_type_of = (uu___1698_24456.check_type_of);
            use_bv_sorts = (uu___1698_24456.use_bv_sorts);
            qtbl_name_and_index = (uu___1698_24456.qtbl_name_and_index);
            normalized_eff_names = (uu___1698_24456.normalized_eff_names);
            fv_delta_depths = (uu___1698_24456.fv_delta_depths);
            proof_ns = (uu___1698_24456.proof_ns);
            synth_hook = (uu___1698_24456.synth_hook);
            try_solve_implicits_hook =
              (uu___1698_24456.try_solve_implicits_hook);
            splice = (uu___1698_24456.splice);
            mpreprocess = (uu___1698_24456.mpreprocess);
            postprocess = (uu___1698_24456.postprocess);
            identifier_info = (uu___1698_24456.identifier_info);
            tc_hooks = (uu___1698_24456.tc_hooks);
            dsenv = (uu___1698_24456.dsenv);
            nbe = (uu___1698_24456.nbe);
            strict_args_tab = (uu___1698_24456.strict_args_tab);
            erasable_types_tab = (uu___1698_24456.erasable_types_tab)
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
        let uu____24485 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24553  ->
                  match uu____24553 with
                  | (m1,n1,uu____24571,uu____24572) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24485 with
        | FStar_Pervasives_Native.Some (uu____24597,uu____24598,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24643 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24718 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24718
                  (fun uu____24739  ->
                     match uu____24739 with
                     | (c1,g1) ->
                         let uu____24750 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24750
                           (fun uu____24771  ->
                              match uu____24771 with
                              | (c2,g2) ->
                                  let uu____24782 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24782)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24904 = l1 u t e  in
                              l2 u t uu____24904))
                | uu____24905 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24973  ->
                    match uu____24973 with
                    | (e,uu____24981) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____25004 =
            match uu____25004 with
            | (i,j) ->
                let uu____25015 = FStar_Ident.lid_equals i j  in
                if uu____25015
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____25022  ->
                       FStar_Pervasives_Native.Some uu____25022)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____25051 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____25061 = FStar_Ident.lid_equals i k  in
                        if uu____25061
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____25075 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____25075
                                  then []
                                  else
                                    (let uu____25082 =
                                       let uu____25091 =
                                         find_edge order1 (i, k)  in
                                       let uu____25094 =
                                         find_edge order1 (k, j)  in
                                       (uu____25091, uu____25094)  in
                                     match uu____25082 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____25109 =
                                           compose_edges e1 e2  in
                                         [uu____25109]
                                     | uu____25110 -> [])))))
                 in
              FStar_List.append order1 uu____25051  in
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
                  let uu____25140 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____25143 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____25143
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____25140
                  then
                    let uu____25150 =
                      let uu____25156 =
                        let uu____25158 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25158
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25156)
                       in
                    let uu____25162 = get_range env1  in
                    FStar_Errors.raise_error uu____25150 uu____25162
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25240 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25240
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25292 =
                                             let uu____25301 =
                                               find_edge order2 (i, k)  in
                                             let uu____25304 =
                                               find_edge order2 (j, k)  in
                                             (uu____25301, uu____25304)  in
                                           match uu____25292 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25346,uu____25347)
                                                    ->
                                                    let uu____25354 =
                                                      let uu____25361 =
                                                        let uu____25363 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25363
                                                         in
                                                      let uu____25366 =
                                                        let uu____25368 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25368
                                                         in
                                                      (uu____25361,
                                                        uu____25366)
                                                       in
                                                    (match uu____25354 with
                                                     | (true ,true ) ->
                                                         let uu____25385 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25385
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
                                           | uu____25428 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25480 =
                                   let uu____25482 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25482
                                     FStar_Util.is_some
                                    in
                                 if uu____25480
                                 then
                                   let uu____25531 =
                                     let uu____25537 =
                                       let uu____25539 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25541 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25543 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25545 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25539 uu____25541 uu____25543
                                         uu____25545
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25537)
                                      in
                                   FStar_Errors.raise_error uu____25531
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1819_25584 = env1.effects  in
             {
               decls = (uu___1819_25584.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1819_25584.polymonadic_binds)
             }  in
           let uu___1822_25585 = env1  in
           {
             solver = (uu___1822_25585.solver);
             range = (uu___1822_25585.range);
             curmodule = (uu___1822_25585.curmodule);
             gamma = (uu___1822_25585.gamma);
             gamma_sig = (uu___1822_25585.gamma_sig);
             gamma_cache = (uu___1822_25585.gamma_cache);
             modules = (uu___1822_25585.modules);
             expected_typ = (uu___1822_25585.expected_typ);
             sigtab = (uu___1822_25585.sigtab);
             attrtab = (uu___1822_25585.attrtab);
             instantiate_imp = (uu___1822_25585.instantiate_imp);
             effects = effects1;
             generalize = (uu___1822_25585.generalize);
             letrecs = (uu___1822_25585.letrecs);
             top_level = (uu___1822_25585.top_level);
             check_uvars = (uu___1822_25585.check_uvars);
             use_eq = (uu___1822_25585.use_eq);
             use_eq_strict = (uu___1822_25585.use_eq_strict);
             is_iface = (uu___1822_25585.is_iface);
             admit = (uu___1822_25585.admit);
             lax = (uu___1822_25585.lax);
             lax_universes = (uu___1822_25585.lax_universes);
             phase1 = (uu___1822_25585.phase1);
             failhard = (uu___1822_25585.failhard);
             nosynth = (uu___1822_25585.nosynth);
             uvar_subtyping = (uu___1822_25585.uvar_subtyping);
             tc_term = (uu___1822_25585.tc_term);
             type_of = (uu___1822_25585.type_of);
             universe_of = (uu___1822_25585.universe_of);
             check_type_of = (uu___1822_25585.check_type_of);
             use_bv_sorts = (uu___1822_25585.use_bv_sorts);
             qtbl_name_and_index = (uu___1822_25585.qtbl_name_and_index);
             normalized_eff_names = (uu___1822_25585.normalized_eff_names);
             fv_delta_depths = (uu___1822_25585.fv_delta_depths);
             proof_ns = (uu___1822_25585.proof_ns);
             synth_hook = (uu___1822_25585.synth_hook);
             try_solve_implicits_hook =
               (uu___1822_25585.try_solve_implicits_hook);
             splice = (uu___1822_25585.splice);
             mpreprocess = (uu___1822_25585.mpreprocess);
             postprocess = (uu___1822_25585.postprocess);
             identifier_info = (uu___1822_25585.identifier_info);
             tc_hooks = (uu___1822_25585.tc_hooks);
             dsenv = (uu___1822_25585.dsenv);
             nbe = (uu___1822_25585.nbe);
             strict_args_tab = (uu___1822_25585.strict_args_tab);
             erasable_types_tab = (uu___1822_25585.erasable_types_tab)
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
              let uu____25633 = FStar_Ident.string_of_lid m  in
              let uu____25635 = FStar_Ident.string_of_lid n  in
              let uu____25637 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25633 uu____25635 uu____25637
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25646 =
              let uu____25648 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25648 FStar_Util.is_some  in
            if uu____25646
            then
              let uu____25685 =
                let uu____25691 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25691)
                 in
              FStar_Errors.raise_error uu____25685 env1.range
            else
              (let uu____25697 =
                 let uu____25699 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25699 FStar_Util.is_some  in
               if uu____25697
               then
                 let uu____25724 =
                   let uu____25730 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25730)
                    in
                 FStar_Errors.raise_error uu____25724 env1.range
               else
                 (let uu___1837_25736 = env1  in
                  {
                    solver = (uu___1837_25736.solver);
                    range = (uu___1837_25736.range);
                    curmodule = (uu___1837_25736.curmodule);
                    gamma = (uu___1837_25736.gamma);
                    gamma_sig = (uu___1837_25736.gamma_sig);
                    gamma_cache = (uu___1837_25736.gamma_cache);
                    modules = (uu___1837_25736.modules);
                    expected_typ = (uu___1837_25736.expected_typ);
                    sigtab = (uu___1837_25736.sigtab);
                    attrtab = (uu___1837_25736.attrtab);
                    instantiate_imp = (uu___1837_25736.instantiate_imp);
                    effects =
                      (let uu___1839_25738 = env1.effects  in
                       {
                         decls = (uu___1839_25738.decls);
                         order = (uu___1839_25738.order);
                         joins = (uu___1839_25738.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1837_25736.generalize);
                    letrecs = (uu___1837_25736.letrecs);
                    top_level = (uu___1837_25736.top_level);
                    check_uvars = (uu___1837_25736.check_uvars);
                    use_eq = (uu___1837_25736.use_eq);
                    use_eq_strict = (uu___1837_25736.use_eq_strict);
                    is_iface = (uu___1837_25736.is_iface);
                    admit = (uu___1837_25736.admit);
                    lax = (uu___1837_25736.lax);
                    lax_universes = (uu___1837_25736.lax_universes);
                    phase1 = (uu___1837_25736.phase1);
                    failhard = (uu___1837_25736.failhard);
                    nosynth = (uu___1837_25736.nosynth);
                    uvar_subtyping = (uu___1837_25736.uvar_subtyping);
                    tc_term = (uu___1837_25736.tc_term);
                    type_of = (uu___1837_25736.type_of);
                    universe_of = (uu___1837_25736.universe_of);
                    check_type_of = (uu___1837_25736.check_type_of);
                    use_bv_sorts = (uu___1837_25736.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1837_25736.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1837_25736.normalized_eff_names);
                    fv_delta_depths = (uu___1837_25736.fv_delta_depths);
                    proof_ns = (uu___1837_25736.proof_ns);
                    synth_hook = (uu___1837_25736.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1837_25736.try_solve_implicits_hook);
                    splice = (uu___1837_25736.splice);
                    mpreprocess = (uu___1837_25736.mpreprocess);
                    postprocess = (uu___1837_25736.postprocess);
                    identifier_info = (uu___1837_25736.identifier_info);
                    tc_hooks = (uu___1837_25736.tc_hooks);
                    dsenv = (uu___1837_25736.dsenv);
                    nbe = (uu___1837_25736.nbe);
                    strict_args_tab = (uu___1837_25736.strict_args_tab);
                    erasable_types_tab = (uu___1837_25736.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1843_25810 = env1  in
      {
        solver = (uu___1843_25810.solver);
        range = (uu___1843_25810.range);
        curmodule = (uu___1843_25810.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1843_25810.gamma_sig);
        gamma_cache = (uu___1843_25810.gamma_cache);
        modules = (uu___1843_25810.modules);
        expected_typ = (uu___1843_25810.expected_typ);
        sigtab = (uu___1843_25810.sigtab);
        attrtab = (uu___1843_25810.attrtab);
        instantiate_imp = (uu___1843_25810.instantiate_imp);
        effects = (uu___1843_25810.effects);
        generalize = (uu___1843_25810.generalize);
        letrecs = (uu___1843_25810.letrecs);
        top_level = (uu___1843_25810.top_level);
        check_uvars = (uu___1843_25810.check_uvars);
        use_eq = (uu___1843_25810.use_eq);
        use_eq_strict = (uu___1843_25810.use_eq_strict);
        is_iface = (uu___1843_25810.is_iface);
        admit = (uu___1843_25810.admit);
        lax = (uu___1843_25810.lax);
        lax_universes = (uu___1843_25810.lax_universes);
        phase1 = (uu___1843_25810.phase1);
        failhard = (uu___1843_25810.failhard);
        nosynth = (uu___1843_25810.nosynth);
        uvar_subtyping = (uu___1843_25810.uvar_subtyping);
        tc_term = (uu___1843_25810.tc_term);
        type_of = (uu___1843_25810.type_of);
        universe_of = (uu___1843_25810.universe_of);
        check_type_of = (uu___1843_25810.check_type_of);
        use_bv_sorts = (uu___1843_25810.use_bv_sorts);
        qtbl_name_and_index = (uu___1843_25810.qtbl_name_and_index);
        normalized_eff_names = (uu___1843_25810.normalized_eff_names);
        fv_delta_depths = (uu___1843_25810.fv_delta_depths);
        proof_ns = (uu___1843_25810.proof_ns);
        synth_hook = (uu___1843_25810.synth_hook);
        try_solve_implicits_hook = (uu___1843_25810.try_solve_implicits_hook);
        splice = (uu___1843_25810.splice);
        mpreprocess = (uu___1843_25810.mpreprocess);
        postprocess = (uu___1843_25810.postprocess);
        identifier_info = (uu___1843_25810.identifier_info);
        tc_hooks = (uu___1843_25810.tc_hooks);
        dsenv = (uu___1843_25810.dsenv);
        nbe = (uu___1843_25810.nbe);
        strict_args_tab = (uu___1843_25810.strict_args_tab);
        erasable_types_tab = (uu___1843_25810.erasable_types_tab)
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
            (let uu___1856_25868 = env1  in
             {
               solver = (uu___1856_25868.solver);
               range = (uu___1856_25868.range);
               curmodule = (uu___1856_25868.curmodule);
               gamma = rest;
               gamma_sig = (uu___1856_25868.gamma_sig);
               gamma_cache = (uu___1856_25868.gamma_cache);
               modules = (uu___1856_25868.modules);
               expected_typ = (uu___1856_25868.expected_typ);
               sigtab = (uu___1856_25868.sigtab);
               attrtab = (uu___1856_25868.attrtab);
               instantiate_imp = (uu___1856_25868.instantiate_imp);
               effects = (uu___1856_25868.effects);
               generalize = (uu___1856_25868.generalize);
               letrecs = (uu___1856_25868.letrecs);
               top_level = (uu___1856_25868.top_level);
               check_uvars = (uu___1856_25868.check_uvars);
               use_eq = (uu___1856_25868.use_eq);
               use_eq_strict = (uu___1856_25868.use_eq_strict);
               is_iface = (uu___1856_25868.is_iface);
               admit = (uu___1856_25868.admit);
               lax = (uu___1856_25868.lax);
               lax_universes = (uu___1856_25868.lax_universes);
               phase1 = (uu___1856_25868.phase1);
               failhard = (uu___1856_25868.failhard);
               nosynth = (uu___1856_25868.nosynth);
               uvar_subtyping = (uu___1856_25868.uvar_subtyping);
               tc_term = (uu___1856_25868.tc_term);
               type_of = (uu___1856_25868.type_of);
               universe_of = (uu___1856_25868.universe_of);
               check_type_of = (uu___1856_25868.check_type_of);
               use_bv_sorts = (uu___1856_25868.use_bv_sorts);
               qtbl_name_and_index = (uu___1856_25868.qtbl_name_and_index);
               normalized_eff_names = (uu___1856_25868.normalized_eff_names);
               fv_delta_depths = (uu___1856_25868.fv_delta_depths);
               proof_ns = (uu___1856_25868.proof_ns);
               synth_hook = (uu___1856_25868.synth_hook);
               try_solve_implicits_hook =
                 (uu___1856_25868.try_solve_implicits_hook);
               splice = (uu___1856_25868.splice);
               mpreprocess = (uu___1856_25868.mpreprocess);
               postprocess = (uu___1856_25868.postprocess);
               identifier_info = (uu___1856_25868.identifier_info);
               tc_hooks = (uu___1856_25868.tc_hooks);
               dsenv = (uu___1856_25868.dsenv);
               nbe = (uu___1856_25868.nbe);
               strict_args_tab = (uu___1856_25868.strict_args_tab);
               erasable_types_tab = (uu___1856_25868.erasable_types_tab)
             }))
    | uu____25869 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25898  ->
             match uu____25898 with | (x,uu____25906) -> push_bv env2 x) env1
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
            let uu___1870_25941 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1870_25941.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1870_25941.FStar_Syntax_Syntax.index);
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
        let uu____26014 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____26014 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____26042 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____26042)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1891_26058 = env1  in
      {
        solver = (uu___1891_26058.solver);
        range = (uu___1891_26058.range);
        curmodule = (uu___1891_26058.curmodule);
        gamma = (uu___1891_26058.gamma);
        gamma_sig = (uu___1891_26058.gamma_sig);
        gamma_cache = (uu___1891_26058.gamma_cache);
        modules = (uu___1891_26058.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1891_26058.sigtab);
        attrtab = (uu___1891_26058.attrtab);
        instantiate_imp = (uu___1891_26058.instantiate_imp);
        effects = (uu___1891_26058.effects);
        generalize = (uu___1891_26058.generalize);
        letrecs = (uu___1891_26058.letrecs);
        top_level = (uu___1891_26058.top_level);
        check_uvars = (uu___1891_26058.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1891_26058.use_eq_strict);
        is_iface = (uu___1891_26058.is_iface);
        admit = (uu___1891_26058.admit);
        lax = (uu___1891_26058.lax);
        lax_universes = (uu___1891_26058.lax_universes);
        phase1 = (uu___1891_26058.phase1);
        failhard = (uu___1891_26058.failhard);
        nosynth = (uu___1891_26058.nosynth);
        uvar_subtyping = (uu___1891_26058.uvar_subtyping);
        tc_term = (uu___1891_26058.tc_term);
        type_of = (uu___1891_26058.type_of);
        universe_of = (uu___1891_26058.universe_of);
        check_type_of = (uu___1891_26058.check_type_of);
        use_bv_sorts = (uu___1891_26058.use_bv_sorts);
        qtbl_name_and_index = (uu___1891_26058.qtbl_name_and_index);
        normalized_eff_names = (uu___1891_26058.normalized_eff_names);
        fv_delta_depths = (uu___1891_26058.fv_delta_depths);
        proof_ns = (uu___1891_26058.proof_ns);
        synth_hook = (uu___1891_26058.synth_hook);
        try_solve_implicits_hook = (uu___1891_26058.try_solve_implicits_hook);
        splice = (uu___1891_26058.splice);
        mpreprocess = (uu___1891_26058.mpreprocess);
        postprocess = (uu___1891_26058.postprocess);
        identifier_info = (uu___1891_26058.identifier_info);
        tc_hooks = (uu___1891_26058.tc_hooks);
        dsenv = (uu___1891_26058.dsenv);
        nbe = (uu___1891_26058.nbe);
        strict_args_tab = (uu___1891_26058.strict_args_tab);
        erasable_types_tab = (uu___1891_26058.erasable_types_tab)
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
    let uu____26089 = expected_typ env_  in
    ((let uu___1898_26095 = env_  in
      {
        solver = (uu___1898_26095.solver);
        range = (uu___1898_26095.range);
        curmodule = (uu___1898_26095.curmodule);
        gamma = (uu___1898_26095.gamma);
        gamma_sig = (uu___1898_26095.gamma_sig);
        gamma_cache = (uu___1898_26095.gamma_cache);
        modules = (uu___1898_26095.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1898_26095.sigtab);
        attrtab = (uu___1898_26095.attrtab);
        instantiate_imp = (uu___1898_26095.instantiate_imp);
        effects = (uu___1898_26095.effects);
        generalize = (uu___1898_26095.generalize);
        letrecs = (uu___1898_26095.letrecs);
        top_level = (uu___1898_26095.top_level);
        check_uvars = (uu___1898_26095.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1898_26095.use_eq_strict);
        is_iface = (uu___1898_26095.is_iface);
        admit = (uu___1898_26095.admit);
        lax = (uu___1898_26095.lax);
        lax_universes = (uu___1898_26095.lax_universes);
        phase1 = (uu___1898_26095.phase1);
        failhard = (uu___1898_26095.failhard);
        nosynth = (uu___1898_26095.nosynth);
        uvar_subtyping = (uu___1898_26095.uvar_subtyping);
        tc_term = (uu___1898_26095.tc_term);
        type_of = (uu___1898_26095.type_of);
        universe_of = (uu___1898_26095.universe_of);
        check_type_of = (uu___1898_26095.check_type_of);
        use_bv_sorts = (uu___1898_26095.use_bv_sorts);
        qtbl_name_and_index = (uu___1898_26095.qtbl_name_and_index);
        normalized_eff_names = (uu___1898_26095.normalized_eff_names);
        fv_delta_depths = (uu___1898_26095.fv_delta_depths);
        proof_ns = (uu___1898_26095.proof_ns);
        synth_hook = (uu___1898_26095.synth_hook);
        try_solve_implicits_hook = (uu___1898_26095.try_solve_implicits_hook);
        splice = (uu___1898_26095.splice);
        mpreprocess = (uu___1898_26095.mpreprocess);
        postprocess = (uu___1898_26095.postprocess);
        identifier_info = (uu___1898_26095.identifier_info);
        tc_hooks = (uu___1898_26095.tc_hooks);
        dsenv = (uu___1898_26095.dsenv);
        nbe = (uu___1898_26095.nbe);
        strict_args_tab = (uu___1898_26095.strict_args_tab);
        erasable_types_tab = (uu___1898_26095.erasable_types_tab)
      }), uu____26089)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____26107 =
      let uu____26108 = FStar_Ident.id_of_text ""  in [uu____26108]  in
    FStar_Ident.lid_of_ids uu____26107  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____26115 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____26115
        then
          let uu____26120 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____26120 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1906_26148 = env1  in
       {
         solver = (uu___1906_26148.solver);
         range = (uu___1906_26148.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1906_26148.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1906_26148.expected_typ);
         sigtab = (uu___1906_26148.sigtab);
         attrtab = (uu___1906_26148.attrtab);
         instantiate_imp = (uu___1906_26148.instantiate_imp);
         effects = (uu___1906_26148.effects);
         generalize = (uu___1906_26148.generalize);
         letrecs = (uu___1906_26148.letrecs);
         top_level = (uu___1906_26148.top_level);
         check_uvars = (uu___1906_26148.check_uvars);
         use_eq = (uu___1906_26148.use_eq);
         use_eq_strict = (uu___1906_26148.use_eq_strict);
         is_iface = (uu___1906_26148.is_iface);
         admit = (uu___1906_26148.admit);
         lax = (uu___1906_26148.lax);
         lax_universes = (uu___1906_26148.lax_universes);
         phase1 = (uu___1906_26148.phase1);
         failhard = (uu___1906_26148.failhard);
         nosynth = (uu___1906_26148.nosynth);
         uvar_subtyping = (uu___1906_26148.uvar_subtyping);
         tc_term = (uu___1906_26148.tc_term);
         type_of = (uu___1906_26148.type_of);
         universe_of = (uu___1906_26148.universe_of);
         check_type_of = (uu___1906_26148.check_type_of);
         use_bv_sorts = (uu___1906_26148.use_bv_sorts);
         qtbl_name_and_index = (uu___1906_26148.qtbl_name_and_index);
         normalized_eff_names = (uu___1906_26148.normalized_eff_names);
         fv_delta_depths = (uu___1906_26148.fv_delta_depths);
         proof_ns = (uu___1906_26148.proof_ns);
         synth_hook = (uu___1906_26148.synth_hook);
         try_solve_implicits_hook =
           (uu___1906_26148.try_solve_implicits_hook);
         splice = (uu___1906_26148.splice);
         mpreprocess = (uu___1906_26148.mpreprocess);
         postprocess = (uu___1906_26148.postprocess);
         identifier_info = (uu___1906_26148.identifier_info);
         tc_hooks = (uu___1906_26148.tc_hooks);
         dsenv = (uu___1906_26148.dsenv);
         nbe = (uu___1906_26148.nbe);
         strict_args_tab = (uu___1906_26148.strict_args_tab);
         erasable_types_tab = (uu___1906_26148.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26200)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26204,(uu____26205,t)))::tl
          ->
          let uu____26226 =
            let uu____26229 = FStar_Syntax_Free.uvars t  in
            ext out uu____26229  in
          aux uu____26226 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26232;
            FStar_Syntax_Syntax.index = uu____26233;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26241 =
            let uu____26244 = FStar_Syntax_Free.uvars t  in
            ext out uu____26244  in
          aux uu____26241 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26302)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26306,(uu____26307,t)))::tl
          ->
          let uu____26328 =
            let uu____26331 = FStar_Syntax_Free.univs t  in
            ext out uu____26331  in
          aux uu____26328 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26334;
            FStar_Syntax_Syntax.index = uu____26335;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26343 =
            let uu____26346 = FStar_Syntax_Free.univs t  in
            ext out uu____26346  in
          aux uu____26343 tl
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
          let uu____26408 = FStar_Util.set_add uname out  in
          aux uu____26408 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26411,(uu____26412,t)))::tl
          ->
          let uu____26433 =
            let uu____26436 = FStar_Syntax_Free.univnames t  in
            ext out uu____26436  in
          aux uu____26433 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26439;
            FStar_Syntax_Syntax.index = uu____26440;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26448 =
            let uu____26451 = FStar_Syntax_Free.univnames t  in
            ext out uu____26451  in
          aux uu____26448 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26472  ->
            match uu___12_26472 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26476 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26489 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26500 =
      let uu____26509 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26509
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26500 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26557 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26570  ->
              match uu___13_26570 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26573 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26573
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26577 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26577
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26581) ->
                  let uu____26598 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26598))
       in
    FStar_All.pipe_right uu____26557 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26612  ->
    match uu___14_26612 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26618 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26618
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26641  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26696) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26729,uu____26730) -> false  in
      let uu____26744 =
        FStar_List.tryFind
          (fun uu____26766  ->
             match uu____26766 with | (p,uu____26777) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26744 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26796,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26826 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26826
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2049_26848 = e  in
        {
          solver = (uu___2049_26848.solver);
          range = (uu___2049_26848.range);
          curmodule = (uu___2049_26848.curmodule);
          gamma = (uu___2049_26848.gamma);
          gamma_sig = (uu___2049_26848.gamma_sig);
          gamma_cache = (uu___2049_26848.gamma_cache);
          modules = (uu___2049_26848.modules);
          expected_typ = (uu___2049_26848.expected_typ);
          sigtab = (uu___2049_26848.sigtab);
          attrtab = (uu___2049_26848.attrtab);
          instantiate_imp = (uu___2049_26848.instantiate_imp);
          effects = (uu___2049_26848.effects);
          generalize = (uu___2049_26848.generalize);
          letrecs = (uu___2049_26848.letrecs);
          top_level = (uu___2049_26848.top_level);
          check_uvars = (uu___2049_26848.check_uvars);
          use_eq = (uu___2049_26848.use_eq);
          use_eq_strict = (uu___2049_26848.use_eq_strict);
          is_iface = (uu___2049_26848.is_iface);
          admit = (uu___2049_26848.admit);
          lax = (uu___2049_26848.lax);
          lax_universes = (uu___2049_26848.lax_universes);
          phase1 = (uu___2049_26848.phase1);
          failhard = (uu___2049_26848.failhard);
          nosynth = (uu___2049_26848.nosynth);
          uvar_subtyping = (uu___2049_26848.uvar_subtyping);
          tc_term = (uu___2049_26848.tc_term);
          type_of = (uu___2049_26848.type_of);
          universe_of = (uu___2049_26848.universe_of);
          check_type_of = (uu___2049_26848.check_type_of);
          use_bv_sorts = (uu___2049_26848.use_bv_sorts);
          qtbl_name_and_index = (uu___2049_26848.qtbl_name_and_index);
          normalized_eff_names = (uu___2049_26848.normalized_eff_names);
          fv_delta_depths = (uu___2049_26848.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2049_26848.synth_hook);
          try_solve_implicits_hook =
            (uu___2049_26848.try_solve_implicits_hook);
          splice = (uu___2049_26848.splice);
          mpreprocess = (uu___2049_26848.mpreprocess);
          postprocess = (uu___2049_26848.postprocess);
          identifier_info = (uu___2049_26848.identifier_info);
          tc_hooks = (uu___2049_26848.tc_hooks);
          dsenv = (uu___2049_26848.dsenv);
          nbe = (uu___2049_26848.nbe);
          strict_args_tab = (uu___2049_26848.strict_args_tab);
          erasable_types_tab = (uu___2049_26848.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2058_26896 = e  in
      {
        solver = (uu___2058_26896.solver);
        range = (uu___2058_26896.range);
        curmodule = (uu___2058_26896.curmodule);
        gamma = (uu___2058_26896.gamma);
        gamma_sig = (uu___2058_26896.gamma_sig);
        gamma_cache = (uu___2058_26896.gamma_cache);
        modules = (uu___2058_26896.modules);
        expected_typ = (uu___2058_26896.expected_typ);
        sigtab = (uu___2058_26896.sigtab);
        attrtab = (uu___2058_26896.attrtab);
        instantiate_imp = (uu___2058_26896.instantiate_imp);
        effects = (uu___2058_26896.effects);
        generalize = (uu___2058_26896.generalize);
        letrecs = (uu___2058_26896.letrecs);
        top_level = (uu___2058_26896.top_level);
        check_uvars = (uu___2058_26896.check_uvars);
        use_eq = (uu___2058_26896.use_eq);
        use_eq_strict = (uu___2058_26896.use_eq_strict);
        is_iface = (uu___2058_26896.is_iface);
        admit = (uu___2058_26896.admit);
        lax = (uu___2058_26896.lax);
        lax_universes = (uu___2058_26896.lax_universes);
        phase1 = (uu___2058_26896.phase1);
        failhard = (uu___2058_26896.failhard);
        nosynth = (uu___2058_26896.nosynth);
        uvar_subtyping = (uu___2058_26896.uvar_subtyping);
        tc_term = (uu___2058_26896.tc_term);
        type_of = (uu___2058_26896.type_of);
        universe_of = (uu___2058_26896.universe_of);
        check_type_of = (uu___2058_26896.check_type_of);
        use_bv_sorts = (uu___2058_26896.use_bv_sorts);
        qtbl_name_and_index = (uu___2058_26896.qtbl_name_and_index);
        normalized_eff_names = (uu___2058_26896.normalized_eff_names);
        fv_delta_depths = (uu___2058_26896.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2058_26896.synth_hook);
        try_solve_implicits_hook = (uu___2058_26896.try_solve_implicits_hook);
        splice = (uu___2058_26896.splice);
        mpreprocess = (uu___2058_26896.mpreprocess);
        postprocess = (uu___2058_26896.postprocess);
        identifier_info = (uu___2058_26896.identifier_info);
        tc_hooks = (uu___2058_26896.tc_hooks);
        dsenv = (uu___2058_26896.dsenv);
        nbe = (uu___2058_26896.nbe);
        strict_args_tab = (uu___2058_26896.strict_args_tab);
        erasable_types_tab = (uu___2058_26896.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26912 = FStar_Syntax_Free.names t  in
      let uu____26915 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26912 uu____26915
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26938 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26938
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26948 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26948
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____26969 =
      match uu____26969 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26989 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26989)
       in
    let uu____26997 =
      let uu____27001 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____27001 FStar_List.rev  in
    FStar_All.pipe_right uu____26997 (FStar_String.concat " ")
  
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
                  (let uu____27069 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____27069 with
                   | FStar_Pervasives_Native.Some uu____27073 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____27076 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____27086;
        FStar_TypeChecker_Common.univ_ineqs = uu____27087;
        FStar_TypeChecker_Common.implicits = uu____27088;_} -> true
    | uu____27098 -> false
  
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
          let uu___2102_27120 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2102_27120.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2102_27120.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2102_27120.FStar_TypeChecker_Common.implicits)
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
          let uu____27159 = FStar_Options.defensive ()  in
          if uu____27159
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27165 =
              let uu____27167 =
                let uu____27169 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27169  in
              Prims.op_Negation uu____27167  in
            (if uu____27165
             then
               let uu____27176 =
                 let uu____27182 =
                   let uu____27184 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27186 =
                     let uu____27188 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27188
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27184 uu____27186
                    in
                 (FStar_Errors.Warning_Defensive, uu____27182)  in
               FStar_Errors.log_issue rng uu____27176
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
          let uu____27228 =
            let uu____27230 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27230  in
          if uu____27228
          then ()
          else
            (let uu____27235 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27235 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27261 =
            let uu____27263 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27263  in
          if uu____27261
          then ()
          else
            (let uu____27268 = bound_vars e  in
             def_check_closed_in rng msg uu____27268 t)
  
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
          let uu___2139_27307 = g  in
          let uu____27308 =
            let uu____27309 =
              let uu____27310 =
                let uu____27317 =
                  let uu____27318 =
                    let uu____27335 =
                      let uu____27346 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27346]  in
                    (f, uu____27335)  in
                  FStar_Syntax_Syntax.Tm_app uu____27318  in
                FStar_Syntax_Syntax.mk uu____27317  in
              uu____27310 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27383  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27383) uu____27309
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27308;
            FStar_TypeChecker_Common.deferred =
              (uu___2139_27307.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2139_27307.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2139_27307.FStar_TypeChecker_Common.implicits)
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
          let uu___2146_27401 = g  in
          let uu____27402 =
            let uu____27403 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27403  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27402;
            FStar_TypeChecker_Common.deferred =
              (uu___2146_27401.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2146_27401.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2146_27401.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2151_27420 = g  in
          let uu____27421 =
            let uu____27422 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27422  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27421;
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27420.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27420.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27420.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2155_27424 = g  in
          let uu____27425 =
            let uu____27426 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27426  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27425;
            FStar_TypeChecker_Common.deferred =
              (uu___2155_27424.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2155_27424.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2155_27424.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27433 ->
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
                       let uu____27510 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27510
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2178_27517 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2178_27517.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2178_27517.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2178_27517.FStar_TypeChecker_Common.implicits)
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
               let uu____27551 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27551
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
            let uu___2193_27578 = g  in
            let uu____27579 =
              let uu____27580 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27580  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27579;
              FStar_TypeChecker_Common.deferred =
                (uu___2193_27578.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2193_27578.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2193_27578.FStar_TypeChecker_Common.implicits)
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
              let uu____27638 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27638 with
              | FStar_Pervasives_Native.Some
                  (uu____27663::(tm,uu____27665)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27729 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27747 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27747;
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
                    (let uu____27781 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27781
                     then
                       let uu____27785 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27785
                     else ());
                    (let g =
                       let uu___2217_27791 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2217_27791.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2217_27791.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2217_27791.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27845 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27902  ->
                      fun b  ->
                        match uu____27902 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27944 =
                              let uu____27957 = reason b  in
                              new_implicit_var_aux uu____27957 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27944 with
                             | (t,uu____27974,g_t) ->
                                 let uu____27988 =
                                   let uu____27991 =
                                     let uu____27994 =
                                       let uu____27995 =
                                         let uu____28002 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____28002, t)  in
                                       FStar_Syntax_Syntax.NT uu____27995  in
                                     [uu____27994]  in
                                   FStar_List.append substs1 uu____27991  in
                                 let uu____28013 = conj_guard g g_t  in
                                 (uu____27988, (FStar_List.append uvars [t]),
                                   uu____28013))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27845
              (fun uu____28042  ->
                 match uu____28042 with | (uu____28059,uvars,g) -> (uvars, g))
  
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
                let uu____28100 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____28100 FStar_Util.must  in
              let uu____28117 = inst_tscheme_with post_ts [u]  in
              match uu____28117 with
              | (uu____28122,post) ->
                  let uu____28124 =
                    let uu____28129 =
                      let uu____28130 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____28130]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____28129  in
                  uu____28124 FStar_Pervasives_Native.None r
               in
            let uu____28163 =
              let uu____28168 =
                let uu____28169 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28169]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28168  in
            uu____28163 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28205  -> ());
    push = (fun uu____28207  -> ());
    pop = (fun uu____28210  -> ());
    snapshot =
      (fun uu____28213  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28232  -> fun uu____28233  -> ());
    encode_sig = (fun uu____28248  -> fun uu____28249  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28255 =
             let uu____28262 = FStar_Options.peek ()  in (e, g, uu____28262)
              in
           [uu____28255]);
    solve = (fun uu____28278  -> fun uu____28279  -> fun uu____28280  -> ());
    finish = (fun uu____28287  -> ());
    refresh = (fun uu____28289  -> ())
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
        | uu____28398 -> false  in
      let uu____28412 =
        FStar_Util.find_opt
          (fun uu____28446  ->
             match uu____28446 with
             | (lbname',uu____28462,uu____28463,uu____28464) ->
                 compare_either FStar_Syntax_Syntax.bv_eq
                   FStar_Syntax_Syntax.fv_eq lbname lbname') env1.letrecs
         in
      match uu____28412 with
      | FStar_Pervasives_Native.Some
          (uu____28478,arity,uu____28480,uu____28481) ->
          FStar_Pervasives_Native.Some arity
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  