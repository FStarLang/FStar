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
           (fun uu___0_14046  ->
              match uu___0_14046 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14049 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____14049  in
                  let uu____14050 =
                    let uu____14051 = FStar_Syntax_Subst.compress y  in
                    uu____14051.FStar_Syntax_Syntax.n  in
                  (match uu____14050 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14055 =
                         let uu___324_14056 = y1  in
                         let uu____14057 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___324_14056.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___324_14056.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14057
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14055
                   | uu____14060 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst  ->
    fun env1  ->
      let uu___330_14074 = env1  in
      let uu____14075 = rename_gamma subst env1.gamma  in
      {
        solver = (uu___330_14074.solver);
        range = (uu___330_14074.range);
        curmodule = (uu___330_14074.curmodule);
        gamma = uu____14075;
        gamma_sig = (uu___330_14074.gamma_sig);
        gamma_cache = (uu___330_14074.gamma_cache);
        modules = (uu___330_14074.modules);
        expected_typ = (uu___330_14074.expected_typ);
        sigtab = (uu___330_14074.sigtab);
        attrtab = (uu___330_14074.attrtab);
        instantiate_imp = (uu___330_14074.instantiate_imp);
        effects = (uu___330_14074.effects);
        generalize = (uu___330_14074.generalize);
        letrecs = (uu___330_14074.letrecs);
        top_level = (uu___330_14074.top_level);
        check_uvars = (uu___330_14074.check_uvars);
        use_eq = (uu___330_14074.use_eq);
        use_eq_strict = (uu___330_14074.use_eq_strict);
        is_iface = (uu___330_14074.is_iface);
        admit = (uu___330_14074.admit);
        lax = (uu___330_14074.lax);
        lax_universes = (uu___330_14074.lax_universes);
        phase1 = (uu___330_14074.phase1);
        failhard = (uu___330_14074.failhard);
        nosynth = (uu___330_14074.nosynth);
        uvar_subtyping = (uu___330_14074.uvar_subtyping);
        tc_term = (uu___330_14074.tc_term);
        type_of = (uu___330_14074.type_of);
        universe_of = (uu___330_14074.universe_of);
        check_type_of = (uu___330_14074.check_type_of);
        use_bv_sorts = (uu___330_14074.use_bv_sorts);
        qtbl_name_and_index = (uu___330_14074.qtbl_name_and_index);
        normalized_eff_names = (uu___330_14074.normalized_eff_names);
        fv_delta_depths = (uu___330_14074.fv_delta_depths);
        proof_ns = (uu___330_14074.proof_ns);
        synth_hook = (uu___330_14074.synth_hook);
        try_solve_implicits_hook = (uu___330_14074.try_solve_implicits_hook);
        splice = (uu___330_14074.splice);
        mpreprocess = (uu___330_14074.mpreprocess);
        postprocess = (uu___330_14074.postprocess);
        identifier_info = (uu___330_14074.identifier_info);
        tc_hooks = (uu___330_14074.tc_hooks);
        dsenv = (uu___330_14074.dsenv);
        nbe = (uu___330_14074.nbe);
        strict_args_tab = (uu___330_14074.strict_args_tab);
        erasable_types_tab = (uu___330_14074.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14083  -> fun uu____14084  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___337_14106 = env1  in
      {
        solver = (uu___337_14106.solver);
        range = (uu___337_14106.range);
        curmodule = (uu___337_14106.curmodule);
        gamma = (uu___337_14106.gamma);
        gamma_sig = (uu___337_14106.gamma_sig);
        gamma_cache = (uu___337_14106.gamma_cache);
        modules = (uu___337_14106.modules);
        expected_typ = (uu___337_14106.expected_typ);
        sigtab = (uu___337_14106.sigtab);
        attrtab = (uu___337_14106.attrtab);
        instantiate_imp = (uu___337_14106.instantiate_imp);
        effects = (uu___337_14106.effects);
        generalize = (uu___337_14106.generalize);
        letrecs = (uu___337_14106.letrecs);
        top_level = (uu___337_14106.top_level);
        check_uvars = (uu___337_14106.check_uvars);
        use_eq = (uu___337_14106.use_eq);
        use_eq_strict = (uu___337_14106.use_eq_strict);
        is_iface = (uu___337_14106.is_iface);
        admit = (uu___337_14106.admit);
        lax = (uu___337_14106.lax);
        lax_universes = (uu___337_14106.lax_universes);
        phase1 = (uu___337_14106.phase1);
        failhard = (uu___337_14106.failhard);
        nosynth = (uu___337_14106.nosynth);
        uvar_subtyping = (uu___337_14106.uvar_subtyping);
        tc_term = (uu___337_14106.tc_term);
        type_of = (uu___337_14106.type_of);
        universe_of = (uu___337_14106.universe_of);
        check_type_of = (uu___337_14106.check_type_of);
        use_bv_sorts = (uu___337_14106.use_bv_sorts);
        qtbl_name_and_index = (uu___337_14106.qtbl_name_and_index);
        normalized_eff_names = (uu___337_14106.normalized_eff_names);
        fv_delta_depths = (uu___337_14106.fv_delta_depths);
        proof_ns = (uu___337_14106.proof_ns);
        synth_hook = (uu___337_14106.synth_hook);
        try_solve_implicits_hook = (uu___337_14106.try_solve_implicits_hook);
        splice = (uu___337_14106.splice);
        mpreprocess = (uu___337_14106.mpreprocess);
        postprocess = (uu___337_14106.postprocess);
        identifier_info = (uu___337_14106.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___337_14106.dsenv);
        nbe = (uu___337_14106.nbe);
        strict_args_tab = (uu___337_14106.strict_args_tab);
        erasable_types_tab = (uu___337_14106.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___341_14118 = e  in
      let uu____14119 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___341_14118.solver);
        range = (uu___341_14118.range);
        curmodule = (uu___341_14118.curmodule);
        gamma = (uu___341_14118.gamma);
        gamma_sig = (uu___341_14118.gamma_sig);
        gamma_cache = (uu___341_14118.gamma_cache);
        modules = (uu___341_14118.modules);
        expected_typ = (uu___341_14118.expected_typ);
        sigtab = (uu___341_14118.sigtab);
        attrtab = (uu___341_14118.attrtab);
        instantiate_imp = (uu___341_14118.instantiate_imp);
        effects = (uu___341_14118.effects);
        generalize = (uu___341_14118.generalize);
        letrecs = (uu___341_14118.letrecs);
        top_level = (uu___341_14118.top_level);
        check_uvars = (uu___341_14118.check_uvars);
        use_eq = (uu___341_14118.use_eq);
        use_eq_strict = (uu___341_14118.use_eq_strict);
        is_iface = (uu___341_14118.is_iface);
        admit = (uu___341_14118.admit);
        lax = (uu___341_14118.lax);
        lax_universes = (uu___341_14118.lax_universes);
        phase1 = (uu___341_14118.phase1);
        failhard = (uu___341_14118.failhard);
        nosynth = (uu___341_14118.nosynth);
        uvar_subtyping = (uu___341_14118.uvar_subtyping);
        tc_term = (uu___341_14118.tc_term);
        type_of = (uu___341_14118.type_of);
        universe_of = (uu___341_14118.universe_of);
        check_type_of = (uu___341_14118.check_type_of);
        use_bv_sorts = (uu___341_14118.use_bv_sorts);
        qtbl_name_and_index = (uu___341_14118.qtbl_name_and_index);
        normalized_eff_names = (uu___341_14118.normalized_eff_names);
        fv_delta_depths = (uu___341_14118.fv_delta_depths);
        proof_ns = (uu___341_14118.proof_ns);
        synth_hook = (uu___341_14118.synth_hook);
        try_solve_implicits_hook = (uu___341_14118.try_solve_implicits_hook);
        splice = (uu___341_14118.splice);
        mpreprocess = (uu___341_14118.mpreprocess);
        postprocess = (uu___341_14118.postprocess);
        identifier_info = (uu___341_14118.identifier_info);
        tc_hooks = (uu___341_14118.tc_hooks);
        dsenv = uu____14119;
        nbe = (uu___341_14118.nbe);
        strict_args_tab = (uu___341_14118.strict_args_tab);
        erasable_types_tab = (uu___341_14118.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____14136 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____14136)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14151) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14154,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14156,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14159 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14173 . unit -> 'uuuuuu14173 FStar_Util.smap =
  fun uu____14180  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14186 . unit -> 'uuuuuu14186 FStar_Util.smap =
  fun uu____14193  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14331 = new_gamma_cache ()  in
                  let uu____14334 = new_sigtab ()  in
                  let uu____14337 = new_sigtab ()  in
                  let uu____14344 =
                    let uu____14359 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14359, FStar_Pervasives_Native.None)  in
                  let uu____14380 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14384 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14388 = FStar_Options.using_facts_from ()  in
                  let uu____14389 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14392 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14393 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14407 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14331;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14334;
                    attrtab = uu____14337;
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
                    qtbl_name_and_index = uu____14344;
                    normalized_eff_names = uu____14380;
                    fv_delta_depths = uu____14384;
                    proof_ns = uu____14388;
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
                    identifier_info = uu____14389;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14392;
                    nbe;
                    strict_args_tab = uu____14393;
                    erasable_types_tab = uu____14407
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
  fun uu____14600  ->
    let uu____14601 = FStar_ST.op_Bang query_indices  in
    match uu____14601 with
    | [] -> failwith "Empty query indices!"
    | uu____14656 ->
        let uu____14666 =
          let uu____14676 =
            let uu____14684 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14684  in
          let uu____14738 = FStar_ST.op_Bang query_indices  in uu____14676 ::
            uu____14738
           in
        FStar_ST.op_Colon_Equals query_indices uu____14666
  
let (pop_query_indices : unit -> unit) =
  fun uu____14834  ->
    let uu____14835 = FStar_ST.op_Bang query_indices  in
    match uu____14835 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14962  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14999  ->
    match uu____14999 with
    | (l,n) ->
        let uu____15009 = FStar_ST.op_Bang query_indices  in
        (match uu____15009 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____15131 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15154  ->
    let uu____15155 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15155
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15223 =
       let uu____15226 = FStar_ST.op_Bang stack  in env1 :: uu____15226  in
     FStar_ST.op_Colon_Equals stack uu____15223);
    (let uu___415_15275 = env1  in
     let uu____15276 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15279 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15282 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15289 =
       let uu____15304 =
         let uu____15308 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15308  in
       let uu____15340 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15304, uu____15340)  in
     let uu____15389 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15392 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15395 =
       let uu____15398 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15398  in
     let uu____15418 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15431 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___415_15275.solver);
       range = (uu___415_15275.range);
       curmodule = (uu___415_15275.curmodule);
       gamma = (uu___415_15275.gamma);
       gamma_sig = (uu___415_15275.gamma_sig);
       gamma_cache = uu____15276;
       modules = (uu___415_15275.modules);
       expected_typ = (uu___415_15275.expected_typ);
       sigtab = uu____15279;
       attrtab = uu____15282;
       instantiate_imp = (uu___415_15275.instantiate_imp);
       effects = (uu___415_15275.effects);
       generalize = (uu___415_15275.generalize);
       letrecs = (uu___415_15275.letrecs);
       top_level = (uu___415_15275.top_level);
       check_uvars = (uu___415_15275.check_uvars);
       use_eq = (uu___415_15275.use_eq);
       use_eq_strict = (uu___415_15275.use_eq_strict);
       is_iface = (uu___415_15275.is_iface);
       admit = (uu___415_15275.admit);
       lax = (uu___415_15275.lax);
       lax_universes = (uu___415_15275.lax_universes);
       phase1 = (uu___415_15275.phase1);
       failhard = (uu___415_15275.failhard);
       nosynth = (uu___415_15275.nosynth);
       uvar_subtyping = (uu___415_15275.uvar_subtyping);
       tc_term = (uu___415_15275.tc_term);
       type_of = (uu___415_15275.type_of);
       universe_of = (uu___415_15275.universe_of);
       check_type_of = (uu___415_15275.check_type_of);
       use_bv_sorts = (uu___415_15275.use_bv_sorts);
       qtbl_name_and_index = uu____15289;
       normalized_eff_names = uu____15389;
       fv_delta_depths = uu____15392;
       proof_ns = (uu___415_15275.proof_ns);
       synth_hook = (uu___415_15275.synth_hook);
       try_solve_implicits_hook = (uu___415_15275.try_solve_implicits_hook);
       splice = (uu___415_15275.splice);
       mpreprocess = (uu___415_15275.mpreprocess);
       postprocess = (uu___415_15275.postprocess);
       identifier_info = uu____15395;
       tc_hooks = (uu___415_15275.tc_hooks);
       dsenv = (uu___415_15275.dsenv);
       nbe = (uu___415_15275.nbe);
       strict_args_tab = uu____15418;
       erasable_types_tab = uu____15431
     })
  
let (pop_stack : unit -> env) =
  fun uu____15441  ->
    let uu____15442 = FStar_ST.op_Bang stack  in
    match uu____15442 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15496 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15586  ->
           let uu____15587 = snapshot_stack env1  in
           match uu____15587 with
           | (stack_depth,env2) ->
               let uu____15621 = snapshot_query_indices ()  in
               (match uu____15621 with
                | (query_indices_depth,()) ->
                    let uu____15654 = (env2.solver).snapshot msg  in
                    (match uu____15654 with
                     | (solver_depth,()) ->
                         let uu____15711 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____15711 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___440_15778 = env2  in
                                 {
                                   solver = (uu___440_15778.solver);
                                   range = (uu___440_15778.range);
                                   curmodule = (uu___440_15778.curmodule);
                                   gamma = (uu___440_15778.gamma);
                                   gamma_sig = (uu___440_15778.gamma_sig);
                                   gamma_cache = (uu___440_15778.gamma_cache);
                                   modules = (uu___440_15778.modules);
                                   expected_typ =
                                     (uu___440_15778.expected_typ);
                                   sigtab = (uu___440_15778.sigtab);
                                   attrtab = (uu___440_15778.attrtab);
                                   instantiate_imp =
                                     (uu___440_15778.instantiate_imp);
                                   effects = (uu___440_15778.effects);
                                   generalize = (uu___440_15778.generalize);
                                   letrecs = (uu___440_15778.letrecs);
                                   top_level = (uu___440_15778.top_level);
                                   check_uvars = (uu___440_15778.check_uvars);
                                   use_eq = (uu___440_15778.use_eq);
                                   use_eq_strict =
                                     (uu___440_15778.use_eq_strict);
                                   is_iface = (uu___440_15778.is_iface);
                                   admit = (uu___440_15778.admit);
                                   lax = (uu___440_15778.lax);
                                   lax_universes =
                                     (uu___440_15778.lax_universes);
                                   phase1 = (uu___440_15778.phase1);
                                   failhard = (uu___440_15778.failhard);
                                   nosynth = (uu___440_15778.nosynth);
                                   uvar_subtyping =
                                     (uu___440_15778.uvar_subtyping);
                                   tc_term = (uu___440_15778.tc_term);
                                   type_of = (uu___440_15778.type_of);
                                   universe_of = (uu___440_15778.universe_of);
                                   check_type_of =
                                     (uu___440_15778.check_type_of);
                                   use_bv_sorts =
                                     (uu___440_15778.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___440_15778.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___440_15778.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___440_15778.fv_delta_depths);
                                   proof_ns = (uu___440_15778.proof_ns);
                                   synth_hook = (uu___440_15778.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___440_15778.try_solve_implicits_hook);
                                   splice = (uu___440_15778.splice);
                                   mpreprocess = (uu___440_15778.mpreprocess);
                                   postprocess = (uu___440_15778.postprocess);
                                   identifier_info =
                                     (uu___440_15778.identifier_info);
                                   tc_hooks = (uu___440_15778.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___440_15778.nbe);
                                   strict_args_tab =
                                     (uu___440_15778.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___440_15778.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15812  ->
             let uu____15813 =
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
             match uu____15813 with
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
                             ((let uu____15993 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15993
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____16009 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____16009
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____16041,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____16083 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16113  ->
                  match uu____16113 with
                  | (m,uu____16121) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16083 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16135 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16135 next);
              (let uu___485_16138 = env1  in
               {
                 solver = (uu___485_16138.solver);
                 range = (uu___485_16138.range);
                 curmodule = (uu___485_16138.curmodule);
                 gamma = (uu___485_16138.gamma);
                 gamma_sig = (uu___485_16138.gamma_sig);
                 gamma_cache = (uu___485_16138.gamma_cache);
                 modules = (uu___485_16138.modules);
                 expected_typ = (uu___485_16138.expected_typ);
                 sigtab = (uu___485_16138.sigtab);
                 attrtab = (uu___485_16138.attrtab);
                 instantiate_imp = (uu___485_16138.instantiate_imp);
                 effects = (uu___485_16138.effects);
                 generalize = (uu___485_16138.generalize);
                 letrecs = (uu___485_16138.letrecs);
                 top_level = (uu___485_16138.top_level);
                 check_uvars = (uu___485_16138.check_uvars);
                 use_eq = (uu___485_16138.use_eq);
                 use_eq_strict = (uu___485_16138.use_eq_strict);
                 is_iface = (uu___485_16138.is_iface);
                 admit = (uu___485_16138.admit);
                 lax = (uu___485_16138.lax);
                 lax_universes = (uu___485_16138.lax_universes);
                 phase1 = (uu___485_16138.phase1);
                 failhard = (uu___485_16138.failhard);
                 nosynth = (uu___485_16138.nosynth);
                 uvar_subtyping = (uu___485_16138.uvar_subtyping);
                 tc_term = (uu___485_16138.tc_term);
                 type_of = (uu___485_16138.type_of);
                 universe_of = (uu___485_16138.universe_of);
                 check_type_of = (uu___485_16138.check_type_of);
                 use_bv_sorts = (uu___485_16138.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___485_16138.normalized_eff_names);
                 fv_delta_depths = (uu___485_16138.fv_delta_depths);
                 proof_ns = (uu___485_16138.proof_ns);
                 synth_hook = (uu___485_16138.synth_hook);
                 try_solve_implicits_hook =
                   (uu___485_16138.try_solve_implicits_hook);
                 splice = (uu___485_16138.splice);
                 mpreprocess = (uu___485_16138.mpreprocess);
                 postprocess = (uu___485_16138.postprocess);
                 identifier_info = (uu___485_16138.identifier_info);
                 tc_hooks = (uu___485_16138.tc_hooks);
                 dsenv = (uu___485_16138.dsenv);
                 nbe = (uu___485_16138.nbe);
                 strict_args_tab = (uu___485_16138.strict_args_tab);
                 erasable_types_tab = (uu___485_16138.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16155,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16170 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16170 next);
              (let uu___494_16173 = env1  in
               {
                 solver = (uu___494_16173.solver);
                 range = (uu___494_16173.range);
                 curmodule = (uu___494_16173.curmodule);
                 gamma = (uu___494_16173.gamma);
                 gamma_sig = (uu___494_16173.gamma_sig);
                 gamma_cache = (uu___494_16173.gamma_cache);
                 modules = (uu___494_16173.modules);
                 expected_typ = (uu___494_16173.expected_typ);
                 sigtab = (uu___494_16173.sigtab);
                 attrtab = (uu___494_16173.attrtab);
                 instantiate_imp = (uu___494_16173.instantiate_imp);
                 effects = (uu___494_16173.effects);
                 generalize = (uu___494_16173.generalize);
                 letrecs = (uu___494_16173.letrecs);
                 top_level = (uu___494_16173.top_level);
                 check_uvars = (uu___494_16173.check_uvars);
                 use_eq = (uu___494_16173.use_eq);
                 use_eq_strict = (uu___494_16173.use_eq_strict);
                 is_iface = (uu___494_16173.is_iface);
                 admit = (uu___494_16173.admit);
                 lax = (uu___494_16173.lax);
                 lax_universes = (uu___494_16173.lax_universes);
                 phase1 = (uu___494_16173.phase1);
                 failhard = (uu___494_16173.failhard);
                 nosynth = (uu___494_16173.nosynth);
                 uvar_subtyping = (uu___494_16173.uvar_subtyping);
                 tc_term = (uu___494_16173.tc_term);
                 type_of = (uu___494_16173.type_of);
                 universe_of = (uu___494_16173.universe_of);
                 check_type_of = (uu___494_16173.check_type_of);
                 use_bv_sorts = (uu___494_16173.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___494_16173.normalized_eff_names);
                 fv_delta_depths = (uu___494_16173.fv_delta_depths);
                 proof_ns = (uu___494_16173.proof_ns);
                 synth_hook = (uu___494_16173.synth_hook);
                 try_solve_implicits_hook =
                   (uu___494_16173.try_solve_implicits_hook);
                 splice = (uu___494_16173.splice);
                 mpreprocess = (uu___494_16173.mpreprocess);
                 postprocess = (uu___494_16173.postprocess);
                 identifier_info = (uu___494_16173.identifier_info);
                 tc_hooks = (uu___494_16173.tc_hooks);
                 dsenv = (uu___494_16173.dsenv);
                 nbe = (uu___494_16173.nbe);
                 strict_args_tab = (uu___494_16173.strict_args_tab);
                 erasable_types_tab = (uu___494_16173.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16202 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16202 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___501_16218 = e  in
         {
           solver = (uu___501_16218.solver);
           range = r;
           curmodule = (uu___501_16218.curmodule);
           gamma = (uu___501_16218.gamma);
           gamma_sig = (uu___501_16218.gamma_sig);
           gamma_cache = (uu___501_16218.gamma_cache);
           modules = (uu___501_16218.modules);
           expected_typ = (uu___501_16218.expected_typ);
           sigtab = (uu___501_16218.sigtab);
           attrtab = (uu___501_16218.attrtab);
           instantiate_imp = (uu___501_16218.instantiate_imp);
           effects = (uu___501_16218.effects);
           generalize = (uu___501_16218.generalize);
           letrecs = (uu___501_16218.letrecs);
           top_level = (uu___501_16218.top_level);
           check_uvars = (uu___501_16218.check_uvars);
           use_eq = (uu___501_16218.use_eq);
           use_eq_strict = (uu___501_16218.use_eq_strict);
           is_iface = (uu___501_16218.is_iface);
           admit = (uu___501_16218.admit);
           lax = (uu___501_16218.lax);
           lax_universes = (uu___501_16218.lax_universes);
           phase1 = (uu___501_16218.phase1);
           failhard = (uu___501_16218.failhard);
           nosynth = (uu___501_16218.nosynth);
           uvar_subtyping = (uu___501_16218.uvar_subtyping);
           tc_term = (uu___501_16218.tc_term);
           type_of = (uu___501_16218.type_of);
           universe_of = (uu___501_16218.universe_of);
           check_type_of = (uu___501_16218.check_type_of);
           use_bv_sorts = (uu___501_16218.use_bv_sorts);
           qtbl_name_and_index = (uu___501_16218.qtbl_name_and_index);
           normalized_eff_names = (uu___501_16218.normalized_eff_names);
           fv_delta_depths = (uu___501_16218.fv_delta_depths);
           proof_ns = (uu___501_16218.proof_ns);
           synth_hook = (uu___501_16218.synth_hook);
           try_solve_implicits_hook =
             (uu___501_16218.try_solve_implicits_hook);
           splice = (uu___501_16218.splice);
           mpreprocess = (uu___501_16218.mpreprocess);
           postprocess = (uu___501_16218.postprocess);
           identifier_info = (uu___501_16218.identifier_info);
           tc_hooks = (uu___501_16218.tc_hooks);
           dsenv = (uu___501_16218.dsenv);
           nbe = (uu___501_16218.nbe);
           strict_args_tab = (uu___501_16218.strict_args_tab);
           erasable_types_tab = (uu___501_16218.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16238 =
        let uu____16239 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16239 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16238
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16294 =
          let uu____16295 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16295 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16294
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16350 =
          let uu____16351 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16351 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16350
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16406 =
        let uu____16407 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16407 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16406
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___518_16471 = env1  in
      {
        solver = (uu___518_16471.solver);
        range = (uu___518_16471.range);
        curmodule = lid;
        gamma = (uu___518_16471.gamma);
        gamma_sig = (uu___518_16471.gamma_sig);
        gamma_cache = (uu___518_16471.gamma_cache);
        modules = (uu___518_16471.modules);
        expected_typ = (uu___518_16471.expected_typ);
        sigtab = (uu___518_16471.sigtab);
        attrtab = (uu___518_16471.attrtab);
        instantiate_imp = (uu___518_16471.instantiate_imp);
        effects = (uu___518_16471.effects);
        generalize = (uu___518_16471.generalize);
        letrecs = (uu___518_16471.letrecs);
        top_level = (uu___518_16471.top_level);
        check_uvars = (uu___518_16471.check_uvars);
        use_eq = (uu___518_16471.use_eq);
        use_eq_strict = (uu___518_16471.use_eq_strict);
        is_iface = (uu___518_16471.is_iface);
        admit = (uu___518_16471.admit);
        lax = (uu___518_16471.lax);
        lax_universes = (uu___518_16471.lax_universes);
        phase1 = (uu___518_16471.phase1);
        failhard = (uu___518_16471.failhard);
        nosynth = (uu___518_16471.nosynth);
        uvar_subtyping = (uu___518_16471.uvar_subtyping);
        tc_term = (uu___518_16471.tc_term);
        type_of = (uu___518_16471.type_of);
        universe_of = (uu___518_16471.universe_of);
        check_type_of = (uu___518_16471.check_type_of);
        use_bv_sorts = (uu___518_16471.use_bv_sorts);
        qtbl_name_and_index = (uu___518_16471.qtbl_name_and_index);
        normalized_eff_names = (uu___518_16471.normalized_eff_names);
        fv_delta_depths = (uu___518_16471.fv_delta_depths);
        proof_ns = (uu___518_16471.proof_ns);
        synth_hook = (uu___518_16471.synth_hook);
        try_solve_implicits_hook = (uu___518_16471.try_solve_implicits_hook);
        splice = (uu___518_16471.splice);
        mpreprocess = (uu___518_16471.mpreprocess);
        postprocess = (uu___518_16471.postprocess);
        identifier_info = (uu___518_16471.identifier_info);
        tc_hooks = (uu___518_16471.tc_hooks);
        dsenv = (uu___518_16471.dsenv);
        nbe = (uu___518_16471.nbe);
        strict_args_tab = (uu___518_16471.strict_args_tab);
        erasable_types_tab = (uu___518_16471.erasable_types_tab)
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
      let uu____16502 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16502
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16515 =
      let uu____16517 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____16517  in
    (FStar_Errors.Fatal_NameNotFound, uu____16515)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16532 =
      let uu____16534 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16534  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16532)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16543  ->
    let uu____16544 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
    FStar_Syntax_Syntax.U_unif uu____16544
  
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
      | ((formals,t),uu____16646) ->
          let vs = mk_univ_subst formals us  in
          let uu____16670 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16670)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16687  ->
    match uu___1_16687 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16713  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16733 = inst_tscheme t  in
      match uu____16733 with
      | (us,t1) ->
          let uu____16744 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16744)
  
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
          let uu____16769 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16771 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16769 uu____16771
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
        fun uu____16798  ->
          match uu____16798 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16812 =
                    let uu____16814 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16818 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16822 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16824 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16814 uu____16818 uu____16822 uu____16824
                     in
                  failwith uu____16812)
               else ();
               (let uu____16829 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16829))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16847 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16858 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16869 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____16883 =
        let uu____16885 = FStar_Ident.nsstr l  in
        let uu____16887 = FStar_Ident.string_of_lid cur  in
        uu____16885 = uu____16887  in
      if uu____16883
      then Yes
      else
        (let uu____16893 =
           let uu____16895 = FStar_Ident.nsstr l  in
           let uu____16897 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____16895 uu____16897  in
         if uu____16893
         then
           let lns =
             let uu____16903 = FStar_Ident.ns_of_lid l  in
             let uu____16906 =
               let uu____16909 = FStar_Ident.ident_of_lid l  in [uu____16909]
                in
             FStar_List.append uu____16903 uu____16906  in
           let cur1 =
             let uu____16913 = FStar_Ident.ns_of_lid cur  in
             let uu____16916 =
               let uu____16919 = FStar_Ident.ident_of_lid cur  in
               [uu____16919]  in
             FStar_List.append uu____16913 uu____16916  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____16943) -> Maybe
             | (uu____16950,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____16969 = FStar_Ident.text_of_id hd  in
                 let uu____16971 = FStar_Ident.text_of_id hd'  in
                 uu____16969 = uu____16971 -> aux tl tl'
             | uu____16974 -> No  in
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
        (let uu____17026 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____17026 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____17070 =
            let uu____17073 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____17073  in
          match uu____17070 with
          | FStar_Pervasives_Native.None  ->
              let uu____17095 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_17139  ->
                     match uu___2_17139 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17178 = FStar_Ident.lid_equals lid l  in
                         if uu____17178
                         then
                           let uu____17201 =
                             let uu____17220 =
                               let uu____17235 = inst_tscheme t  in
                               FStar_Util.Inl uu____17235  in
                             let uu____17250 = FStar_Ident.range_of_lid l  in
                             (uu____17220, uu____17250)  in
                           FStar_Pervasives_Native.Some uu____17201
                         else FStar_Pervasives_Native.None
                     | uu____17303 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17095
                (fun uu____17341  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17351  ->
                        match uu___3_17351 with
                        | (uu____17354,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17356);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17357;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17358;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17359;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17360;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17361;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17383 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17383
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
                                  uu____17435 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17442 -> cache t  in
                            let uu____17443 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17443 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17449 =
                                   let uu____17450 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17450)
                                    in
                                 maybe_cache uu____17449)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17521 = find_in_sigtab env1 lid  in
         match uu____17521 with
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
      let uu____17602 = lookup_qname env1 lid  in
      match uu____17602 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17623,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17737 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17737 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17782 =
          let uu____17785 = lookup_attr env2 attr  in se1 :: uu____17785  in
        FStar_Util.smap_add (attrtab env2) attr uu____17782  in
      FStar_List.iter
        (fun attr  ->
           let uu____17795 =
             let uu____17796 = FStar_Syntax_Subst.compress attr  in
             uu____17796.FStar_Syntax_Syntax.n  in
           match uu____17795 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17800 =
                 let uu____17802 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17802  in
               add_one env1 se uu____17800
           | uu____17803 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17826) ->
          add_sigelts env1 ses
      | uu____17835 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17843 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17843 se) lids;
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
        (fun uu___4_17877  ->
           match uu___4_17877 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____17887 =
                 let uu____17894 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____17894)  in
               FStar_Pervasives_Native.Some uu____17887
           | uu____17903 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17965,lb::[]),uu____17967) ->
            let uu____17976 =
              let uu____17985 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17994 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17985, uu____17994)  in
            FStar_Pervasives_Native.Some uu____17976
        | FStar_Syntax_Syntax.Sig_let ((uu____18007,lbs),uu____18009) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____18041 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____18054 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____18054
                     then
                       let uu____18067 =
                         let uu____18076 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____18085 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____18076, uu____18085)  in
                       FStar_Pervasives_Native.Some uu____18067
                     else FStar_Pervasives_Native.None)
        | uu____18108 -> FStar_Pervasives_Native.None
  
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
                    let uu____18200 =
                      let uu____18202 =
                        let uu____18204 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18206 =
                          let uu____18208 =
                            let uu____18210 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18216 =
                              let uu____18218 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18218  in
                            Prims.op_Hat uu____18210 uu____18216  in
                          Prims.op_Hat ", expected " uu____18208  in
                        Prims.op_Hat uu____18204 uu____18206  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18202
                       in
                    failwith uu____18200
                  else ());
             (let uu____18225 =
                let uu____18234 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18234, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18225))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18254,uu____18255) ->
            let uu____18260 =
              let uu____18269 =
                let uu____18274 =
                  let uu____18275 =
                    let uu____18278 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18278  in
                  (us, uu____18275)  in
                inst_ts us_opt uu____18274  in
              (uu____18269, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18260
        | uu____18297 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18386 =
          match uu____18386 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18482,uvs,t,uu____18485,uu____18486,uu____18487);
                      FStar_Syntax_Syntax.sigrng = uu____18488;
                      FStar_Syntax_Syntax.sigquals = uu____18489;
                      FStar_Syntax_Syntax.sigmeta = uu____18490;
                      FStar_Syntax_Syntax.sigattrs = uu____18491;
                      FStar_Syntax_Syntax.sigopts = uu____18492;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18517 =
                     let uu____18526 = inst_tscheme1 (uvs, t)  in
                     (uu____18526, rng)  in
                   FStar_Pervasives_Native.Some uu____18517
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18550;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18552;
                      FStar_Syntax_Syntax.sigattrs = uu____18553;
                      FStar_Syntax_Syntax.sigopts = uu____18554;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18573 =
                     let uu____18575 = in_cur_mod env1 l  in
                     uu____18575 = Yes  in
                   if uu____18573
                   then
                     let uu____18587 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18587
                      then
                        let uu____18603 =
                          let uu____18612 = inst_tscheme1 (uvs, t)  in
                          (uu____18612, rng)  in
                        FStar_Pervasives_Native.Some uu____18603
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18645 =
                        let uu____18654 = inst_tscheme1 (uvs, t)  in
                        (uu____18654, rng)  in
                      FStar_Pervasives_Native.Some uu____18645)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18679,uu____18680);
                      FStar_Syntax_Syntax.sigrng = uu____18681;
                      FStar_Syntax_Syntax.sigquals = uu____18682;
                      FStar_Syntax_Syntax.sigmeta = uu____18683;
                      FStar_Syntax_Syntax.sigattrs = uu____18684;
                      FStar_Syntax_Syntax.sigopts = uu____18685;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18728 =
                          let uu____18737 = inst_tscheme1 (uvs, k)  in
                          (uu____18737, rng)  in
                        FStar_Pervasives_Native.Some uu____18728
                    | uu____18758 ->
                        let uu____18759 =
                          let uu____18768 =
                            let uu____18773 =
                              let uu____18774 =
                                let uu____18777 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18777
                                 in
                              (uvs, uu____18774)  in
                            inst_tscheme1 uu____18773  in
                          (uu____18768, rng)  in
                        FStar_Pervasives_Native.Some uu____18759)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18800,uu____18801);
                      FStar_Syntax_Syntax.sigrng = uu____18802;
                      FStar_Syntax_Syntax.sigquals = uu____18803;
                      FStar_Syntax_Syntax.sigmeta = uu____18804;
                      FStar_Syntax_Syntax.sigattrs = uu____18805;
                      FStar_Syntax_Syntax.sigopts = uu____18806;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18850 =
                          let uu____18859 = inst_tscheme_with (uvs, k) us  in
                          (uu____18859, rng)  in
                        FStar_Pervasives_Native.Some uu____18850
                    | uu____18880 ->
                        let uu____18881 =
                          let uu____18890 =
                            let uu____18895 =
                              let uu____18896 =
                                let uu____18899 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18899
                                 in
                              (uvs, uu____18896)  in
                            inst_tscheme_with uu____18895 us  in
                          (uu____18890, rng)  in
                        FStar_Pervasives_Native.Some uu____18881)
               | FStar_Util.Inr se ->
                   let uu____18935 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18956;
                          FStar_Syntax_Syntax.sigrng = uu____18957;
                          FStar_Syntax_Syntax.sigquals = uu____18958;
                          FStar_Syntax_Syntax.sigmeta = uu____18959;
                          FStar_Syntax_Syntax.sigattrs = uu____18960;
                          FStar_Syntax_Syntax.sigopts = uu____18961;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18978 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____18935
                     (FStar_Util.map_option
                        (fun uu____19026  ->
                           match uu____19026 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____19057 =
          let uu____19068 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____19068 mapper  in
        match uu____19057 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19142 =
              let uu____19153 =
                let uu____19160 =
                  let uu___855_19163 = t  in
                  let uu____19164 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___855_19163.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19164;
                    FStar_Syntax_Syntax.vars =
                      (uu___855_19163.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19160)  in
              (uu____19153, r)  in
            FStar_Pervasives_Native.Some uu____19142
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19213 = lookup_qname env1 l  in
      match uu____19213 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19234 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19288 = try_lookup_bv env1 bv  in
      match uu____19288 with
      | FStar_Pervasives_Native.None  ->
          let uu____19303 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19303 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19319 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19320 =
            let uu____19321 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19321  in
          (uu____19319, uu____19320)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19343 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19343 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19409 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19409  in
          let uu____19410 =
            let uu____19419 =
              let uu____19424 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19424)  in
            (uu____19419, r1)  in
          FStar_Pervasives_Native.Some uu____19410
  
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
        let uu____19459 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19459 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19492,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19517 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19517  in
            let uu____19518 =
              let uu____19523 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19523, r1)  in
            FStar_Pervasives_Native.Some uu____19518
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19547 = try_lookup_lid env1 l  in
      match uu____19547 with
      | FStar_Pervasives_Native.None  ->
          let uu____19574 = name_not_found l  in
          let uu____19580 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19574 uu____19580
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19625  ->
              match uu___5_19625 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19628 = FStar_Ident.text_of_id x  in
                  let uu____19630 = FStar_Ident.text_of_id y  in
                  uu____19628 = uu____19630
              | uu____19633 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19654 = lookup_qname env1 lid  in
      match uu____19654 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19663,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19666;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19668;
              FStar_Syntax_Syntax.sigattrs = uu____19669;
              FStar_Syntax_Syntax.sigopts = uu____19670;_},FStar_Pervasives_Native.None
            ),uu____19671)
          ->
          let uu____19722 =
            let uu____19729 =
              let uu____19730 =
                let uu____19733 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19733 t  in
              (uvs, uu____19730)  in
            (uu____19729, q)  in
          FStar_Pervasives_Native.Some uu____19722
      | uu____19746 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19768 = lookup_qname env1 lid  in
      match uu____19768 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19773,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19776;
              FStar_Syntax_Syntax.sigquals = uu____19777;
              FStar_Syntax_Syntax.sigmeta = uu____19778;
              FStar_Syntax_Syntax.sigattrs = uu____19779;
              FStar_Syntax_Syntax.sigopts = uu____19780;_},FStar_Pervasives_Native.None
            ),uu____19781)
          ->
          let uu____19832 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19832 (uvs, t)
      | uu____19837 ->
          let uu____19838 = name_not_found lid  in
          let uu____19844 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19838 uu____19844
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19864 = lookup_qname env1 lid  in
      match uu____19864 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19869,uvs,t,uu____19872,uu____19873,uu____19874);
              FStar_Syntax_Syntax.sigrng = uu____19875;
              FStar_Syntax_Syntax.sigquals = uu____19876;
              FStar_Syntax_Syntax.sigmeta = uu____19877;
              FStar_Syntax_Syntax.sigattrs = uu____19878;
              FStar_Syntax_Syntax.sigopts = uu____19879;_},FStar_Pervasives_Native.None
            ),uu____19880)
          ->
          let uu____19937 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19937 (uvs, t)
      | uu____19942 ->
          let uu____19943 = name_not_found lid  in
          let uu____19949 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19943 uu____19949
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____19972 = lookup_qname env1 lid  in
      match uu____19972 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19980,uu____19981,uu____19982,uu____19983,uu____19984,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19986;
              FStar_Syntax_Syntax.sigquals = uu____19987;
              FStar_Syntax_Syntax.sigmeta = uu____19988;
              FStar_Syntax_Syntax.sigattrs = uu____19989;
              FStar_Syntax_Syntax.sigopts = uu____19990;_},uu____19991),uu____19992)
          -> (true, dcs)
      | uu____20057 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____20073 = lookup_qname env1 lid  in
      match uu____20073 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20074,uu____20075,uu____20076,l,uu____20078,uu____20079);
              FStar_Syntax_Syntax.sigrng = uu____20080;
              FStar_Syntax_Syntax.sigquals = uu____20081;
              FStar_Syntax_Syntax.sigmeta = uu____20082;
              FStar_Syntax_Syntax.sigattrs = uu____20083;
              FStar_Syntax_Syntax.sigopts = uu____20084;_},uu____20085),uu____20086)
          -> l
      | uu____20145 ->
          let uu____20146 =
            let uu____20148 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20148  in
          failwith uu____20146
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20218)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20275) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20299 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20299
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20334 -> FStar_Pervasives_Native.None)
          | uu____20343 -> FStar_Pervasives_Native.None
  
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
        let uu____20405 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20405
  
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
        let uu____20438 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20438
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20462 =
        let uu____20464 = FStar_Ident.nsstr lid  in uu____20464 = "Prims"  in
      if uu____20462
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20494,uu____20495) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20544),uu____20545) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20594 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20612 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20622 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20639 ->
                  let uu____20646 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20646
              | FStar_Syntax_Syntax.Sig_let ((uu____20647,lbs),uu____20649)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20665 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20665
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20672 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20688 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____20698 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20705 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20706 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20707 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20720 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20721 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20744 =
        let uu____20746 = FStar_Ident.nsstr lid  in uu____20746 = "Prims"  in
      if uu____20744
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20753 =
           let uu____20756 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20756
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20753
           (fun d_opt  ->
              let uu____20768 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20768
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20778 =
                   let uu____20781 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20781  in
                 match uu____20778 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20782 =
                       let uu____20784 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20784
                        in
                     failwith uu____20782
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20789 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20789
                       then
                         let uu____20792 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20794 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20796 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20792 uu____20794 uu____20796
                       else ());
                      (let uu____20802 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20802 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20823),uu____20824) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20873 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20895),uu____20896) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20945 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20967 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20967
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21000 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____21000 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____21022 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____21031 =
                        let uu____21032 = FStar_Syntax_Util.un_uinst tm  in
                        uu____21032.FStar_Syntax_Syntax.n  in
                      match uu____21031 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____21037 -> false))
               in
            (true, uu____21022)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____21060 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____21060
  
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
          let uu____21132 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____21132  in
        let uu____21133 = FStar_Util.smap_try_find tab s  in
        match uu____21133 with
        | FStar_Pervasives_Native.None  ->
            let uu____21136 = f ()  in
            (match uu____21136 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21174 =
        let uu____21175 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21175 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21209 =
        let uu____21210 = FStar_Syntax_Util.unrefine t  in
        uu____21210.FStar_Syntax_Syntax.n  in
      match uu____21209 with
      | FStar_Syntax_Syntax.Tm_type uu____21214 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21218) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21244) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21249,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21271 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21304 =
        let attrs =
          let uu____21310 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21310  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21350 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21350)
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
      let uu____21395 = lookup_qname env1 ftv  in
      match uu____21395 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21399) ->
          let uu____21444 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21444 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21465,t),r) ->
               let uu____21480 =
                 let uu____21481 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21481 t  in
               FStar_Pervasives_Native.Some uu____21480)
      | uu____21482 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21494 = try_lookup_effect_lid env1 ftv  in
      match uu____21494 with
      | FStar_Pervasives_Native.None  ->
          let uu____21497 = name_not_found ftv  in
          let uu____21503 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21497 uu____21503
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
        let uu____21527 = lookup_qname env1 lid0  in
        match uu____21527 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21538);
                FStar_Syntax_Syntax.sigrng = uu____21539;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21541;
                FStar_Syntax_Syntax.sigattrs = uu____21542;
                FStar_Syntax_Syntax.sigopts = uu____21543;_},FStar_Pervasives_Native.None
              ),uu____21544)
            ->
            let lid1 =
              let uu____21600 =
                let uu____21601 = FStar_Ident.range_of_lid lid  in
                let uu____21602 =
                  let uu____21603 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21603  in
                FStar_Range.set_use_range uu____21601 uu____21602  in
              FStar_Ident.set_lid_range lid uu____21600  in
            let uu____21604 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21610  ->
                      match uu___6_21610 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21613 -> false))
               in
            if uu____21604
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21632 =
                      let uu____21634 =
                        let uu____21636 = get_range env1  in
                        FStar_Range.string_of_range uu____21636  in
                      let uu____21637 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21639 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21634 uu____21637 uu____21639
                       in
                    failwith uu____21632)
                  in
               match (binders, univs) with
               | ([],uu____21660) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21686,uu____21687::uu____21688::uu____21689) ->
                   let uu____21710 =
                     let uu____21712 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21714 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21712 uu____21714
                      in
                   failwith uu____21710
               | uu____21725 ->
                   let uu____21740 =
                     let uu____21745 =
                       let uu____21746 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21746)  in
                     inst_tscheme_with uu____21745 insts  in
                   (match uu____21740 with
                    | (uu____21759,t) ->
                        let t1 =
                          let uu____21762 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21762 t  in
                        let uu____21763 =
                          let uu____21764 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21764.FStar_Syntax_Syntax.n  in
                        (match uu____21763 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21799 -> failwith "Impossible")))
        | uu____21807 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21831 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21831 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21844,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21851 = find l2  in
            (match uu____21851 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21858 =
          let uu____21861 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____21861  in
        match uu____21858 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21864 = find l  in
            (match uu____21864 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____21869 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____21869
                     m);
                  m))
         in
      let uu____21871 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21871
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21892 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____21892 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21898) ->
            FStar_List.length bs
        | uu____21937 ->
            let uu____21938 =
              let uu____21944 =
                let uu____21946 = FStar_Ident.string_of_lid name  in
                let uu____21948 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21946 uu____21948
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21944)
               in
            FStar_Errors.raise_error uu____21938 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____21967 = lookup_qname env1 l1  in
      match uu____21967 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21970;
              FStar_Syntax_Syntax.sigrng = uu____21971;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21973;
              FStar_Syntax_Syntax.sigattrs = uu____21974;
              FStar_Syntax_Syntax.sigopts = uu____21975;_},uu____21976),uu____21977)
          -> q
      | uu____22030 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____22054 =
          let uu____22055 =
            let uu____22057 = FStar_Util.string_of_int i  in
            let uu____22059 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____22057 uu____22059
             in
          failwith uu____22055  in
        let uu____22062 = lookup_datacon env1 lid  in
        match uu____22062 with
        | (uu____22067,t) ->
            let uu____22069 =
              let uu____22070 = FStar_Syntax_Subst.compress t  in
              uu____22070.FStar_Syntax_Syntax.n  in
            (match uu____22069 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____22074) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____22120 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22134 = lookup_qname env1 l  in
      match uu____22134 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22136,uu____22137,uu____22138);
              FStar_Syntax_Syntax.sigrng = uu____22139;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22141;
              FStar_Syntax_Syntax.sigattrs = uu____22142;
              FStar_Syntax_Syntax.sigopts = uu____22143;_},uu____22144),uu____22145)
          ->
          FStar_Util.for_some
            (fun uu___7_22200  ->
               match uu___7_22200 with
               | FStar_Syntax_Syntax.Projector uu____22202 -> true
               | uu____22208 -> false) quals
      | uu____22210 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22224 = lookup_qname env1 lid  in
      match uu____22224 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22226,uu____22227,uu____22228,uu____22229,uu____22230,uu____22231);
              FStar_Syntax_Syntax.sigrng = uu____22232;
              FStar_Syntax_Syntax.sigquals = uu____22233;
              FStar_Syntax_Syntax.sigmeta = uu____22234;
              FStar_Syntax_Syntax.sigattrs = uu____22235;
              FStar_Syntax_Syntax.sigopts = uu____22236;_},uu____22237),uu____22238)
          -> true
      | uu____22298 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22312 = lookup_qname env1 lid  in
      match uu____22312 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22314,uu____22315,uu____22316,uu____22317,uu____22318,uu____22319);
              FStar_Syntax_Syntax.sigrng = uu____22320;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22322;
              FStar_Syntax_Syntax.sigattrs = uu____22323;
              FStar_Syntax_Syntax.sigopts = uu____22324;_},uu____22325),uu____22326)
          ->
          FStar_Util.for_some
            (fun uu___8_22389  ->
               match uu___8_22389 with
               | FStar_Syntax_Syntax.RecordType uu____22391 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22401 -> true
               | uu____22411 -> false) quals
      | uu____22413 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22423,uu____22424);
            FStar_Syntax_Syntax.sigrng = uu____22425;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22427;
            FStar_Syntax_Syntax.sigattrs = uu____22428;
            FStar_Syntax_Syntax.sigopts = uu____22429;_},uu____22430),uu____22431)
        ->
        FStar_Util.for_some
          (fun uu___9_22490  ->
             match uu___9_22490 with
             | FStar_Syntax_Syntax.Action uu____22492 -> true
             | uu____22494 -> false) quals
    | uu____22496 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22510 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22510
  
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
      let uu____22527 =
        let uu____22528 = FStar_Syntax_Util.un_uinst head  in
        uu____22528.FStar_Syntax_Syntax.n  in
      match uu____22527 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22534 ->
               true
           | uu____22537 -> false)
      | uu____22539 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22553 = lookup_qname env1 l  in
      match uu____22553 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22556),uu____22557) ->
          FStar_Util.for_some
            (fun uu___10_22605  ->
               match uu___10_22605 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22608 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22610 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22686 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22704) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22722 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22730 ->
                 FStar_Pervasives_Native.Some true
             | uu____22749 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22752 =
        let uu____22756 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22756 mapper  in
      match uu____22752 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22816 = lookup_qname env1 lid  in
      match uu____22816 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22820,uu____22821,tps,uu____22823,uu____22824,uu____22825);
              FStar_Syntax_Syntax.sigrng = uu____22826;
              FStar_Syntax_Syntax.sigquals = uu____22827;
              FStar_Syntax_Syntax.sigmeta = uu____22828;
              FStar_Syntax_Syntax.sigattrs = uu____22829;
              FStar_Syntax_Syntax.sigopts = uu____22830;_},uu____22831),uu____22832)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22900 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22946  ->
              match uu____22946 with
              | (d,uu____22955) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____22971 = effect_decl_opt env1 l  in
      match uu____22971 with
      | FStar_Pervasives_Native.None  ->
          let uu____22986 = name_not_found l  in
          let uu____22992 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22986 uu____22992
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____23020 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____23020 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____23027  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____23041  ->
            fun uu____23042  -> fun e  -> FStar_Util.return_all e))
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
        let uu____23076 = FStar_Ident.lid_equals l1 l2  in
        if uu____23076
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____23095 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____23095
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____23114 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23167  ->
                        match uu____23167 with
                        | (m1,m2,uu____23181,uu____23182,uu____23183) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____23114 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23208,uu____23209,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23257 = join_opt env1 l1 l2  in
        match uu____23257 with
        | FStar_Pervasives_Native.None  ->
            let uu____23278 =
              let uu____23284 =
                let uu____23286 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23288 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23286 uu____23288
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23284)  in
            FStar_Errors.raise_error uu____23278 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23331 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23331
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
  'uuuuuu23351 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23351) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23380 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23406  ->
                match uu____23406 with
                | (d,uu____23413) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23380 with
      | FStar_Pervasives_Native.None  ->
          let uu____23424 =
            let uu____23426 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23426
             in
          failwith uu____23424
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23441 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23441 with
           | (uu____23452,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23470)::(wp,uu____23472)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23528 -> failwith "Impossible"))
  
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
        | uu____23593 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23606 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23606 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23623 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23623 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23648 =
                     let uu____23654 =
                       let uu____23656 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23664 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23675 =
                         let uu____23677 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23677  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23656 uu____23664 uu____23675
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23654)
                      in
                   FStar_Errors.raise_error uu____23648
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23685 =
                     let uu____23696 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23696 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23733  ->
                        fun uu____23734  ->
                          match (uu____23733, uu____23734) with
                          | ((x,uu____23764),(t,uu____23766)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23685
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23797 =
                     let uu___1609_23798 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1609_23798.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1609_23798.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1609_23798.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1609_23798.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23797
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23810 .
    'uuuuuu23810 ->
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
            let uu____23851 =
              let uu____23858 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____23858)  in
            match uu____23851 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23882 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23884 = FStar_Util.string_of_int given  in
                     let uu____23886 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23882 uu____23884 uu____23886
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23891 = effect_decl_opt env1 effect_name  in
          match uu____23891 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23913) ->
              let uu____23924 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23924 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23942 =
                       let uu____23945 = get_range env1  in
                       let uu____23946 =
                         let uu____23953 =
                           let uu____23954 =
                             let uu____23971 =
                               let uu____23982 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23982 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23971)  in
                           FStar_Syntax_Syntax.Tm_app uu____23954  in
                         FStar_Syntax_Syntax.mk uu____23953  in
                       uu____23946 FStar_Pervasives_Native.None uu____23945
                        in
                     FStar_Pervasives_Native.Some uu____23942)))
  
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
           (fun uu___11_24082  ->
              match uu___11_24082 with
              | FStar_Syntax_Syntax.Reflectable uu____24084 -> true
              | uu____24086 -> false))
  
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
      | uu____24146 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24161 =
        let uu____24162 = FStar_Syntax_Subst.compress t  in
        uu____24162.FStar_Syntax_Syntax.n  in
      match uu____24161 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24166,c) ->
          is_reifiable_comp env1 c
      | uu____24188 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24208 =
           let uu____24210 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24210  in
         if uu____24208
         then
           let uu____24213 =
             let uu____24219 =
               let uu____24221 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24221
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24219)  in
           let uu____24225 = get_range env1  in
           FStar_Errors.raise_error uu____24213 uu____24225
         else ());
        (let uu____24228 = effect_repr_aux true env1 c u_c  in
         match uu____24228 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1686_24264 = env1  in
        {
          solver = (uu___1686_24264.solver);
          range = (uu___1686_24264.range);
          curmodule = (uu___1686_24264.curmodule);
          gamma = (uu___1686_24264.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1686_24264.gamma_cache);
          modules = (uu___1686_24264.modules);
          expected_typ = (uu___1686_24264.expected_typ);
          sigtab = (uu___1686_24264.sigtab);
          attrtab = (uu___1686_24264.attrtab);
          instantiate_imp = (uu___1686_24264.instantiate_imp);
          effects = (uu___1686_24264.effects);
          generalize = (uu___1686_24264.generalize);
          letrecs = (uu___1686_24264.letrecs);
          top_level = (uu___1686_24264.top_level);
          check_uvars = (uu___1686_24264.check_uvars);
          use_eq = (uu___1686_24264.use_eq);
          use_eq_strict = (uu___1686_24264.use_eq_strict);
          is_iface = (uu___1686_24264.is_iface);
          admit = (uu___1686_24264.admit);
          lax = (uu___1686_24264.lax);
          lax_universes = (uu___1686_24264.lax_universes);
          phase1 = (uu___1686_24264.phase1);
          failhard = (uu___1686_24264.failhard);
          nosynth = (uu___1686_24264.nosynth);
          uvar_subtyping = (uu___1686_24264.uvar_subtyping);
          tc_term = (uu___1686_24264.tc_term);
          type_of = (uu___1686_24264.type_of);
          universe_of = (uu___1686_24264.universe_of);
          check_type_of = (uu___1686_24264.check_type_of);
          use_bv_sorts = (uu___1686_24264.use_bv_sorts);
          qtbl_name_and_index = (uu___1686_24264.qtbl_name_and_index);
          normalized_eff_names = (uu___1686_24264.normalized_eff_names);
          fv_delta_depths = (uu___1686_24264.fv_delta_depths);
          proof_ns = (uu___1686_24264.proof_ns);
          synth_hook = (uu___1686_24264.synth_hook);
          try_solve_implicits_hook =
            (uu___1686_24264.try_solve_implicits_hook);
          splice = (uu___1686_24264.splice);
          mpreprocess = (uu___1686_24264.mpreprocess);
          postprocess = (uu___1686_24264.postprocess);
          identifier_info = (uu___1686_24264.identifier_info);
          tc_hooks = (uu___1686_24264.tc_hooks);
          dsenv = (uu___1686_24264.dsenv);
          nbe = (uu___1686_24264.nbe);
          strict_args_tab = (uu___1686_24264.strict_args_tab);
          erasable_types_tab = (uu___1686_24264.erasable_types_tab)
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
    fun uu____24283  ->
      match uu____24283 with
      | (ed,quals) ->
          let effects1 =
            let uu___1695_24297 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1695_24297.order);
              joins = (uu___1695_24297.joins);
              polymonadic_binds = (uu___1695_24297.polymonadic_binds)
            }  in
          let uu___1698_24306 = env1  in
          {
            solver = (uu___1698_24306.solver);
            range = (uu___1698_24306.range);
            curmodule = (uu___1698_24306.curmodule);
            gamma = (uu___1698_24306.gamma);
            gamma_sig = (uu___1698_24306.gamma_sig);
            gamma_cache = (uu___1698_24306.gamma_cache);
            modules = (uu___1698_24306.modules);
            expected_typ = (uu___1698_24306.expected_typ);
            sigtab = (uu___1698_24306.sigtab);
            attrtab = (uu___1698_24306.attrtab);
            instantiate_imp = (uu___1698_24306.instantiate_imp);
            effects = effects1;
            generalize = (uu___1698_24306.generalize);
            letrecs = (uu___1698_24306.letrecs);
            top_level = (uu___1698_24306.top_level);
            check_uvars = (uu___1698_24306.check_uvars);
            use_eq = (uu___1698_24306.use_eq);
            use_eq_strict = (uu___1698_24306.use_eq_strict);
            is_iface = (uu___1698_24306.is_iface);
            admit = (uu___1698_24306.admit);
            lax = (uu___1698_24306.lax);
            lax_universes = (uu___1698_24306.lax_universes);
            phase1 = (uu___1698_24306.phase1);
            failhard = (uu___1698_24306.failhard);
            nosynth = (uu___1698_24306.nosynth);
            uvar_subtyping = (uu___1698_24306.uvar_subtyping);
            tc_term = (uu___1698_24306.tc_term);
            type_of = (uu___1698_24306.type_of);
            universe_of = (uu___1698_24306.universe_of);
            check_type_of = (uu___1698_24306.check_type_of);
            use_bv_sorts = (uu___1698_24306.use_bv_sorts);
            qtbl_name_and_index = (uu___1698_24306.qtbl_name_and_index);
            normalized_eff_names = (uu___1698_24306.normalized_eff_names);
            fv_delta_depths = (uu___1698_24306.fv_delta_depths);
            proof_ns = (uu___1698_24306.proof_ns);
            synth_hook = (uu___1698_24306.synth_hook);
            try_solve_implicits_hook =
              (uu___1698_24306.try_solve_implicits_hook);
            splice = (uu___1698_24306.splice);
            mpreprocess = (uu___1698_24306.mpreprocess);
            postprocess = (uu___1698_24306.postprocess);
            identifier_info = (uu___1698_24306.identifier_info);
            tc_hooks = (uu___1698_24306.tc_hooks);
            dsenv = (uu___1698_24306.dsenv);
            nbe = (uu___1698_24306.nbe);
            strict_args_tab = (uu___1698_24306.strict_args_tab);
            erasable_types_tab = (uu___1698_24306.erasable_types_tab)
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
        let uu____24335 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24403  ->
                  match uu____24403 with
                  | (m1,n1,uu____24421,uu____24422) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24335 with
        | FStar_Pervasives_Native.Some (uu____24447,uu____24448,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24493 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24568 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24568
                  (fun uu____24589  ->
                     match uu____24589 with
                     | (c1,g1) ->
                         let uu____24600 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24600
                           (fun uu____24621  ->
                              match uu____24621 with
                              | (c2,g2) ->
                                  let uu____24632 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24632)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24754 = l1 u t e  in
                              l2 u t uu____24754))
                | uu____24755 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24823  ->
                    match uu____24823 with
                    | (e,uu____24831) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24854 =
            match uu____24854 with
            | (i,j) ->
                let uu____24865 = FStar_Ident.lid_equals i j  in
                if uu____24865
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____24872  ->
                       FStar_Pervasives_Native.Some uu____24872)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24901 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24911 = FStar_Ident.lid_equals i k  in
                        if uu____24911
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24925 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24925
                                  then []
                                  else
                                    (let uu____24932 =
                                       let uu____24941 =
                                         find_edge order1 (i, k)  in
                                       let uu____24944 =
                                         find_edge order1 (k, j)  in
                                       (uu____24941, uu____24944)  in
                                     match uu____24932 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24959 =
                                           compose_edges e1 e2  in
                                         [uu____24959]
                                     | uu____24960 -> [])))))
                 in
              FStar_List.append order1 uu____24901  in
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
                  let uu____24990 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24993 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____24993
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24990
                  then
                    let uu____25000 =
                      let uu____25006 =
                        let uu____25008 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____25008
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____25006)
                       in
                    let uu____25012 = get_range env1  in
                    FStar_Errors.raise_error uu____25000 uu____25012
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____25090 = FStar_Ident.lid_equals i j
                                  in
                               if uu____25090
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25142 =
                                             let uu____25151 =
                                               find_edge order2 (i, k)  in
                                             let uu____25154 =
                                               find_edge order2 (j, k)  in
                                             (uu____25151, uu____25154)  in
                                           match uu____25142 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25196,uu____25197)
                                                    ->
                                                    let uu____25204 =
                                                      let uu____25211 =
                                                        let uu____25213 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25213
                                                         in
                                                      let uu____25216 =
                                                        let uu____25218 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25218
                                                         in
                                                      (uu____25211,
                                                        uu____25216)
                                                       in
                                                    (match uu____25204 with
                                                     | (true ,true ) ->
                                                         let uu____25235 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25235
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
                                           | uu____25278 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25330 =
                                   let uu____25332 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25332
                                     FStar_Util.is_some
                                    in
                                 if uu____25330
                                 then
                                   let uu____25381 =
                                     let uu____25387 =
                                       let uu____25389 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25391 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25393 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25395 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25389 uu____25391 uu____25393
                                         uu____25395
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25387)
                                      in
                                   FStar_Errors.raise_error uu____25381
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1819_25434 = env1.effects  in
             {
               decls = (uu___1819_25434.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1819_25434.polymonadic_binds)
             }  in
           let uu___1822_25435 = env1  in
           {
             solver = (uu___1822_25435.solver);
             range = (uu___1822_25435.range);
             curmodule = (uu___1822_25435.curmodule);
             gamma = (uu___1822_25435.gamma);
             gamma_sig = (uu___1822_25435.gamma_sig);
             gamma_cache = (uu___1822_25435.gamma_cache);
             modules = (uu___1822_25435.modules);
             expected_typ = (uu___1822_25435.expected_typ);
             sigtab = (uu___1822_25435.sigtab);
             attrtab = (uu___1822_25435.attrtab);
             instantiate_imp = (uu___1822_25435.instantiate_imp);
             effects = effects1;
             generalize = (uu___1822_25435.generalize);
             letrecs = (uu___1822_25435.letrecs);
             top_level = (uu___1822_25435.top_level);
             check_uvars = (uu___1822_25435.check_uvars);
             use_eq = (uu___1822_25435.use_eq);
             use_eq_strict = (uu___1822_25435.use_eq_strict);
             is_iface = (uu___1822_25435.is_iface);
             admit = (uu___1822_25435.admit);
             lax = (uu___1822_25435.lax);
             lax_universes = (uu___1822_25435.lax_universes);
             phase1 = (uu___1822_25435.phase1);
             failhard = (uu___1822_25435.failhard);
             nosynth = (uu___1822_25435.nosynth);
             uvar_subtyping = (uu___1822_25435.uvar_subtyping);
             tc_term = (uu___1822_25435.tc_term);
             type_of = (uu___1822_25435.type_of);
             universe_of = (uu___1822_25435.universe_of);
             check_type_of = (uu___1822_25435.check_type_of);
             use_bv_sorts = (uu___1822_25435.use_bv_sorts);
             qtbl_name_and_index = (uu___1822_25435.qtbl_name_and_index);
             normalized_eff_names = (uu___1822_25435.normalized_eff_names);
             fv_delta_depths = (uu___1822_25435.fv_delta_depths);
             proof_ns = (uu___1822_25435.proof_ns);
             synth_hook = (uu___1822_25435.synth_hook);
             try_solve_implicits_hook =
               (uu___1822_25435.try_solve_implicits_hook);
             splice = (uu___1822_25435.splice);
             mpreprocess = (uu___1822_25435.mpreprocess);
             postprocess = (uu___1822_25435.postprocess);
             identifier_info = (uu___1822_25435.identifier_info);
             tc_hooks = (uu___1822_25435.tc_hooks);
             dsenv = (uu___1822_25435.dsenv);
             nbe = (uu___1822_25435.nbe);
             strict_args_tab = (uu___1822_25435.strict_args_tab);
             erasable_types_tab = (uu___1822_25435.erasable_types_tab)
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
              let uu____25483 = FStar_Ident.string_of_lid m  in
              let uu____25485 = FStar_Ident.string_of_lid n  in
              let uu____25487 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25483 uu____25485 uu____25487
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25496 =
              let uu____25498 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25498 FStar_Util.is_some  in
            if uu____25496
            then
              let uu____25535 =
                let uu____25541 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25541)
                 in
              FStar_Errors.raise_error uu____25535 env1.range
            else
              (let uu____25547 =
                 let uu____25549 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25549 FStar_Util.is_some  in
               if uu____25547
               then
                 let uu____25574 =
                   let uu____25580 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25580)
                    in
                 FStar_Errors.raise_error uu____25574 env1.range
               else
                 (let uu___1837_25586 = env1  in
                  {
                    solver = (uu___1837_25586.solver);
                    range = (uu___1837_25586.range);
                    curmodule = (uu___1837_25586.curmodule);
                    gamma = (uu___1837_25586.gamma);
                    gamma_sig = (uu___1837_25586.gamma_sig);
                    gamma_cache = (uu___1837_25586.gamma_cache);
                    modules = (uu___1837_25586.modules);
                    expected_typ = (uu___1837_25586.expected_typ);
                    sigtab = (uu___1837_25586.sigtab);
                    attrtab = (uu___1837_25586.attrtab);
                    instantiate_imp = (uu___1837_25586.instantiate_imp);
                    effects =
                      (let uu___1839_25588 = env1.effects  in
                       {
                         decls = (uu___1839_25588.decls);
                         order = (uu___1839_25588.order);
                         joins = (uu___1839_25588.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1837_25586.generalize);
                    letrecs = (uu___1837_25586.letrecs);
                    top_level = (uu___1837_25586.top_level);
                    check_uvars = (uu___1837_25586.check_uvars);
                    use_eq = (uu___1837_25586.use_eq);
                    use_eq_strict = (uu___1837_25586.use_eq_strict);
                    is_iface = (uu___1837_25586.is_iface);
                    admit = (uu___1837_25586.admit);
                    lax = (uu___1837_25586.lax);
                    lax_universes = (uu___1837_25586.lax_universes);
                    phase1 = (uu___1837_25586.phase1);
                    failhard = (uu___1837_25586.failhard);
                    nosynth = (uu___1837_25586.nosynth);
                    uvar_subtyping = (uu___1837_25586.uvar_subtyping);
                    tc_term = (uu___1837_25586.tc_term);
                    type_of = (uu___1837_25586.type_of);
                    universe_of = (uu___1837_25586.universe_of);
                    check_type_of = (uu___1837_25586.check_type_of);
                    use_bv_sorts = (uu___1837_25586.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1837_25586.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1837_25586.normalized_eff_names);
                    fv_delta_depths = (uu___1837_25586.fv_delta_depths);
                    proof_ns = (uu___1837_25586.proof_ns);
                    synth_hook = (uu___1837_25586.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1837_25586.try_solve_implicits_hook);
                    splice = (uu___1837_25586.splice);
                    mpreprocess = (uu___1837_25586.mpreprocess);
                    postprocess = (uu___1837_25586.postprocess);
                    identifier_info = (uu___1837_25586.identifier_info);
                    tc_hooks = (uu___1837_25586.tc_hooks);
                    dsenv = (uu___1837_25586.dsenv);
                    nbe = (uu___1837_25586.nbe);
                    strict_args_tab = (uu___1837_25586.strict_args_tab);
                    erasable_types_tab = (uu___1837_25586.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1843_25660 = env1  in
      {
        solver = (uu___1843_25660.solver);
        range = (uu___1843_25660.range);
        curmodule = (uu___1843_25660.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1843_25660.gamma_sig);
        gamma_cache = (uu___1843_25660.gamma_cache);
        modules = (uu___1843_25660.modules);
        expected_typ = (uu___1843_25660.expected_typ);
        sigtab = (uu___1843_25660.sigtab);
        attrtab = (uu___1843_25660.attrtab);
        instantiate_imp = (uu___1843_25660.instantiate_imp);
        effects = (uu___1843_25660.effects);
        generalize = (uu___1843_25660.generalize);
        letrecs = (uu___1843_25660.letrecs);
        top_level = (uu___1843_25660.top_level);
        check_uvars = (uu___1843_25660.check_uvars);
        use_eq = (uu___1843_25660.use_eq);
        use_eq_strict = (uu___1843_25660.use_eq_strict);
        is_iface = (uu___1843_25660.is_iface);
        admit = (uu___1843_25660.admit);
        lax = (uu___1843_25660.lax);
        lax_universes = (uu___1843_25660.lax_universes);
        phase1 = (uu___1843_25660.phase1);
        failhard = (uu___1843_25660.failhard);
        nosynth = (uu___1843_25660.nosynth);
        uvar_subtyping = (uu___1843_25660.uvar_subtyping);
        tc_term = (uu___1843_25660.tc_term);
        type_of = (uu___1843_25660.type_of);
        universe_of = (uu___1843_25660.universe_of);
        check_type_of = (uu___1843_25660.check_type_of);
        use_bv_sorts = (uu___1843_25660.use_bv_sorts);
        qtbl_name_and_index = (uu___1843_25660.qtbl_name_and_index);
        normalized_eff_names = (uu___1843_25660.normalized_eff_names);
        fv_delta_depths = (uu___1843_25660.fv_delta_depths);
        proof_ns = (uu___1843_25660.proof_ns);
        synth_hook = (uu___1843_25660.synth_hook);
        try_solve_implicits_hook = (uu___1843_25660.try_solve_implicits_hook);
        splice = (uu___1843_25660.splice);
        mpreprocess = (uu___1843_25660.mpreprocess);
        postprocess = (uu___1843_25660.postprocess);
        identifier_info = (uu___1843_25660.identifier_info);
        tc_hooks = (uu___1843_25660.tc_hooks);
        dsenv = (uu___1843_25660.dsenv);
        nbe = (uu___1843_25660.nbe);
        strict_args_tab = (uu___1843_25660.strict_args_tab);
        erasable_types_tab = (uu___1843_25660.erasable_types_tab)
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
            (let uu___1856_25718 = env1  in
             {
               solver = (uu___1856_25718.solver);
               range = (uu___1856_25718.range);
               curmodule = (uu___1856_25718.curmodule);
               gamma = rest;
               gamma_sig = (uu___1856_25718.gamma_sig);
               gamma_cache = (uu___1856_25718.gamma_cache);
               modules = (uu___1856_25718.modules);
               expected_typ = (uu___1856_25718.expected_typ);
               sigtab = (uu___1856_25718.sigtab);
               attrtab = (uu___1856_25718.attrtab);
               instantiate_imp = (uu___1856_25718.instantiate_imp);
               effects = (uu___1856_25718.effects);
               generalize = (uu___1856_25718.generalize);
               letrecs = (uu___1856_25718.letrecs);
               top_level = (uu___1856_25718.top_level);
               check_uvars = (uu___1856_25718.check_uvars);
               use_eq = (uu___1856_25718.use_eq);
               use_eq_strict = (uu___1856_25718.use_eq_strict);
               is_iface = (uu___1856_25718.is_iface);
               admit = (uu___1856_25718.admit);
               lax = (uu___1856_25718.lax);
               lax_universes = (uu___1856_25718.lax_universes);
               phase1 = (uu___1856_25718.phase1);
               failhard = (uu___1856_25718.failhard);
               nosynth = (uu___1856_25718.nosynth);
               uvar_subtyping = (uu___1856_25718.uvar_subtyping);
               tc_term = (uu___1856_25718.tc_term);
               type_of = (uu___1856_25718.type_of);
               universe_of = (uu___1856_25718.universe_of);
               check_type_of = (uu___1856_25718.check_type_of);
               use_bv_sorts = (uu___1856_25718.use_bv_sorts);
               qtbl_name_and_index = (uu___1856_25718.qtbl_name_and_index);
               normalized_eff_names = (uu___1856_25718.normalized_eff_names);
               fv_delta_depths = (uu___1856_25718.fv_delta_depths);
               proof_ns = (uu___1856_25718.proof_ns);
               synth_hook = (uu___1856_25718.synth_hook);
               try_solve_implicits_hook =
                 (uu___1856_25718.try_solve_implicits_hook);
               splice = (uu___1856_25718.splice);
               mpreprocess = (uu___1856_25718.mpreprocess);
               postprocess = (uu___1856_25718.postprocess);
               identifier_info = (uu___1856_25718.identifier_info);
               tc_hooks = (uu___1856_25718.tc_hooks);
               dsenv = (uu___1856_25718.dsenv);
               nbe = (uu___1856_25718.nbe);
               strict_args_tab = (uu___1856_25718.strict_args_tab);
               erasable_types_tab = (uu___1856_25718.erasable_types_tab)
             }))
    | uu____25719 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25748  ->
             match uu____25748 with | (x,uu____25756) -> push_bv env2 x) env1
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
            let uu___1870_25791 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1870_25791.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1870_25791.FStar_Syntax_Syntax.index);
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
        let uu____25864 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25864 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____25892 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25892)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1891_25908 = env1  in
      {
        solver = (uu___1891_25908.solver);
        range = (uu___1891_25908.range);
        curmodule = (uu___1891_25908.curmodule);
        gamma = (uu___1891_25908.gamma);
        gamma_sig = (uu___1891_25908.gamma_sig);
        gamma_cache = (uu___1891_25908.gamma_cache);
        modules = (uu___1891_25908.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1891_25908.sigtab);
        attrtab = (uu___1891_25908.attrtab);
        instantiate_imp = (uu___1891_25908.instantiate_imp);
        effects = (uu___1891_25908.effects);
        generalize = (uu___1891_25908.generalize);
        letrecs = (uu___1891_25908.letrecs);
        top_level = (uu___1891_25908.top_level);
        check_uvars = (uu___1891_25908.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1891_25908.use_eq_strict);
        is_iface = (uu___1891_25908.is_iface);
        admit = (uu___1891_25908.admit);
        lax = (uu___1891_25908.lax);
        lax_universes = (uu___1891_25908.lax_universes);
        phase1 = (uu___1891_25908.phase1);
        failhard = (uu___1891_25908.failhard);
        nosynth = (uu___1891_25908.nosynth);
        uvar_subtyping = (uu___1891_25908.uvar_subtyping);
        tc_term = (uu___1891_25908.tc_term);
        type_of = (uu___1891_25908.type_of);
        universe_of = (uu___1891_25908.universe_of);
        check_type_of = (uu___1891_25908.check_type_of);
        use_bv_sorts = (uu___1891_25908.use_bv_sorts);
        qtbl_name_and_index = (uu___1891_25908.qtbl_name_and_index);
        normalized_eff_names = (uu___1891_25908.normalized_eff_names);
        fv_delta_depths = (uu___1891_25908.fv_delta_depths);
        proof_ns = (uu___1891_25908.proof_ns);
        synth_hook = (uu___1891_25908.synth_hook);
        try_solve_implicits_hook = (uu___1891_25908.try_solve_implicits_hook);
        splice = (uu___1891_25908.splice);
        mpreprocess = (uu___1891_25908.mpreprocess);
        postprocess = (uu___1891_25908.postprocess);
        identifier_info = (uu___1891_25908.identifier_info);
        tc_hooks = (uu___1891_25908.tc_hooks);
        dsenv = (uu___1891_25908.dsenv);
        nbe = (uu___1891_25908.nbe);
        strict_args_tab = (uu___1891_25908.strict_args_tab);
        erasable_types_tab = (uu___1891_25908.erasable_types_tab)
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
    let uu____25939 = expected_typ env_  in
    ((let uu___1898_25945 = env_  in
      {
        solver = (uu___1898_25945.solver);
        range = (uu___1898_25945.range);
        curmodule = (uu___1898_25945.curmodule);
        gamma = (uu___1898_25945.gamma);
        gamma_sig = (uu___1898_25945.gamma_sig);
        gamma_cache = (uu___1898_25945.gamma_cache);
        modules = (uu___1898_25945.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1898_25945.sigtab);
        attrtab = (uu___1898_25945.attrtab);
        instantiate_imp = (uu___1898_25945.instantiate_imp);
        effects = (uu___1898_25945.effects);
        generalize = (uu___1898_25945.generalize);
        letrecs = (uu___1898_25945.letrecs);
        top_level = (uu___1898_25945.top_level);
        check_uvars = (uu___1898_25945.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1898_25945.use_eq_strict);
        is_iface = (uu___1898_25945.is_iface);
        admit = (uu___1898_25945.admit);
        lax = (uu___1898_25945.lax);
        lax_universes = (uu___1898_25945.lax_universes);
        phase1 = (uu___1898_25945.phase1);
        failhard = (uu___1898_25945.failhard);
        nosynth = (uu___1898_25945.nosynth);
        uvar_subtyping = (uu___1898_25945.uvar_subtyping);
        tc_term = (uu___1898_25945.tc_term);
        type_of = (uu___1898_25945.type_of);
        universe_of = (uu___1898_25945.universe_of);
        check_type_of = (uu___1898_25945.check_type_of);
        use_bv_sorts = (uu___1898_25945.use_bv_sorts);
        qtbl_name_and_index = (uu___1898_25945.qtbl_name_and_index);
        normalized_eff_names = (uu___1898_25945.normalized_eff_names);
        fv_delta_depths = (uu___1898_25945.fv_delta_depths);
        proof_ns = (uu___1898_25945.proof_ns);
        synth_hook = (uu___1898_25945.synth_hook);
        try_solve_implicits_hook = (uu___1898_25945.try_solve_implicits_hook);
        splice = (uu___1898_25945.splice);
        mpreprocess = (uu___1898_25945.mpreprocess);
        postprocess = (uu___1898_25945.postprocess);
        identifier_info = (uu___1898_25945.identifier_info);
        tc_hooks = (uu___1898_25945.tc_hooks);
        dsenv = (uu___1898_25945.dsenv);
        nbe = (uu___1898_25945.nbe);
        strict_args_tab = (uu___1898_25945.strict_args_tab);
        erasable_types_tab = (uu___1898_25945.erasable_types_tab)
      }), uu____25939)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25957 =
      let uu____25958 = FStar_Ident.id_of_text ""  in [uu____25958]  in
    FStar_Ident.lid_of_ids uu____25957  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____25965 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25965
        then
          let uu____25970 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25970 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1906_25998 = env1  in
       {
         solver = (uu___1906_25998.solver);
         range = (uu___1906_25998.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1906_25998.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1906_25998.expected_typ);
         sigtab = (uu___1906_25998.sigtab);
         attrtab = (uu___1906_25998.attrtab);
         instantiate_imp = (uu___1906_25998.instantiate_imp);
         effects = (uu___1906_25998.effects);
         generalize = (uu___1906_25998.generalize);
         letrecs = (uu___1906_25998.letrecs);
         top_level = (uu___1906_25998.top_level);
         check_uvars = (uu___1906_25998.check_uvars);
         use_eq = (uu___1906_25998.use_eq);
         use_eq_strict = (uu___1906_25998.use_eq_strict);
         is_iface = (uu___1906_25998.is_iface);
         admit = (uu___1906_25998.admit);
         lax = (uu___1906_25998.lax);
         lax_universes = (uu___1906_25998.lax_universes);
         phase1 = (uu___1906_25998.phase1);
         failhard = (uu___1906_25998.failhard);
         nosynth = (uu___1906_25998.nosynth);
         uvar_subtyping = (uu___1906_25998.uvar_subtyping);
         tc_term = (uu___1906_25998.tc_term);
         type_of = (uu___1906_25998.type_of);
         universe_of = (uu___1906_25998.universe_of);
         check_type_of = (uu___1906_25998.check_type_of);
         use_bv_sorts = (uu___1906_25998.use_bv_sorts);
         qtbl_name_and_index = (uu___1906_25998.qtbl_name_and_index);
         normalized_eff_names = (uu___1906_25998.normalized_eff_names);
         fv_delta_depths = (uu___1906_25998.fv_delta_depths);
         proof_ns = (uu___1906_25998.proof_ns);
         synth_hook = (uu___1906_25998.synth_hook);
         try_solve_implicits_hook =
           (uu___1906_25998.try_solve_implicits_hook);
         splice = (uu___1906_25998.splice);
         mpreprocess = (uu___1906_25998.mpreprocess);
         postprocess = (uu___1906_25998.postprocess);
         identifier_info = (uu___1906_25998.identifier_info);
         tc_hooks = (uu___1906_25998.tc_hooks);
         dsenv = (uu___1906_25998.dsenv);
         nbe = (uu___1906_25998.nbe);
         strict_args_tab = (uu___1906_25998.strict_args_tab);
         erasable_types_tab = (uu___1906_25998.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26050)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26054,(uu____26055,t)))::tl
          ->
          let uu____26076 =
            let uu____26079 = FStar_Syntax_Free.uvars t  in
            ext out uu____26079  in
          aux uu____26076 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26082;
            FStar_Syntax_Syntax.index = uu____26083;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26091 =
            let uu____26094 = FStar_Syntax_Free.uvars t  in
            ext out uu____26094  in
          aux uu____26091 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26152)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26156,(uu____26157,t)))::tl
          ->
          let uu____26178 =
            let uu____26181 = FStar_Syntax_Free.univs t  in
            ext out uu____26181  in
          aux uu____26178 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26184;
            FStar_Syntax_Syntax.index = uu____26185;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26193 =
            let uu____26196 = FStar_Syntax_Free.univs t  in
            ext out uu____26196  in
          aux uu____26193 tl
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
          let uu____26258 = FStar_Util.set_add uname out  in
          aux uu____26258 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26261,(uu____26262,t)))::tl
          ->
          let uu____26283 =
            let uu____26286 = FStar_Syntax_Free.univnames t  in
            ext out uu____26286  in
          aux uu____26283 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26289;
            FStar_Syntax_Syntax.index = uu____26290;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26298 =
            let uu____26301 = FStar_Syntax_Free.univnames t  in
            ext out uu____26301  in
          aux uu____26298 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26322  ->
            match uu___12_26322 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26326 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26339 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26350 =
      let uu____26359 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26359
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26350 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26407 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26420  ->
              match uu___13_26420 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26423 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26423
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26427 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26427
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26431) ->
                  let uu____26448 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26448))
       in
    FStar_All.pipe_right uu____26407 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26462  ->
    match uu___14_26462 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26468 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26468
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26491  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26546) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26579,uu____26580) -> false  in
      let uu____26594 =
        FStar_List.tryFind
          (fun uu____26616  ->
             match uu____26616 with | (p,uu____26627) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26594 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26646,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26676 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26676
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2049_26698 = e  in
        {
          solver = (uu___2049_26698.solver);
          range = (uu___2049_26698.range);
          curmodule = (uu___2049_26698.curmodule);
          gamma = (uu___2049_26698.gamma);
          gamma_sig = (uu___2049_26698.gamma_sig);
          gamma_cache = (uu___2049_26698.gamma_cache);
          modules = (uu___2049_26698.modules);
          expected_typ = (uu___2049_26698.expected_typ);
          sigtab = (uu___2049_26698.sigtab);
          attrtab = (uu___2049_26698.attrtab);
          instantiate_imp = (uu___2049_26698.instantiate_imp);
          effects = (uu___2049_26698.effects);
          generalize = (uu___2049_26698.generalize);
          letrecs = (uu___2049_26698.letrecs);
          top_level = (uu___2049_26698.top_level);
          check_uvars = (uu___2049_26698.check_uvars);
          use_eq = (uu___2049_26698.use_eq);
          use_eq_strict = (uu___2049_26698.use_eq_strict);
          is_iface = (uu___2049_26698.is_iface);
          admit = (uu___2049_26698.admit);
          lax = (uu___2049_26698.lax);
          lax_universes = (uu___2049_26698.lax_universes);
          phase1 = (uu___2049_26698.phase1);
          failhard = (uu___2049_26698.failhard);
          nosynth = (uu___2049_26698.nosynth);
          uvar_subtyping = (uu___2049_26698.uvar_subtyping);
          tc_term = (uu___2049_26698.tc_term);
          type_of = (uu___2049_26698.type_of);
          universe_of = (uu___2049_26698.universe_of);
          check_type_of = (uu___2049_26698.check_type_of);
          use_bv_sorts = (uu___2049_26698.use_bv_sorts);
          qtbl_name_and_index = (uu___2049_26698.qtbl_name_and_index);
          normalized_eff_names = (uu___2049_26698.normalized_eff_names);
          fv_delta_depths = (uu___2049_26698.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2049_26698.synth_hook);
          try_solve_implicits_hook =
            (uu___2049_26698.try_solve_implicits_hook);
          splice = (uu___2049_26698.splice);
          mpreprocess = (uu___2049_26698.mpreprocess);
          postprocess = (uu___2049_26698.postprocess);
          identifier_info = (uu___2049_26698.identifier_info);
          tc_hooks = (uu___2049_26698.tc_hooks);
          dsenv = (uu___2049_26698.dsenv);
          nbe = (uu___2049_26698.nbe);
          strict_args_tab = (uu___2049_26698.strict_args_tab);
          erasable_types_tab = (uu___2049_26698.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2058_26746 = e  in
      {
        solver = (uu___2058_26746.solver);
        range = (uu___2058_26746.range);
        curmodule = (uu___2058_26746.curmodule);
        gamma = (uu___2058_26746.gamma);
        gamma_sig = (uu___2058_26746.gamma_sig);
        gamma_cache = (uu___2058_26746.gamma_cache);
        modules = (uu___2058_26746.modules);
        expected_typ = (uu___2058_26746.expected_typ);
        sigtab = (uu___2058_26746.sigtab);
        attrtab = (uu___2058_26746.attrtab);
        instantiate_imp = (uu___2058_26746.instantiate_imp);
        effects = (uu___2058_26746.effects);
        generalize = (uu___2058_26746.generalize);
        letrecs = (uu___2058_26746.letrecs);
        top_level = (uu___2058_26746.top_level);
        check_uvars = (uu___2058_26746.check_uvars);
        use_eq = (uu___2058_26746.use_eq);
        use_eq_strict = (uu___2058_26746.use_eq_strict);
        is_iface = (uu___2058_26746.is_iface);
        admit = (uu___2058_26746.admit);
        lax = (uu___2058_26746.lax);
        lax_universes = (uu___2058_26746.lax_universes);
        phase1 = (uu___2058_26746.phase1);
        failhard = (uu___2058_26746.failhard);
        nosynth = (uu___2058_26746.nosynth);
        uvar_subtyping = (uu___2058_26746.uvar_subtyping);
        tc_term = (uu___2058_26746.tc_term);
        type_of = (uu___2058_26746.type_of);
        universe_of = (uu___2058_26746.universe_of);
        check_type_of = (uu___2058_26746.check_type_of);
        use_bv_sorts = (uu___2058_26746.use_bv_sorts);
        qtbl_name_and_index = (uu___2058_26746.qtbl_name_and_index);
        normalized_eff_names = (uu___2058_26746.normalized_eff_names);
        fv_delta_depths = (uu___2058_26746.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2058_26746.synth_hook);
        try_solve_implicits_hook = (uu___2058_26746.try_solve_implicits_hook);
        splice = (uu___2058_26746.splice);
        mpreprocess = (uu___2058_26746.mpreprocess);
        postprocess = (uu___2058_26746.postprocess);
        identifier_info = (uu___2058_26746.identifier_info);
        tc_hooks = (uu___2058_26746.tc_hooks);
        dsenv = (uu___2058_26746.dsenv);
        nbe = (uu___2058_26746.nbe);
        strict_args_tab = (uu___2058_26746.strict_args_tab);
        erasable_types_tab = (uu___2058_26746.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26762 = FStar_Syntax_Free.names t  in
      let uu____26765 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26762 uu____26765
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26788 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26788
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26798 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26798
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____26819 =
      match uu____26819 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26839 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26839)
       in
    let uu____26847 =
      let uu____26851 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____26851 FStar_List.rev  in
    FStar_All.pipe_right uu____26847 (FStar_String.concat " ")
  
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
                  (let uu____26919 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26919 with
                   | FStar_Pervasives_Native.Some uu____26923 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26926 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26936;
        FStar_TypeChecker_Common.univ_ineqs = uu____26937;
        FStar_TypeChecker_Common.implicits = uu____26938;_} -> true
    | uu____26948 -> false
  
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
          let uu___2102_26970 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2102_26970.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2102_26970.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2102_26970.FStar_TypeChecker_Common.implicits)
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
          let uu____27009 = FStar_Options.defensive ()  in
          if uu____27009
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____27015 =
              let uu____27017 =
                let uu____27019 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____27019  in
              Prims.op_Negation uu____27017  in
            (if uu____27015
             then
               let uu____27026 =
                 let uu____27032 =
                   let uu____27034 = FStar_Syntax_Print.term_to_string t  in
                   let uu____27036 =
                     let uu____27038 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____27038
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____27034 uu____27036
                    in
                 (FStar_Errors.Warning_Defensive, uu____27032)  in
               FStar_Errors.log_issue rng uu____27026
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
          let uu____27078 =
            let uu____27080 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27080  in
          if uu____27078
          then ()
          else
            (let uu____27085 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____27085 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____27111 =
            let uu____27113 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____27113  in
          if uu____27111
          then ()
          else
            (let uu____27118 = bound_vars e  in
             def_check_closed_in rng msg uu____27118 t)
  
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
          let uu___2139_27157 = g  in
          let uu____27158 =
            let uu____27159 =
              let uu____27160 =
                let uu____27167 =
                  let uu____27168 =
                    let uu____27185 =
                      let uu____27196 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27196]  in
                    (f, uu____27185)  in
                  FStar_Syntax_Syntax.Tm_app uu____27168  in
                FStar_Syntax_Syntax.mk uu____27167  in
              uu____27160 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27233  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27233) uu____27159
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27158;
            FStar_TypeChecker_Common.deferred =
              (uu___2139_27157.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2139_27157.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2139_27157.FStar_TypeChecker_Common.implicits)
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
          let uu___2146_27251 = g  in
          let uu____27252 =
            let uu____27253 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27253  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27252;
            FStar_TypeChecker_Common.deferred =
              (uu___2146_27251.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2146_27251.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2146_27251.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2151_27270 = g  in
          let uu____27271 =
            let uu____27272 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27272  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27271;
            FStar_TypeChecker_Common.deferred =
              (uu___2151_27270.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2151_27270.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2151_27270.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2155_27274 = g  in
          let uu____27275 =
            let uu____27276 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27276  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27275;
            FStar_TypeChecker_Common.deferred =
              (uu___2155_27274.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2155_27274.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2155_27274.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27283 ->
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
                       let uu____27360 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27360
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2178_27367 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2178_27367.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2178_27367.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2178_27367.FStar_TypeChecker_Common.implicits)
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
               let uu____27401 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27401
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
            let uu___2193_27428 = g  in
            let uu____27429 =
              let uu____27430 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27430  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27429;
              FStar_TypeChecker_Common.deferred =
                (uu___2193_27428.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2193_27428.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2193_27428.FStar_TypeChecker_Common.implicits)
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
              let uu____27488 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27488 with
              | FStar_Pervasives_Native.Some
                  (uu____27513::(tm,uu____27515)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27579 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27597 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27597;
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
                    (let uu____27631 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27631
                     then
                       let uu____27635 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27635
                     else ());
                    (let g =
                       let uu___2217_27641 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2217_27641.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2217_27641.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2217_27641.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27695 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27752  ->
                      fun b  ->
                        match uu____27752 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27794 =
                              let uu____27807 = reason b  in
                              new_implicit_var_aux uu____27807 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27794 with
                             | (t,uu____27824,g_t) ->
                                 let uu____27838 =
                                   let uu____27841 =
                                     let uu____27844 =
                                       let uu____27845 =
                                         let uu____27852 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27852, t)  in
                                       FStar_Syntax_Syntax.NT uu____27845  in
                                     [uu____27844]  in
                                   FStar_List.append substs1 uu____27841  in
                                 let uu____27863 = conj_guard g g_t  in
                                 (uu____27838, (FStar_List.append uvars [t]),
                                   uu____27863))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27695
              (fun uu____27892  ->
                 match uu____27892 with | (uu____27909,uvars,g) -> (uvars, g))
  
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
                let uu____27950 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____27950 FStar_Util.must  in
              let uu____27967 = inst_tscheme_with post_ts [u]  in
              match uu____27967 with
              | (uu____27972,post) ->
                  let uu____27974 =
                    let uu____27979 =
                      let uu____27980 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____27980]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____27979  in
                  uu____27974 FStar_Pervasives_Native.None r
               in
            let uu____28013 =
              let uu____28018 =
                let uu____28019 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____28019]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____28018  in
            uu____28013 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____28055  -> ());
    push = (fun uu____28057  -> ());
    pop = (fun uu____28060  -> ());
    snapshot =
      (fun uu____28063  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____28082  -> fun uu____28083  -> ());
    encode_sig = (fun uu____28098  -> fun uu____28099  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____28105 =
             let uu____28112 = FStar_Options.peek ()  in (e, g, uu____28112)
              in
           [uu____28105]);
    solve = (fun uu____28128  -> fun uu____28129  -> fun uu____28130  -> ());
    finish = (fun uu____28137  -> ());
    refresh = (fun uu____28139  -> ())
  } 