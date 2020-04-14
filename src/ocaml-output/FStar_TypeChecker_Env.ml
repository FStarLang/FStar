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
           (fun uu___0_13896  ->
              match uu___0_13896 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13899 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst uu____13899  in
                  let uu____13900 =
                    let uu____13901 = FStar_Syntax_Subst.compress y  in
                    uu____13901.FStar_Syntax_Syntax.n  in
                  (match uu____13900 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13905 =
                         let uu___324_13906 = y1  in
                         let uu____13907 =
                           FStar_Syntax_Subst.subst subst
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___324_13906.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___324_13906.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13907
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13905
                   | uu____13910 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst  ->
    fun env1  ->
      let uu___330_13924 = env1  in
      let uu____13925 = rename_gamma subst env1.gamma  in
      {
        solver = (uu___330_13924.solver);
        range = (uu___330_13924.range);
        curmodule = (uu___330_13924.curmodule);
        gamma = uu____13925;
        gamma_sig = (uu___330_13924.gamma_sig);
        gamma_cache = (uu___330_13924.gamma_cache);
        modules = (uu___330_13924.modules);
        expected_typ = (uu___330_13924.expected_typ);
        sigtab = (uu___330_13924.sigtab);
        attrtab = (uu___330_13924.attrtab);
        instantiate_imp = (uu___330_13924.instantiate_imp);
        effects = (uu___330_13924.effects);
        generalize = (uu___330_13924.generalize);
        letrecs = (uu___330_13924.letrecs);
        top_level = (uu___330_13924.top_level);
        check_uvars = (uu___330_13924.check_uvars);
        use_eq = (uu___330_13924.use_eq);
        use_eq_strict = (uu___330_13924.use_eq_strict);
        is_iface = (uu___330_13924.is_iface);
        admit = (uu___330_13924.admit);
        lax = (uu___330_13924.lax);
        lax_universes = (uu___330_13924.lax_universes);
        phase1 = (uu___330_13924.phase1);
        failhard = (uu___330_13924.failhard);
        nosynth = (uu___330_13924.nosynth);
        uvar_subtyping = (uu___330_13924.uvar_subtyping);
        tc_term = (uu___330_13924.tc_term);
        type_of = (uu___330_13924.type_of);
        universe_of = (uu___330_13924.universe_of);
        check_type_of = (uu___330_13924.check_type_of);
        use_bv_sorts = (uu___330_13924.use_bv_sorts);
        qtbl_name_and_index = (uu___330_13924.qtbl_name_and_index);
        normalized_eff_names = (uu___330_13924.normalized_eff_names);
        fv_delta_depths = (uu___330_13924.fv_delta_depths);
        proof_ns = (uu___330_13924.proof_ns);
        synth_hook = (uu___330_13924.synth_hook);
        try_solve_implicits_hook = (uu___330_13924.try_solve_implicits_hook);
        splice = (uu___330_13924.splice);
        mpreprocess = (uu___330_13924.mpreprocess);
        postprocess = (uu___330_13924.postprocess);
        identifier_info = (uu___330_13924.identifier_info);
        tc_hooks = (uu___330_13924.tc_hooks);
        dsenv = (uu___330_13924.dsenv);
        nbe = (uu___330_13924.nbe);
        strict_args_tab = (uu___330_13924.strict_args_tab);
        erasable_types_tab = (uu___330_13924.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13933  -> fun uu____13934  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env1  -> env1.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env1  ->
    fun hooks  ->
      let uu___337_13956 = env1  in
      {
        solver = (uu___337_13956.solver);
        range = (uu___337_13956.range);
        curmodule = (uu___337_13956.curmodule);
        gamma = (uu___337_13956.gamma);
        gamma_sig = (uu___337_13956.gamma_sig);
        gamma_cache = (uu___337_13956.gamma_cache);
        modules = (uu___337_13956.modules);
        expected_typ = (uu___337_13956.expected_typ);
        sigtab = (uu___337_13956.sigtab);
        attrtab = (uu___337_13956.attrtab);
        instantiate_imp = (uu___337_13956.instantiate_imp);
        effects = (uu___337_13956.effects);
        generalize = (uu___337_13956.generalize);
        letrecs = (uu___337_13956.letrecs);
        top_level = (uu___337_13956.top_level);
        check_uvars = (uu___337_13956.check_uvars);
        use_eq = (uu___337_13956.use_eq);
        use_eq_strict = (uu___337_13956.use_eq_strict);
        is_iface = (uu___337_13956.is_iface);
        admit = (uu___337_13956.admit);
        lax = (uu___337_13956.lax);
        lax_universes = (uu___337_13956.lax_universes);
        phase1 = (uu___337_13956.phase1);
        failhard = (uu___337_13956.failhard);
        nosynth = (uu___337_13956.nosynth);
        uvar_subtyping = (uu___337_13956.uvar_subtyping);
        tc_term = (uu___337_13956.tc_term);
        type_of = (uu___337_13956.type_of);
        universe_of = (uu___337_13956.universe_of);
        check_type_of = (uu___337_13956.check_type_of);
        use_bv_sorts = (uu___337_13956.use_bv_sorts);
        qtbl_name_and_index = (uu___337_13956.qtbl_name_and_index);
        normalized_eff_names = (uu___337_13956.normalized_eff_names);
        fv_delta_depths = (uu___337_13956.fv_delta_depths);
        proof_ns = (uu___337_13956.proof_ns);
        synth_hook = (uu___337_13956.synth_hook);
        try_solve_implicits_hook = (uu___337_13956.try_solve_implicits_hook);
        splice = (uu___337_13956.splice);
        mpreprocess = (uu___337_13956.mpreprocess);
        postprocess = (uu___337_13956.postprocess);
        identifier_info = (uu___337_13956.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___337_13956.dsenv);
        nbe = (uu___337_13956.nbe);
        strict_args_tab = (uu___337_13956.strict_args_tab);
        erasable_types_tab = (uu___337_13956.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___341_13968 = e  in
      let uu____13969 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___341_13968.solver);
        range = (uu___341_13968.range);
        curmodule = (uu___341_13968.curmodule);
        gamma = (uu___341_13968.gamma);
        gamma_sig = (uu___341_13968.gamma_sig);
        gamma_cache = (uu___341_13968.gamma_cache);
        modules = (uu___341_13968.modules);
        expected_typ = (uu___341_13968.expected_typ);
        sigtab = (uu___341_13968.sigtab);
        attrtab = (uu___341_13968.attrtab);
        instantiate_imp = (uu___341_13968.instantiate_imp);
        effects = (uu___341_13968.effects);
        generalize = (uu___341_13968.generalize);
        letrecs = (uu___341_13968.letrecs);
        top_level = (uu___341_13968.top_level);
        check_uvars = (uu___341_13968.check_uvars);
        use_eq = (uu___341_13968.use_eq);
        use_eq_strict = (uu___341_13968.use_eq_strict);
        is_iface = (uu___341_13968.is_iface);
        admit = (uu___341_13968.admit);
        lax = (uu___341_13968.lax);
        lax_universes = (uu___341_13968.lax_universes);
        phase1 = (uu___341_13968.phase1);
        failhard = (uu___341_13968.failhard);
        nosynth = (uu___341_13968.nosynth);
        uvar_subtyping = (uu___341_13968.uvar_subtyping);
        tc_term = (uu___341_13968.tc_term);
        type_of = (uu___341_13968.type_of);
        universe_of = (uu___341_13968.universe_of);
        check_type_of = (uu___341_13968.check_type_of);
        use_bv_sorts = (uu___341_13968.use_bv_sorts);
        qtbl_name_and_index = (uu___341_13968.qtbl_name_and_index);
        normalized_eff_names = (uu___341_13968.normalized_eff_names);
        fv_delta_depths = (uu___341_13968.fv_delta_depths);
        proof_ns = (uu___341_13968.proof_ns);
        synth_hook = (uu___341_13968.synth_hook);
        try_solve_implicits_hook = (uu___341_13968.try_solve_implicits_hook);
        splice = (uu___341_13968.splice);
        mpreprocess = (uu___341_13968.mpreprocess);
        postprocess = (uu___341_13968.postprocess);
        identifier_info = (uu___341_13968.identifier_info);
        tc_hooks = (uu___341_13968.tc_hooks);
        dsenv = uu____13969;
        nbe = (uu___341_13968.nbe);
        strict_args_tab = (uu___341_13968.strict_args_tab);
        erasable_types_tab = (uu___341_13968.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env1  ->
    ((Prims.op_Negation env1.lax) && (Prims.op_Negation env1.admit)) &&
      (let uu____13986 = FStar_Ident.string_of_lid env1.curmodule  in
       FStar_Options.should_verify uu____13986)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14001) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14004,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14006,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14009 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14023 . unit -> 'uuuuuu14023 FStar_Util.smap =
  fun uu____14030  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14036 . unit -> 'uuuuuu14036 FStar_Util.smap =
  fun uu____14043  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14181 = new_gamma_cache ()  in
                  let uu____14184 = new_sigtab ()  in
                  let uu____14187 = new_sigtab ()  in
                  let uu____14194 =
                    let uu____14209 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14209, FStar_Pervasives_Native.None)  in
                  let uu____14230 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14234 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14238 = FStar_Options.using_facts_from ()  in
                  let uu____14239 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14242 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14243 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14257 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14181;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14184;
                    attrtab = uu____14187;
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
                    qtbl_name_and_index = uu____14194;
                    normalized_eff_names = uu____14230;
                    fv_delta_depths = uu____14234;
                    proof_ns = uu____14238;
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
                    identifier_info = uu____14239;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14242;
                    nbe;
                    strict_args_tab = uu____14243;
                    erasable_types_tab = uu____14257
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
  fun uu____14448  ->
    let uu____14449 = FStar_ST.op_Bang query_indices  in
    match uu____14449 with
    | [] -> failwith "Empty query indices!"
    | uu____14504 ->
        let uu____14514 =
          let uu____14524 =
            let uu____14532 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14532  in
          let uu____14586 = FStar_ST.op_Bang query_indices  in uu____14524 ::
            uu____14586
           in
        FStar_ST.op_Colon_Equals query_indices uu____14514
  
let (pop_query_indices : unit -> unit) =
  fun uu____14682  ->
    let uu____14683 = FStar_ST.op_Bang query_indices  in
    match uu____14683 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14810  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14847  ->
    match uu____14847 with
    | (l,n) ->
        let uu____14857 = FStar_ST.op_Bang query_indices  in
        (match uu____14857 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____14979 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15002  ->
    let uu____15003 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15003
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15071 =
       let uu____15074 = FStar_ST.op_Bang stack  in env1 :: uu____15074  in
     FStar_ST.op_Colon_Equals stack uu____15071);
    (let uu___414_15123 = env1  in
     let uu____15124 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15127 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15130 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15137 =
       let uu____15152 =
         let uu____15156 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15156  in
       let uu____15188 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15152, uu____15188)  in
     let uu____15237 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15240 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15243 =
       let uu____15246 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15246  in
     let uu____15266 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15279 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___414_15123.solver);
       range = (uu___414_15123.range);
       curmodule = (uu___414_15123.curmodule);
       gamma = (uu___414_15123.gamma);
       gamma_sig = (uu___414_15123.gamma_sig);
       gamma_cache = uu____15124;
       modules = (uu___414_15123.modules);
       expected_typ = (uu___414_15123.expected_typ);
       sigtab = uu____15127;
       attrtab = uu____15130;
       instantiate_imp = (uu___414_15123.instantiate_imp);
       effects = (uu___414_15123.effects);
       generalize = (uu___414_15123.generalize);
       letrecs = (uu___414_15123.letrecs);
       top_level = (uu___414_15123.top_level);
       check_uvars = (uu___414_15123.check_uvars);
       use_eq = (uu___414_15123.use_eq);
       use_eq_strict = (uu___414_15123.use_eq_strict);
       is_iface = (uu___414_15123.is_iface);
       admit = (uu___414_15123.admit);
       lax = (uu___414_15123.lax);
       lax_universes = (uu___414_15123.lax_universes);
       phase1 = (uu___414_15123.phase1);
       failhard = (uu___414_15123.failhard);
       nosynth = (uu___414_15123.nosynth);
       uvar_subtyping = (uu___414_15123.uvar_subtyping);
       tc_term = (uu___414_15123.tc_term);
       type_of = (uu___414_15123.type_of);
       universe_of = (uu___414_15123.universe_of);
       check_type_of = (uu___414_15123.check_type_of);
       use_bv_sorts = (uu___414_15123.use_bv_sorts);
       qtbl_name_and_index = uu____15137;
       normalized_eff_names = uu____15237;
       fv_delta_depths = uu____15240;
       proof_ns = (uu___414_15123.proof_ns);
       synth_hook = (uu___414_15123.synth_hook);
       try_solve_implicits_hook = (uu___414_15123.try_solve_implicits_hook);
       splice = (uu___414_15123.splice);
       mpreprocess = (uu___414_15123.mpreprocess);
       postprocess = (uu___414_15123.postprocess);
       identifier_info = uu____15243;
       tc_hooks = (uu___414_15123.tc_hooks);
       dsenv = (uu___414_15123.dsenv);
       nbe = (uu___414_15123.nbe);
       strict_args_tab = uu____15266;
       erasable_types_tab = uu____15279
     })
  
let (pop_stack : unit -> env) =
  fun uu____15289  ->
    let uu____15290 = FStar_ST.op_Bang stack  in
    match uu____15290 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15344 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15434  ->
           let uu____15435 = snapshot_stack env1  in
           match uu____15435 with
           | (stack_depth,env2) ->
               let uu____15469 = snapshot_query_indices ()  in
               (match uu____15469 with
                | (query_indices_depth,()) ->
                    let uu____15502 = (env2.solver).snapshot msg  in
                    (match uu____15502 with
                     | (solver_depth,()) ->
                         let uu____15559 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____15559 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___439_15626 = env2  in
                                 {
                                   solver = (uu___439_15626.solver);
                                   range = (uu___439_15626.range);
                                   curmodule = (uu___439_15626.curmodule);
                                   gamma = (uu___439_15626.gamma);
                                   gamma_sig = (uu___439_15626.gamma_sig);
                                   gamma_cache = (uu___439_15626.gamma_cache);
                                   modules = (uu___439_15626.modules);
                                   expected_typ =
                                     (uu___439_15626.expected_typ);
                                   sigtab = (uu___439_15626.sigtab);
                                   attrtab = (uu___439_15626.attrtab);
                                   instantiate_imp =
                                     (uu___439_15626.instantiate_imp);
                                   effects = (uu___439_15626.effects);
                                   generalize = (uu___439_15626.generalize);
                                   letrecs = (uu___439_15626.letrecs);
                                   top_level = (uu___439_15626.top_level);
                                   check_uvars = (uu___439_15626.check_uvars);
                                   use_eq = (uu___439_15626.use_eq);
                                   use_eq_strict =
                                     (uu___439_15626.use_eq_strict);
                                   is_iface = (uu___439_15626.is_iface);
                                   admit = (uu___439_15626.admit);
                                   lax = (uu___439_15626.lax);
                                   lax_universes =
                                     (uu___439_15626.lax_universes);
                                   phase1 = (uu___439_15626.phase1);
                                   failhard = (uu___439_15626.failhard);
                                   nosynth = (uu___439_15626.nosynth);
                                   uvar_subtyping =
                                     (uu___439_15626.uvar_subtyping);
                                   tc_term = (uu___439_15626.tc_term);
                                   type_of = (uu___439_15626.type_of);
                                   universe_of = (uu___439_15626.universe_of);
                                   check_type_of =
                                     (uu___439_15626.check_type_of);
                                   use_bv_sorts =
                                     (uu___439_15626.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___439_15626.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___439_15626.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___439_15626.fv_delta_depths);
                                   proof_ns = (uu___439_15626.proof_ns);
                                   synth_hook = (uu___439_15626.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___439_15626.try_solve_implicits_hook);
                                   splice = (uu___439_15626.splice);
                                   mpreprocess = (uu___439_15626.mpreprocess);
                                   postprocess = (uu___439_15626.postprocess);
                                   identifier_info =
                                     (uu___439_15626.identifier_info);
                                   tc_hooks = (uu___439_15626.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___439_15626.nbe);
                                   strict_args_tab =
                                     (uu___439_15626.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___439_15626.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15660  ->
             let uu____15661 =
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
             match uu____15661 with
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
                             ((let uu____15841 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15841
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____15857 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____15857
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____15889,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____15931 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15961  ->
                  match uu____15961 with
                  | (m,uu____15969) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15931 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____15983 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____15983 next);
              (let uu___484_15986 = env1  in
               {
                 solver = (uu___484_15986.solver);
                 range = (uu___484_15986.range);
                 curmodule = (uu___484_15986.curmodule);
                 gamma = (uu___484_15986.gamma);
                 gamma_sig = (uu___484_15986.gamma_sig);
                 gamma_cache = (uu___484_15986.gamma_cache);
                 modules = (uu___484_15986.modules);
                 expected_typ = (uu___484_15986.expected_typ);
                 sigtab = (uu___484_15986.sigtab);
                 attrtab = (uu___484_15986.attrtab);
                 instantiate_imp = (uu___484_15986.instantiate_imp);
                 effects = (uu___484_15986.effects);
                 generalize = (uu___484_15986.generalize);
                 letrecs = (uu___484_15986.letrecs);
                 top_level = (uu___484_15986.top_level);
                 check_uvars = (uu___484_15986.check_uvars);
                 use_eq = (uu___484_15986.use_eq);
                 use_eq_strict = (uu___484_15986.use_eq_strict);
                 is_iface = (uu___484_15986.is_iface);
                 admit = (uu___484_15986.admit);
                 lax = (uu___484_15986.lax);
                 lax_universes = (uu___484_15986.lax_universes);
                 phase1 = (uu___484_15986.phase1);
                 failhard = (uu___484_15986.failhard);
                 nosynth = (uu___484_15986.nosynth);
                 uvar_subtyping = (uu___484_15986.uvar_subtyping);
                 tc_term = (uu___484_15986.tc_term);
                 type_of = (uu___484_15986.type_of);
                 universe_of = (uu___484_15986.universe_of);
                 check_type_of = (uu___484_15986.check_type_of);
                 use_bv_sorts = (uu___484_15986.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___484_15986.normalized_eff_names);
                 fv_delta_depths = (uu___484_15986.fv_delta_depths);
                 proof_ns = (uu___484_15986.proof_ns);
                 synth_hook = (uu___484_15986.synth_hook);
                 try_solve_implicits_hook =
                   (uu___484_15986.try_solve_implicits_hook);
                 splice = (uu___484_15986.splice);
                 mpreprocess = (uu___484_15986.mpreprocess);
                 postprocess = (uu___484_15986.postprocess);
                 identifier_info = (uu___484_15986.identifier_info);
                 tc_hooks = (uu___484_15986.tc_hooks);
                 dsenv = (uu___484_15986.dsenv);
                 nbe = (uu___484_15986.nbe);
                 strict_args_tab = (uu___484_15986.strict_args_tab);
                 erasable_types_tab = (uu___484_15986.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16003,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              (let uu____16018 = FStar_Ident.string_of_lid l  in
               FStar_Util.smap_add tbl uu____16018 next);
              (let uu___493_16021 = env1  in
               {
                 solver = (uu___493_16021.solver);
                 range = (uu___493_16021.range);
                 curmodule = (uu___493_16021.curmodule);
                 gamma = (uu___493_16021.gamma);
                 gamma_sig = (uu___493_16021.gamma_sig);
                 gamma_cache = (uu___493_16021.gamma_cache);
                 modules = (uu___493_16021.modules);
                 expected_typ = (uu___493_16021.expected_typ);
                 sigtab = (uu___493_16021.sigtab);
                 attrtab = (uu___493_16021.attrtab);
                 instantiate_imp = (uu___493_16021.instantiate_imp);
                 effects = (uu___493_16021.effects);
                 generalize = (uu___493_16021.generalize);
                 letrecs = (uu___493_16021.letrecs);
                 top_level = (uu___493_16021.top_level);
                 check_uvars = (uu___493_16021.check_uvars);
                 use_eq = (uu___493_16021.use_eq);
                 use_eq_strict = (uu___493_16021.use_eq_strict);
                 is_iface = (uu___493_16021.is_iface);
                 admit = (uu___493_16021.admit);
                 lax = (uu___493_16021.lax);
                 lax_universes = (uu___493_16021.lax_universes);
                 phase1 = (uu___493_16021.phase1);
                 failhard = (uu___493_16021.failhard);
                 nosynth = (uu___493_16021.nosynth);
                 uvar_subtyping = (uu___493_16021.uvar_subtyping);
                 tc_term = (uu___493_16021.tc_term);
                 type_of = (uu___493_16021.type_of);
                 universe_of = (uu___493_16021.universe_of);
                 check_type_of = (uu___493_16021.check_type_of);
                 use_bv_sorts = (uu___493_16021.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___493_16021.normalized_eff_names);
                 fv_delta_depths = (uu___493_16021.fv_delta_depths);
                 proof_ns = (uu___493_16021.proof_ns);
                 synth_hook = (uu___493_16021.synth_hook);
                 try_solve_implicits_hook =
                   (uu___493_16021.try_solve_implicits_hook);
                 splice = (uu___493_16021.splice);
                 mpreprocess = (uu___493_16021.mpreprocess);
                 postprocess = (uu___493_16021.postprocess);
                 identifier_info = (uu___493_16021.identifier_info);
                 tc_hooks = (uu___493_16021.tc_hooks);
                 dsenv = (uu___493_16021.dsenv);
                 nbe = (uu___493_16021.nbe);
                 strict_args_tab = (uu___493_16021.strict_args_tab);
                 erasable_types_tab = (uu___493_16021.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____16050 = FStar_Ident.string_of_lid env1.curmodule  in
      FStar_Options.debug_at_level uu____16050 l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___500_16066 = e  in
         {
           solver = (uu___500_16066.solver);
           range = r;
           curmodule = (uu___500_16066.curmodule);
           gamma = (uu___500_16066.gamma);
           gamma_sig = (uu___500_16066.gamma_sig);
           gamma_cache = (uu___500_16066.gamma_cache);
           modules = (uu___500_16066.modules);
           expected_typ = (uu___500_16066.expected_typ);
           sigtab = (uu___500_16066.sigtab);
           attrtab = (uu___500_16066.attrtab);
           instantiate_imp = (uu___500_16066.instantiate_imp);
           effects = (uu___500_16066.effects);
           generalize = (uu___500_16066.generalize);
           letrecs = (uu___500_16066.letrecs);
           top_level = (uu___500_16066.top_level);
           check_uvars = (uu___500_16066.check_uvars);
           use_eq = (uu___500_16066.use_eq);
           use_eq_strict = (uu___500_16066.use_eq_strict);
           is_iface = (uu___500_16066.is_iface);
           admit = (uu___500_16066.admit);
           lax = (uu___500_16066.lax);
           lax_universes = (uu___500_16066.lax_universes);
           phase1 = (uu___500_16066.phase1);
           failhard = (uu___500_16066.failhard);
           nosynth = (uu___500_16066.nosynth);
           uvar_subtyping = (uu___500_16066.uvar_subtyping);
           tc_term = (uu___500_16066.tc_term);
           type_of = (uu___500_16066.type_of);
           universe_of = (uu___500_16066.universe_of);
           check_type_of = (uu___500_16066.check_type_of);
           use_bv_sorts = (uu___500_16066.use_bv_sorts);
           qtbl_name_and_index = (uu___500_16066.qtbl_name_and_index);
           normalized_eff_names = (uu___500_16066.normalized_eff_names);
           fv_delta_depths = (uu___500_16066.fv_delta_depths);
           proof_ns = (uu___500_16066.proof_ns);
           synth_hook = (uu___500_16066.synth_hook);
           try_solve_implicits_hook =
             (uu___500_16066.try_solve_implicits_hook);
           splice = (uu___500_16066.splice);
           mpreprocess = (uu___500_16066.mpreprocess);
           postprocess = (uu___500_16066.postprocess);
           identifier_info = (uu___500_16066.identifier_info);
           tc_hooks = (uu___500_16066.tc_hooks);
           dsenv = (uu___500_16066.dsenv);
           nbe = (uu___500_16066.nbe);
           strict_args_tab = (uu___500_16066.strict_args_tab);
           erasable_types_tab = (uu___500_16066.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16086 =
        let uu____16087 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16087 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16086
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16142 =
          let uu____16143 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16143 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16142
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16198 =
          let uu____16199 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16199 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16198
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16254 =
        let uu____16255 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16255 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16254
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___517_16319 = env1  in
      {
        solver = (uu___517_16319.solver);
        range = (uu___517_16319.range);
        curmodule = lid;
        gamma = (uu___517_16319.gamma);
        gamma_sig = (uu___517_16319.gamma_sig);
        gamma_cache = (uu___517_16319.gamma_cache);
        modules = (uu___517_16319.modules);
        expected_typ = (uu___517_16319.expected_typ);
        sigtab = (uu___517_16319.sigtab);
        attrtab = (uu___517_16319.attrtab);
        instantiate_imp = (uu___517_16319.instantiate_imp);
        effects = (uu___517_16319.effects);
        generalize = (uu___517_16319.generalize);
        letrecs = (uu___517_16319.letrecs);
        top_level = (uu___517_16319.top_level);
        check_uvars = (uu___517_16319.check_uvars);
        use_eq = (uu___517_16319.use_eq);
        use_eq_strict = (uu___517_16319.use_eq_strict);
        is_iface = (uu___517_16319.is_iface);
        admit = (uu___517_16319.admit);
        lax = (uu___517_16319.lax);
        lax_universes = (uu___517_16319.lax_universes);
        phase1 = (uu___517_16319.phase1);
        failhard = (uu___517_16319.failhard);
        nosynth = (uu___517_16319.nosynth);
        uvar_subtyping = (uu___517_16319.uvar_subtyping);
        tc_term = (uu___517_16319.tc_term);
        type_of = (uu___517_16319.type_of);
        universe_of = (uu___517_16319.universe_of);
        check_type_of = (uu___517_16319.check_type_of);
        use_bv_sorts = (uu___517_16319.use_bv_sorts);
        qtbl_name_and_index = (uu___517_16319.qtbl_name_and_index);
        normalized_eff_names = (uu___517_16319.normalized_eff_names);
        fv_delta_depths = (uu___517_16319.fv_delta_depths);
        proof_ns = (uu___517_16319.proof_ns);
        synth_hook = (uu___517_16319.synth_hook);
        try_solve_implicits_hook = (uu___517_16319.try_solve_implicits_hook);
        splice = (uu___517_16319.splice);
        mpreprocess = (uu___517_16319.mpreprocess);
        postprocess = (uu___517_16319.postprocess);
        identifier_info = (uu___517_16319.identifier_info);
        tc_hooks = (uu___517_16319.tc_hooks);
        dsenv = (uu___517_16319.dsenv);
        nbe = (uu___517_16319.nbe);
        strict_args_tab = (uu___517_16319.strict_args_tab);
        erasable_types_tab = (uu___517_16319.erasable_types_tab)
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
      let uu____16350 = FStar_Ident.string_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16350
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16363 =
      let uu____16365 = FStar_Ident.string_of_lid l  in
      FStar_Util.format1 "Name \"%s\" not found" uu____16365  in
    (FStar_Errors.Fatal_NameNotFound, uu____16363)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16380 =
      let uu____16382 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16382  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16380)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16391  ->
    let uu____16392 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16392
  
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
      | ((formals,t),uu____16492) ->
          let vs = mk_univ_subst formals us  in
          let uu____16516 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16516)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16533  ->
    match uu___1_16533 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16559  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16579 = inst_tscheme t  in
      match uu____16579 with
      | (us,t1) ->
          let uu____16590 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16590)
  
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
          let uu____16615 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16617 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16615 uu____16617
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
        fun uu____16644  ->
          match uu____16644 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16658 =
                    let uu____16660 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16664 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16668 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16670 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16660 uu____16664 uu____16668 uu____16670
                     in
                  failwith uu____16658)
               else ();
               (let uu____16675 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16675))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16693 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16704 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16715 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____16729 =
        let uu____16731 = FStar_Ident.nsstr l  in
        let uu____16733 = FStar_Ident.string_of_lid cur  in
        uu____16731 = uu____16733  in
      if uu____16729
      then Yes
      else
        (let uu____16739 =
           let uu____16741 = FStar_Ident.nsstr l  in
           let uu____16743 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____16741 uu____16743  in
         if uu____16739
         then
           let lns =
             let uu____16749 = FStar_Ident.ns_of_lid l  in
             let uu____16752 =
               let uu____16755 = FStar_Ident.ident_of_lid l  in [uu____16755]
                in
             FStar_List.append uu____16749 uu____16752  in
           let cur1 =
             let uu____16759 = FStar_Ident.ns_of_lid cur  in
             let uu____16762 =
               let uu____16765 = FStar_Ident.ident_of_lid cur  in
               [uu____16765]  in
             FStar_List.append uu____16759 uu____16762  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____16789) -> Maybe
             | (uu____16796,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____16815 = FStar_Ident.text_of_id hd  in
                 let uu____16817 = FStar_Ident.text_of_id hd'  in
                 uu____16815 = uu____16817 -> aux tl tl'
             | uu____16820 -> No  in
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
        (let uu____16872 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____16872 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____16916 =
            let uu____16919 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____16919  in
          match uu____16916 with
          | FStar_Pervasives_Native.None  ->
              let uu____16941 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_16985  ->
                     match uu___2_16985 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17024 = FStar_Ident.lid_equals lid l  in
                         if uu____17024
                         then
                           let uu____17047 =
                             let uu____17066 =
                               let uu____17081 = inst_tscheme t  in
                               FStar_Util.Inl uu____17081  in
                             let uu____17096 = FStar_Ident.range_of_lid l  in
                             (uu____17066, uu____17096)  in
                           FStar_Pervasives_Native.Some uu____17047
                         else FStar_Pervasives_Native.None
                     | uu____17149 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16941
                (fun uu____17187  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17197  ->
                        match uu___3_17197 with
                        | (uu____17200,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17202);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17203;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17204;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17205;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17206;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17207;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17229 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17229
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
                                  uu____17281 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17288 -> cache t  in
                            let uu____17289 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17289 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17295 =
                                   let uu____17296 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17296)
                                    in
                                 maybe_cache uu____17295)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17367 = find_in_sigtab env1 lid  in
         match uu____17367 with
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
      let uu____17448 = lookup_qname env1 lid  in
      match uu____17448 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17469,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17583 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17583 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17628 =
          let uu____17631 = lookup_attr env2 attr  in se1 :: uu____17631  in
        FStar_Util.smap_add (attrtab env2) attr uu____17628  in
      FStar_List.iter
        (fun attr  ->
           let uu____17641 =
             let uu____17642 = FStar_Syntax_Subst.compress attr  in
             uu____17642.FStar_Syntax_Syntax.n  in
           match uu____17641 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17646 =
                 let uu____17648 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17648  in
               add_one env1 se uu____17646
           | uu____17649 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17672) ->
          add_sigelts env1 ses
      | uu____17681 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17689 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17689 se) lids;
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
        (fun uu___4_17723  ->
           match uu___4_17723 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____17733 =
                 let uu____17740 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____17740)  in
               FStar_Pervasives_Native.Some uu____17733
           | uu____17749 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17811,lb::[]),uu____17813) ->
            let uu____17822 =
              let uu____17831 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17840 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17831, uu____17840)  in
            FStar_Pervasives_Native.Some uu____17822
        | FStar_Syntax_Syntax.Sig_let ((uu____17853,lbs),uu____17855) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17887 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17900 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17900
                     then
                       let uu____17913 =
                         let uu____17922 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17931 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17922, uu____17931)  in
                       FStar_Pervasives_Native.Some uu____17913
                     else FStar_Pervasives_Native.None)
        | uu____17954 -> FStar_Pervasives_Native.None
  
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
                    let uu____18046 =
                      let uu____18048 =
                        let uu____18050 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18052 =
                          let uu____18054 =
                            let uu____18056 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18062 =
                              let uu____18064 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18064  in
                            Prims.op_Hat uu____18056 uu____18062  in
                          Prims.op_Hat ", expected " uu____18054  in
                        Prims.op_Hat uu____18050 uu____18052  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18048
                       in
                    failwith uu____18046
                  else ());
             (let uu____18071 =
                let uu____18080 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18080, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18071))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18100,uu____18101) ->
            let uu____18106 =
              let uu____18115 =
                let uu____18120 =
                  let uu____18121 =
                    let uu____18124 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18124  in
                  (us, uu____18121)  in
                inst_ts us_opt uu____18120  in
              (uu____18115, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18106
        | uu____18143 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18232 =
          match uu____18232 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18328,uvs,t,uu____18331,uu____18332,uu____18333);
                      FStar_Syntax_Syntax.sigrng = uu____18334;
                      FStar_Syntax_Syntax.sigquals = uu____18335;
                      FStar_Syntax_Syntax.sigmeta = uu____18336;
                      FStar_Syntax_Syntax.sigattrs = uu____18337;
                      FStar_Syntax_Syntax.sigopts = uu____18338;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18363 =
                     let uu____18372 = inst_tscheme1 (uvs, t)  in
                     (uu____18372, rng)  in
                   FStar_Pervasives_Native.Some uu____18363
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18396;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18398;
                      FStar_Syntax_Syntax.sigattrs = uu____18399;
                      FStar_Syntax_Syntax.sigopts = uu____18400;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18419 =
                     let uu____18421 = in_cur_mod env1 l  in
                     uu____18421 = Yes  in
                   if uu____18419
                   then
                     let uu____18433 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18433
                      then
                        let uu____18449 =
                          let uu____18458 = inst_tscheme1 (uvs, t)  in
                          (uu____18458, rng)  in
                        FStar_Pervasives_Native.Some uu____18449
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18491 =
                        let uu____18500 = inst_tscheme1 (uvs, t)  in
                        (uu____18500, rng)  in
                      FStar_Pervasives_Native.Some uu____18491)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18525,uu____18526);
                      FStar_Syntax_Syntax.sigrng = uu____18527;
                      FStar_Syntax_Syntax.sigquals = uu____18528;
                      FStar_Syntax_Syntax.sigmeta = uu____18529;
                      FStar_Syntax_Syntax.sigattrs = uu____18530;
                      FStar_Syntax_Syntax.sigopts = uu____18531;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18574 =
                          let uu____18583 = inst_tscheme1 (uvs, k)  in
                          (uu____18583, rng)  in
                        FStar_Pervasives_Native.Some uu____18574
                    | uu____18604 ->
                        let uu____18605 =
                          let uu____18614 =
                            let uu____18619 =
                              let uu____18620 =
                                let uu____18623 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18623
                                 in
                              (uvs, uu____18620)  in
                            inst_tscheme1 uu____18619  in
                          (uu____18614, rng)  in
                        FStar_Pervasives_Native.Some uu____18605)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18646,uu____18647);
                      FStar_Syntax_Syntax.sigrng = uu____18648;
                      FStar_Syntax_Syntax.sigquals = uu____18649;
                      FStar_Syntax_Syntax.sigmeta = uu____18650;
                      FStar_Syntax_Syntax.sigattrs = uu____18651;
                      FStar_Syntax_Syntax.sigopts = uu____18652;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18696 =
                          let uu____18705 = inst_tscheme_with (uvs, k) us  in
                          (uu____18705, rng)  in
                        FStar_Pervasives_Native.Some uu____18696
                    | uu____18726 ->
                        let uu____18727 =
                          let uu____18736 =
                            let uu____18741 =
                              let uu____18742 =
                                let uu____18745 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18745
                                 in
                              (uvs, uu____18742)  in
                            inst_tscheme_with uu____18741 us  in
                          (uu____18736, rng)  in
                        FStar_Pervasives_Native.Some uu____18727)
               | FStar_Util.Inr se ->
                   let uu____18781 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18802;
                          FStar_Syntax_Syntax.sigrng = uu____18803;
                          FStar_Syntax_Syntax.sigquals = uu____18804;
                          FStar_Syntax_Syntax.sigmeta = uu____18805;
                          FStar_Syntax_Syntax.sigattrs = uu____18806;
                          FStar_Syntax_Syntax.sigopts = uu____18807;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18824 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____18781
                     (FStar_Util.map_option
                        (fun uu____18872  ->
                           match uu____18872 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18903 =
          let uu____18914 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____18914 mapper  in
        match uu____18903 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18988 =
              let uu____18999 =
                let uu____19006 =
                  let uu___854_19009 = t  in
                  let uu____19010 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___854_19009.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19010;
                    FStar_Syntax_Syntax.vars =
                      (uu___854_19009.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19006)  in
              (uu____18999, r)  in
            FStar_Pervasives_Native.Some uu____18988
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19059 = lookup_qname env1 l  in
      match uu____19059 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19080 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19134 = try_lookup_bv env1 bv  in
      match uu____19134 with
      | FStar_Pervasives_Native.None  ->
          let uu____19149 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19149 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19165 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19166 =
            let uu____19167 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19167  in
          (uu____19165, uu____19166)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19189 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19189 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19255 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19255  in
          let uu____19256 =
            let uu____19265 =
              let uu____19270 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19270)  in
            (uu____19265, r1)  in
          FStar_Pervasives_Native.Some uu____19256
  
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
        let uu____19305 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19305 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19338,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19363 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19363  in
            let uu____19364 =
              let uu____19369 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19369, r1)  in
            FStar_Pervasives_Native.Some uu____19364
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19393 = try_lookup_lid env1 l  in
      match uu____19393 with
      | FStar_Pervasives_Native.None  ->
          let uu____19420 = name_not_found l  in
          let uu____19426 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19420 uu____19426
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19471  ->
              match uu___5_19471 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19474 = FStar_Ident.text_of_id x  in
                  let uu____19476 = FStar_Ident.text_of_id y  in
                  uu____19474 = uu____19476
              | uu____19479 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19500 = lookup_qname env1 lid  in
      match uu____19500 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19509,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19512;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19514;
              FStar_Syntax_Syntax.sigattrs = uu____19515;
              FStar_Syntax_Syntax.sigopts = uu____19516;_},FStar_Pervasives_Native.None
            ),uu____19517)
          ->
          let uu____19568 =
            let uu____19575 =
              let uu____19576 =
                let uu____19579 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19579 t  in
              (uvs, uu____19576)  in
            (uu____19575, q)  in
          FStar_Pervasives_Native.Some uu____19568
      | uu____19592 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19614 = lookup_qname env1 lid  in
      match uu____19614 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19619,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19622;
              FStar_Syntax_Syntax.sigquals = uu____19623;
              FStar_Syntax_Syntax.sigmeta = uu____19624;
              FStar_Syntax_Syntax.sigattrs = uu____19625;
              FStar_Syntax_Syntax.sigopts = uu____19626;_},FStar_Pervasives_Native.None
            ),uu____19627)
          ->
          let uu____19678 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19678 (uvs, t)
      | uu____19683 ->
          let uu____19684 = name_not_found lid  in
          let uu____19690 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19684 uu____19690
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19710 = lookup_qname env1 lid  in
      match uu____19710 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19715,uvs,t,uu____19718,uu____19719,uu____19720);
              FStar_Syntax_Syntax.sigrng = uu____19721;
              FStar_Syntax_Syntax.sigquals = uu____19722;
              FStar_Syntax_Syntax.sigmeta = uu____19723;
              FStar_Syntax_Syntax.sigattrs = uu____19724;
              FStar_Syntax_Syntax.sigopts = uu____19725;_},FStar_Pervasives_Native.None
            ),uu____19726)
          ->
          let uu____19783 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19783 (uvs, t)
      | uu____19788 ->
          let uu____19789 = name_not_found lid  in
          let uu____19795 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19789 uu____19795
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____19818 = lookup_qname env1 lid  in
      match uu____19818 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19826,uu____19827,uu____19828,uu____19829,uu____19830,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19832;
              FStar_Syntax_Syntax.sigquals = uu____19833;
              FStar_Syntax_Syntax.sigmeta = uu____19834;
              FStar_Syntax_Syntax.sigattrs = uu____19835;
              FStar_Syntax_Syntax.sigopts = uu____19836;_},uu____19837),uu____19838)
          -> (true, dcs)
      | uu____19903 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____19919 = lookup_qname env1 lid  in
      match uu____19919 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19920,uu____19921,uu____19922,l,uu____19924,uu____19925);
              FStar_Syntax_Syntax.sigrng = uu____19926;
              FStar_Syntax_Syntax.sigquals = uu____19927;
              FStar_Syntax_Syntax.sigmeta = uu____19928;
              FStar_Syntax_Syntax.sigattrs = uu____19929;
              FStar_Syntax_Syntax.sigopts = uu____19930;_},uu____19931),uu____19932)
          -> l
      | uu____19991 ->
          let uu____19992 =
            let uu____19994 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19994  in
          failwith uu____19992
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20064)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20121) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20145 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20145
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20180 -> FStar_Pervasives_Native.None)
          | uu____20189 -> FStar_Pervasives_Native.None
  
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
        let uu____20251 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20251
  
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
        let uu____20284 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20284
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20308 =
        let uu____20310 = FStar_Ident.nsstr lid  in uu____20310 = "Prims"  in
      if uu____20308
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20340,uu____20341) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20390),uu____20391) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20440 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20458 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20468 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20485 ->
                  let uu____20492 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20492
              | FStar_Syntax_Syntax.Sig_let ((uu____20493,lbs),uu____20495)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20511 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20511
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20518 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20534 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20544 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20545 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20552 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20553 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20554 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20567 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20568 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20591 =
        let uu____20593 = FStar_Ident.nsstr lid  in uu____20593 = "Prims"  in
      if uu____20591
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20600 =
           let uu____20603 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20603
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20600
           (fun d_opt  ->
              let uu____20615 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20615
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20625 =
                   let uu____20628 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20628  in
                 match uu____20625 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20629 =
                       let uu____20631 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20631
                        in
                     failwith uu____20629
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20636 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20636
                       then
                         let uu____20639 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20641 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20643 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20639 uu____20641 uu____20643
                       else ());
                      (let uu____20649 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20649 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20670),uu____20671) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20720 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20742),uu____20743) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20792 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20814 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20814
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20847 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____20847 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20869 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20878 =
                        let uu____20879 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20879.FStar_Syntax_Syntax.n  in
                      match uu____20878 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20884 -> false))
               in
            (true, uu____20869)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20907 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____20907
  
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
          let uu____20979 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____20979  in
        let uu____20980 = FStar_Util.smap_try_find tab s  in
        match uu____20980 with
        | FStar_Pervasives_Native.None  ->
            let uu____20983 = f ()  in
            (match uu____20983 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21021 =
        let uu____21022 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21022 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21056 =
        let uu____21057 = FStar_Syntax_Util.unrefine t  in
        uu____21057.FStar_Syntax_Syntax.n  in
      match uu____21056 with
      | FStar_Syntax_Syntax.Tm_type uu____21061 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21065) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21091) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21096,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21118 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21151 =
        let attrs =
          let uu____21157 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21157  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21197 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21197)
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
      let uu____21242 = lookup_qname env1 ftv  in
      match uu____21242 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21246) ->
          let uu____21291 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21291 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21312,t),r) ->
               let uu____21327 =
                 let uu____21328 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21328 t  in
               FStar_Pervasives_Native.Some uu____21327)
      | uu____21329 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21341 = try_lookup_effect_lid env1 ftv  in
      match uu____21341 with
      | FStar_Pervasives_Native.None  ->
          let uu____21344 = name_not_found ftv  in
          let uu____21350 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21344 uu____21350
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
        let uu____21374 = lookup_qname env1 lid0  in
        match uu____21374 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21385);
                FStar_Syntax_Syntax.sigrng = uu____21386;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21388;
                FStar_Syntax_Syntax.sigattrs = uu____21389;
                FStar_Syntax_Syntax.sigopts = uu____21390;_},FStar_Pervasives_Native.None
              ),uu____21391)
            ->
            let lid1 =
              let uu____21447 =
                let uu____21448 = FStar_Ident.range_of_lid lid  in
                let uu____21449 =
                  let uu____21450 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21450  in
                FStar_Range.set_use_range uu____21448 uu____21449  in
              FStar_Ident.set_lid_range lid uu____21447  in
            let uu____21451 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21457  ->
                      match uu___6_21457 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21460 -> false))
               in
            if uu____21451
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21479 =
                      let uu____21481 =
                        let uu____21483 = get_range env1  in
                        FStar_Range.string_of_range uu____21483  in
                      let uu____21484 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21486 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21481 uu____21484 uu____21486
                       in
                    failwith uu____21479)
                  in
               match (binders, univs) with
               | ([],uu____21507) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21533,uu____21534::uu____21535::uu____21536) ->
                   let uu____21557 =
                     let uu____21559 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21561 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21559 uu____21561
                      in
                   failwith uu____21557
               | uu____21572 ->
                   let uu____21587 =
                     let uu____21592 =
                       let uu____21593 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21593)  in
                     inst_tscheme_with uu____21592 insts  in
                   (match uu____21587 with
                    | (uu____21606,t) ->
                        let t1 =
                          let uu____21609 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21609 t  in
                        let uu____21610 =
                          let uu____21611 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21611.FStar_Syntax_Syntax.n  in
                        (match uu____21610 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21646 -> failwith "Impossible")))
        | uu____21654 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21678 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21678 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21691,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21698 = find l2  in
            (match uu____21698 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21705 =
          let uu____21708 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____21708  in
        match uu____21705 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21711 = find l  in
            (match uu____21711 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____21716 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____21716
                     m);
                  m))
         in
      let uu____21718 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21718
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21739 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____21739 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21745) ->
            FStar_List.length bs
        | uu____21784 ->
            let uu____21785 =
              let uu____21791 =
                let uu____21793 = FStar_Ident.string_of_lid name  in
                let uu____21795 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21793 uu____21795
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21791)
               in
            FStar_Errors.raise_error uu____21785 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____21814 = lookup_qname env1 l1  in
      match uu____21814 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21817;
              FStar_Syntax_Syntax.sigrng = uu____21818;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21820;
              FStar_Syntax_Syntax.sigattrs = uu____21821;
              FStar_Syntax_Syntax.sigopts = uu____21822;_},uu____21823),uu____21824)
          -> q
      | uu____21877 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____21901 =
          let uu____21902 =
            let uu____21904 = FStar_Util.string_of_int i  in
            let uu____21906 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21904 uu____21906
             in
          failwith uu____21902  in
        let uu____21909 = lookup_datacon env1 lid  in
        match uu____21909 with
        | (uu____21914,t) ->
            let uu____21916 =
              let uu____21917 = FStar_Syntax_Subst.compress t  in
              uu____21917.FStar_Syntax_Syntax.n  in
            (match uu____21916 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21921) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____21967 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____21981 = lookup_qname env1 l  in
      match uu____21981 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21983,uu____21984,uu____21985);
              FStar_Syntax_Syntax.sigrng = uu____21986;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21988;
              FStar_Syntax_Syntax.sigattrs = uu____21989;
              FStar_Syntax_Syntax.sigopts = uu____21990;_},uu____21991),uu____21992)
          ->
          FStar_Util.for_some
            (fun uu___7_22047  ->
               match uu___7_22047 with
               | FStar_Syntax_Syntax.Projector uu____22049 -> true
               | uu____22055 -> false) quals
      | uu____22057 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22071 = lookup_qname env1 lid  in
      match uu____22071 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22073,uu____22074,uu____22075,uu____22076,uu____22077,uu____22078);
              FStar_Syntax_Syntax.sigrng = uu____22079;
              FStar_Syntax_Syntax.sigquals = uu____22080;
              FStar_Syntax_Syntax.sigmeta = uu____22081;
              FStar_Syntax_Syntax.sigattrs = uu____22082;
              FStar_Syntax_Syntax.sigopts = uu____22083;_},uu____22084),uu____22085)
          -> true
      | uu____22145 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22159 = lookup_qname env1 lid  in
      match uu____22159 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22161,uu____22162,uu____22163,uu____22164,uu____22165,uu____22166);
              FStar_Syntax_Syntax.sigrng = uu____22167;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22169;
              FStar_Syntax_Syntax.sigattrs = uu____22170;
              FStar_Syntax_Syntax.sigopts = uu____22171;_},uu____22172),uu____22173)
          ->
          FStar_Util.for_some
            (fun uu___8_22236  ->
               match uu___8_22236 with
               | FStar_Syntax_Syntax.RecordType uu____22238 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22248 -> true
               | uu____22258 -> false) quals
      | uu____22260 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22270,uu____22271);
            FStar_Syntax_Syntax.sigrng = uu____22272;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22274;
            FStar_Syntax_Syntax.sigattrs = uu____22275;
            FStar_Syntax_Syntax.sigopts = uu____22276;_},uu____22277),uu____22278)
        ->
        FStar_Util.for_some
          (fun uu___9_22337  ->
             match uu___9_22337 with
             | FStar_Syntax_Syntax.Action uu____22339 -> true
             | uu____22341 -> false) quals
    | uu____22343 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22357 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22357
  
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
      let uu____22374 =
        let uu____22375 = FStar_Syntax_Util.un_uinst head  in
        uu____22375.FStar_Syntax_Syntax.n  in
      match uu____22374 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22381 ->
               true
           | uu____22384 -> false)
      | uu____22386 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22400 = lookup_qname env1 l  in
      match uu____22400 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22403),uu____22404) ->
          FStar_Util.for_some
            (fun uu___10_22452  ->
               match uu___10_22452 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22455 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22457 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22533 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22551) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22569 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22577 ->
                 FStar_Pervasives_Native.Some true
             | uu____22596 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22599 =
        let uu____22603 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22603 mapper  in
      match uu____22599 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22663 = lookup_qname env1 lid  in
      match uu____22663 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22667,uu____22668,tps,uu____22670,uu____22671,uu____22672);
              FStar_Syntax_Syntax.sigrng = uu____22673;
              FStar_Syntax_Syntax.sigquals = uu____22674;
              FStar_Syntax_Syntax.sigmeta = uu____22675;
              FStar_Syntax_Syntax.sigattrs = uu____22676;
              FStar_Syntax_Syntax.sigopts = uu____22677;_},uu____22678),uu____22679)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22747 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22793  ->
              match uu____22793 with
              | (d,uu____22802) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____22818 = effect_decl_opt env1 l  in
      match uu____22818 with
      | FStar_Pervasives_Native.None  ->
          let uu____22833 = name_not_found l  in
          let uu____22839 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22833 uu____22839
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22867 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____22867 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22874  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22888  ->
            fun uu____22889  -> fun e  -> FStar_Util.return_all e))
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
        let uu____22923 = FStar_Ident.lid_equals l1 l2  in
        if uu____22923
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____22942 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22942
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____22961 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23014  ->
                        match uu____23014 with
                        | (m1,m2,uu____23028,uu____23029,uu____23030) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22961 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23055,uu____23056,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23104 = join_opt env1 l1 l2  in
        match uu____23104 with
        | FStar_Pervasives_Native.None  ->
            let uu____23125 =
              let uu____23131 =
                let uu____23133 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23135 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23133 uu____23135
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23131)  in
            FStar_Errors.raise_error uu____23125 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23178 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23178
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
  'uuuuuu23198 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23198) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23227 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23253  ->
                match uu____23253 with
                | (d,uu____23260) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23227 with
      | FStar_Pervasives_Native.None  ->
          let uu____23271 =
            let uu____23273 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23273
             in
          failwith uu____23271
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23288 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23288 with
           | (uu____23299,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23317)::(wp,uu____23319)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23375 -> failwith "Impossible"))
  
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
        | uu____23440 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23453 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23453 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23470 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23470 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23495 =
                     let uu____23501 =
                       let uu____23503 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23511 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23522 =
                         let uu____23524 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23524  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23503 uu____23511 uu____23522
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23501)
                      in
                   FStar_Errors.raise_error uu____23495
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23532 =
                     let uu____23543 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23543 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23580  ->
                        fun uu____23581  ->
                          match (uu____23580, uu____23581) with
                          | ((x,uu____23611),(t,uu____23613)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23532
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23644 =
                     let uu___1610_23645 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1610_23645.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1610_23645.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1610_23645.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1610_23645.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23644
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23657 .
    'uuuuuu23657 ->
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
            let uu____23698 =
              let uu____23705 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____23705)  in
            match uu____23698 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23729 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23731 = FStar_Util.string_of_int given  in
                     let uu____23733 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23729 uu____23731 uu____23733
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23738 = effect_decl_opt env1 effect_name  in
          match uu____23738 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23760) ->
              let uu____23771 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23771 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23789 =
                       let uu____23792 = get_range env1  in
                       let uu____23793 =
                         let uu____23800 =
                           let uu____23801 =
                             let uu____23818 =
                               let uu____23829 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23829 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23818)  in
                           FStar_Syntax_Syntax.Tm_app uu____23801  in
                         FStar_Syntax_Syntax.mk uu____23800  in
                       uu____23793 FStar_Pervasives_Native.None uu____23792
                        in
                     FStar_Pervasives_Native.Some uu____23789)))
  
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
           (fun uu___11_23929  ->
              match uu___11_23929 with
              | FStar_Syntax_Syntax.Reflectable uu____23931 -> true
              | uu____23933 -> false))
  
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
      | uu____23993 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24008 =
        let uu____24009 = FStar_Syntax_Subst.compress t  in
        uu____24009.FStar_Syntax_Syntax.n  in
      match uu____24008 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24013,c) ->
          is_reifiable_comp env1 c
      | uu____24035 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24055 =
           let uu____24057 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24057  in
         if uu____24055
         then
           let uu____24060 =
             let uu____24066 =
               let uu____24068 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24068
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24066)  in
           let uu____24072 = get_range env1  in
           FStar_Errors.raise_error uu____24060 uu____24072
         else ());
        (let uu____24075 = effect_repr_aux true env1 c u_c  in
         match uu____24075 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1687_24111 = env1  in
        {
          solver = (uu___1687_24111.solver);
          range = (uu___1687_24111.range);
          curmodule = (uu___1687_24111.curmodule);
          gamma = (uu___1687_24111.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1687_24111.gamma_cache);
          modules = (uu___1687_24111.modules);
          expected_typ = (uu___1687_24111.expected_typ);
          sigtab = (uu___1687_24111.sigtab);
          attrtab = (uu___1687_24111.attrtab);
          instantiate_imp = (uu___1687_24111.instantiate_imp);
          effects = (uu___1687_24111.effects);
          generalize = (uu___1687_24111.generalize);
          letrecs = (uu___1687_24111.letrecs);
          top_level = (uu___1687_24111.top_level);
          check_uvars = (uu___1687_24111.check_uvars);
          use_eq = (uu___1687_24111.use_eq);
          use_eq_strict = (uu___1687_24111.use_eq_strict);
          is_iface = (uu___1687_24111.is_iface);
          admit = (uu___1687_24111.admit);
          lax = (uu___1687_24111.lax);
          lax_universes = (uu___1687_24111.lax_universes);
          phase1 = (uu___1687_24111.phase1);
          failhard = (uu___1687_24111.failhard);
          nosynth = (uu___1687_24111.nosynth);
          uvar_subtyping = (uu___1687_24111.uvar_subtyping);
          tc_term = (uu___1687_24111.tc_term);
          type_of = (uu___1687_24111.type_of);
          universe_of = (uu___1687_24111.universe_of);
          check_type_of = (uu___1687_24111.check_type_of);
          use_bv_sorts = (uu___1687_24111.use_bv_sorts);
          qtbl_name_and_index = (uu___1687_24111.qtbl_name_and_index);
          normalized_eff_names = (uu___1687_24111.normalized_eff_names);
          fv_delta_depths = (uu___1687_24111.fv_delta_depths);
          proof_ns = (uu___1687_24111.proof_ns);
          synth_hook = (uu___1687_24111.synth_hook);
          try_solve_implicits_hook =
            (uu___1687_24111.try_solve_implicits_hook);
          splice = (uu___1687_24111.splice);
          mpreprocess = (uu___1687_24111.mpreprocess);
          postprocess = (uu___1687_24111.postprocess);
          identifier_info = (uu___1687_24111.identifier_info);
          tc_hooks = (uu___1687_24111.tc_hooks);
          dsenv = (uu___1687_24111.dsenv);
          nbe = (uu___1687_24111.nbe);
          strict_args_tab = (uu___1687_24111.strict_args_tab);
          erasable_types_tab = (uu___1687_24111.erasable_types_tab)
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
    fun uu____24130  ->
      match uu____24130 with
      | (ed,quals) ->
          let effects1 =
            let uu___1696_24144 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1696_24144.order);
              joins = (uu___1696_24144.joins);
              polymonadic_binds = (uu___1696_24144.polymonadic_binds)
            }  in
          let uu___1699_24153 = env1  in
          {
            solver = (uu___1699_24153.solver);
            range = (uu___1699_24153.range);
            curmodule = (uu___1699_24153.curmodule);
            gamma = (uu___1699_24153.gamma);
            gamma_sig = (uu___1699_24153.gamma_sig);
            gamma_cache = (uu___1699_24153.gamma_cache);
            modules = (uu___1699_24153.modules);
            expected_typ = (uu___1699_24153.expected_typ);
            sigtab = (uu___1699_24153.sigtab);
            attrtab = (uu___1699_24153.attrtab);
            instantiate_imp = (uu___1699_24153.instantiate_imp);
            effects = effects1;
            generalize = (uu___1699_24153.generalize);
            letrecs = (uu___1699_24153.letrecs);
            top_level = (uu___1699_24153.top_level);
            check_uvars = (uu___1699_24153.check_uvars);
            use_eq = (uu___1699_24153.use_eq);
            use_eq_strict = (uu___1699_24153.use_eq_strict);
            is_iface = (uu___1699_24153.is_iface);
            admit = (uu___1699_24153.admit);
            lax = (uu___1699_24153.lax);
            lax_universes = (uu___1699_24153.lax_universes);
            phase1 = (uu___1699_24153.phase1);
            failhard = (uu___1699_24153.failhard);
            nosynth = (uu___1699_24153.nosynth);
            uvar_subtyping = (uu___1699_24153.uvar_subtyping);
            tc_term = (uu___1699_24153.tc_term);
            type_of = (uu___1699_24153.type_of);
            universe_of = (uu___1699_24153.universe_of);
            check_type_of = (uu___1699_24153.check_type_of);
            use_bv_sorts = (uu___1699_24153.use_bv_sorts);
            qtbl_name_and_index = (uu___1699_24153.qtbl_name_and_index);
            normalized_eff_names = (uu___1699_24153.normalized_eff_names);
            fv_delta_depths = (uu___1699_24153.fv_delta_depths);
            proof_ns = (uu___1699_24153.proof_ns);
            synth_hook = (uu___1699_24153.synth_hook);
            try_solve_implicits_hook =
              (uu___1699_24153.try_solve_implicits_hook);
            splice = (uu___1699_24153.splice);
            mpreprocess = (uu___1699_24153.mpreprocess);
            postprocess = (uu___1699_24153.postprocess);
            identifier_info = (uu___1699_24153.identifier_info);
            tc_hooks = (uu___1699_24153.tc_hooks);
            dsenv = (uu___1699_24153.dsenv);
            nbe = (uu___1699_24153.nbe);
            strict_args_tab = (uu___1699_24153.strict_args_tab);
            erasable_types_tab = (uu___1699_24153.erasable_types_tab)
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
        let uu____24182 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24250  ->
                  match uu____24250 with
                  | (m1,n1,uu____24268,uu____24269) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24182 with
        | FStar_Pervasives_Native.Some (uu____24294,uu____24295,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24340 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24415 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24415
                  (fun uu____24436  ->
                     match uu____24436 with
                     | (c1,g1) ->
                         let uu____24447 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24447
                           (fun uu____24468  ->
                              match uu____24468 with
                              | (c2,g2) ->
                                  let uu____24479 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24479)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24601 = l1 u t e  in
                              l2 u t uu____24601))
                | uu____24602 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24670  ->
                    match uu____24670 with
                    | (e,uu____24678) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24701 =
            match uu____24701 with
            | (i,j) ->
                let uu____24712 = FStar_Ident.lid_equals i j  in
                if uu____24712
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____24719  ->
                       FStar_Pervasives_Native.Some uu____24719)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24748 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24758 = FStar_Ident.lid_equals i k  in
                        if uu____24758
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24772 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24772
                                  then []
                                  else
                                    (let uu____24779 =
                                       let uu____24788 =
                                         find_edge order1 (i, k)  in
                                       let uu____24791 =
                                         find_edge order1 (k, j)  in
                                       (uu____24788, uu____24791)  in
                                     match uu____24779 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24806 =
                                           compose_edges e1 e2  in
                                         [uu____24806]
                                     | uu____24807 -> [])))))
                 in
              FStar_List.append order1 uu____24748  in
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
                  let uu____24837 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24840 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____24840
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24837
                  then
                    let uu____24847 =
                      let uu____24853 =
                        let uu____24855 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____24855
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24853)
                       in
                    let uu____24859 = get_range env1  in
                    FStar_Errors.raise_error uu____24847 uu____24859
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____24937 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24937
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24989 =
                                             let uu____24998 =
                                               find_edge order2 (i, k)  in
                                             let uu____25001 =
                                               find_edge order2 (j, k)  in
                                             (uu____24998, uu____25001)  in
                                           match uu____24989 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25043,uu____25044)
                                                    ->
                                                    let uu____25051 =
                                                      let uu____25058 =
                                                        let uu____25060 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25060
                                                         in
                                                      let uu____25063 =
                                                        let uu____25065 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25065
                                                         in
                                                      (uu____25058,
                                                        uu____25063)
                                                       in
                                                    (match uu____25051 with
                                                     | (true ,true ) ->
                                                         let uu____25082 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25082
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
                                           | uu____25125 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25177 =
                                   let uu____25179 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25179
                                     FStar_Util.is_some
                                    in
                                 if uu____25177
                                 then
                                   let uu____25228 =
                                     let uu____25234 =
                                       let uu____25236 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25238 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25240 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25242 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25236 uu____25238 uu____25240
                                         uu____25242
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25234)
                                      in
                                   FStar_Errors.raise_error uu____25228
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1820_25281 = env1.effects  in
             {
               decls = (uu___1820_25281.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1820_25281.polymonadic_binds)
             }  in
           let uu___1823_25282 = env1  in
           {
             solver = (uu___1823_25282.solver);
             range = (uu___1823_25282.range);
             curmodule = (uu___1823_25282.curmodule);
             gamma = (uu___1823_25282.gamma);
             gamma_sig = (uu___1823_25282.gamma_sig);
             gamma_cache = (uu___1823_25282.gamma_cache);
             modules = (uu___1823_25282.modules);
             expected_typ = (uu___1823_25282.expected_typ);
             sigtab = (uu___1823_25282.sigtab);
             attrtab = (uu___1823_25282.attrtab);
             instantiate_imp = (uu___1823_25282.instantiate_imp);
             effects = effects1;
             generalize = (uu___1823_25282.generalize);
             letrecs = (uu___1823_25282.letrecs);
             top_level = (uu___1823_25282.top_level);
             check_uvars = (uu___1823_25282.check_uvars);
             use_eq = (uu___1823_25282.use_eq);
             use_eq_strict = (uu___1823_25282.use_eq_strict);
             is_iface = (uu___1823_25282.is_iface);
             admit = (uu___1823_25282.admit);
             lax = (uu___1823_25282.lax);
             lax_universes = (uu___1823_25282.lax_universes);
             phase1 = (uu___1823_25282.phase1);
             failhard = (uu___1823_25282.failhard);
             nosynth = (uu___1823_25282.nosynth);
             uvar_subtyping = (uu___1823_25282.uvar_subtyping);
             tc_term = (uu___1823_25282.tc_term);
             type_of = (uu___1823_25282.type_of);
             universe_of = (uu___1823_25282.universe_of);
             check_type_of = (uu___1823_25282.check_type_of);
             use_bv_sorts = (uu___1823_25282.use_bv_sorts);
             qtbl_name_and_index = (uu___1823_25282.qtbl_name_and_index);
             normalized_eff_names = (uu___1823_25282.normalized_eff_names);
             fv_delta_depths = (uu___1823_25282.fv_delta_depths);
             proof_ns = (uu___1823_25282.proof_ns);
             synth_hook = (uu___1823_25282.synth_hook);
             try_solve_implicits_hook =
               (uu___1823_25282.try_solve_implicits_hook);
             splice = (uu___1823_25282.splice);
             mpreprocess = (uu___1823_25282.mpreprocess);
             postprocess = (uu___1823_25282.postprocess);
             identifier_info = (uu___1823_25282.identifier_info);
             tc_hooks = (uu___1823_25282.tc_hooks);
             dsenv = (uu___1823_25282.dsenv);
             nbe = (uu___1823_25282.nbe);
             strict_args_tab = (uu___1823_25282.strict_args_tab);
             erasable_types_tab = (uu___1823_25282.erasable_types_tab)
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
              let uu____25330 = FStar_Ident.string_of_lid m  in
              let uu____25332 = FStar_Ident.string_of_lid n  in
              let uu____25334 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25330 uu____25332 uu____25334
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25343 =
              let uu____25345 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25345 FStar_Util.is_some  in
            if uu____25343
            then
              let uu____25382 =
                let uu____25388 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25388)
                 in
              FStar_Errors.raise_error uu____25382 env1.range
            else
              (let uu____25394 =
                 let uu____25396 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25396 FStar_Util.is_some  in
               if uu____25394
               then
                 let uu____25421 =
                   let uu____25427 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25427)
                    in
                 FStar_Errors.raise_error uu____25421 env1.range
               else
                 (let uu___1838_25433 = env1  in
                  {
                    solver = (uu___1838_25433.solver);
                    range = (uu___1838_25433.range);
                    curmodule = (uu___1838_25433.curmodule);
                    gamma = (uu___1838_25433.gamma);
                    gamma_sig = (uu___1838_25433.gamma_sig);
                    gamma_cache = (uu___1838_25433.gamma_cache);
                    modules = (uu___1838_25433.modules);
                    expected_typ = (uu___1838_25433.expected_typ);
                    sigtab = (uu___1838_25433.sigtab);
                    attrtab = (uu___1838_25433.attrtab);
                    instantiate_imp = (uu___1838_25433.instantiate_imp);
                    effects =
                      (let uu___1840_25435 = env1.effects  in
                       {
                         decls = (uu___1840_25435.decls);
                         order = (uu___1840_25435.order);
                         joins = (uu___1840_25435.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1838_25433.generalize);
                    letrecs = (uu___1838_25433.letrecs);
                    top_level = (uu___1838_25433.top_level);
                    check_uvars = (uu___1838_25433.check_uvars);
                    use_eq = (uu___1838_25433.use_eq);
                    use_eq_strict = (uu___1838_25433.use_eq_strict);
                    is_iface = (uu___1838_25433.is_iface);
                    admit = (uu___1838_25433.admit);
                    lax = (uu___1838_25433.lax);
                    lax_universes = (uu___1838_25433.lax_universes);
                    phase1 = (uu___1838_25433.phase1);
                    failhard = (uu___1838_25433.failhard);
                    nosynth = (uu___1838_25433.nosynth);
                    uvar_subtyping = (uu___1838_25433.uvar_subtyping);
                    tc_term = (uu___1838_25433.tc_term);
                    type_of = (uu___1838_25433.type_of);
                    universe_of = (uu___1838_25433.universe_of);
                    check_type_of = (uu___1838_25433.check_type_of);
                    use_bv_sorts = (uu___1838_25433.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1838_25433.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1838_25433.normalized_eff_names);
                    fv_delta_depths = (uu___1838_25433.fv_delta_depths);
                    proof_ns = (uu___1838_25433.proof_ns);
                    synth_hook = (uu___1838_25433.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1838_25433.try_solve_implicits_hook);
                    splice = (uu___1838_25433.splice);
                    mpreprocess = (uu___1838_25433.mpreprocess);
                    postprocess = (uu___1838_25433.postprocess);
                    identifier_info = (uu___1838_25433.identifier_info);
                    tc_hooks = (uu___1838_25433.tc_hooks);
                    dsenv = (uu___1838_25433.dsenv);
                    nbe = (uu___1838_25433.nbe);
                    strict_args_tab = (uu___1838_25433.strict_args_tab);
                    erasable_types_tab = (uu___1838_25433.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1844_25507 = env1  in
      {
        solver = (uu___1844_25507.solver);
        range = (uu___1844_25507.range);
        curmodule = (uu___1844_25507.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1844_25507.gamma_sig);
        gamma_cache = (uu___1844_25507.gamma_cache);
        modules = (uu___1844_25507.modules);
        expected_typ = (uu___1844_25507.expected_typ);
        sigtab = (uu___1844_25507.sigtab);
        attrtab = (uu___1844_25507.attrtab);
        instantiate_imp = (uu___1844_25507.instantiate_imp);
        effects = (uu___1844_25507.effects);
        generalize = (uu___1844_25507.generalize);
        letrecs = (uu___1844_25507.letrecs);
        top_level = (uu___1844_25507.top_level);
        check_uvars = (uu___1844_25507.check_uvars);
        use_eq = (uu___1844_25507.use_eq);
        use_eq_strict = (uu___1844_25507.use_eq_strict);
        is_iface = (uu___1844_25507.is_iface);
        admit = (uu___1844_25507.admit);
        lax = (uu___1844_25507.lax);
        lax_universes = (uu___1844_25507.lax_universes);
        phase1 = (uu___1844_25507.phase1);
        failhard = (uu___1844_25507.failhard);
        nosynth = (uu___1844_25507.nosynth);
        uvar_subtyping = (uu___1844_25507.uvar_subtyping);
        tc_term = (uu___1844_25507.tc_term);
        type_of = (uu___1844_25507.type_of);
        universe_of = (uu___1844_25507.universe_of);
        check_type_of = (uu___1844_25507.check_type_of);
        use_bv_sorts = (uu___1844_25507.use_bv_sorts);
        qtbl_name_and_index = (uu___1844_25507.qtbl_name_and_index);
        normalized_eff_names = (uu___1844_25507.normalized_eff_names);
        fv_delta_depths = (uu___1844_25507.fv_delta_depths);
        proof_ns = (uu___1844_25507.proof_ns);
        synth_hook = (uu___1844_25507.synth_hook);
        try_solve_implicits_hook = (uu___1844_25507.try_solve_implicits_hook);
        splice = (uu___1844_25507.splice);
        mpreprocess = (uu___1844_25507.mpreprocess);
        postprocess = (uu___1844_25507.postprocess);
        identifier_info = (uu___1844_25507.identifier_info);
        tc_hooks = (uu___1844_25507.tc_hooks);
        dsenv = (uu___1844_25507.dsenv);
        nbe = (uu___1844_25507.nbe);
        strict_args_tab = (uu___1844_25507.strict_args_tab);
        erasable_types_tab = (uu___1844_25507.erasable_types_tab)
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
            (let uu___1857_25565 = env1  in
             {
               solver = (uu___1857_25565.solver);
               range = (uu___1857_25565.range);
               curmodule = (uu___1857_25565.curmodule);
               gamma = rest;
               gamma_sig = (uu___1857_25565.gamma_sig);
               gamma_cache = (uu___1857_25565.gamma_cache);
               modules = (uu___1857_25565.modules);
               expected_typ = (uu___1857_25565.expected_typ);
               sigtab = (uu___1857_25565.sigtab);
               attrtab = (uu___1857_25565.attrtab);
               instantiate_imp = (uu___1857_25565.instantiate_imp);
               effects = (uu___1857_25565.effects);
               generalize = (uu___1857_25565.generalize);
               letrecs = (uu___1857_25565.letrecs);
               top_level = (uu___1857_25565.top_level);
               check_uvars = (uu___1857_25565.check_uvars);
               use_eq = (uu___1857_25565.use_eq);
               use_eq_strict = (uu___1857_25565.use_eq_strict);
               is_iface = (uu___1857_25565.is_iface);
               admit = (uu___1857_25565.admit);
               lax = (uu___1857_25565.lax);
               lax_universes = (uu___1857_25565.lax_universes);
               phase1 = (uu___1857_25565.phase1);
               failhard = (uu___1857_25565.failhard);
               nosynth = (uu___1857_25565.nosynth);
               uvar_subtyping = (uu___1857_25565.uvar_subtyping);
               tc_term = (uu___1857_25565.tc_term);
               type_of = (uu___1857_25565.type_of);
               universe_of = (uu___1857_25565.universe_of);
               check_type_of = (uu___1857_25565.check_type_of);
               use_bv_sorts = (uu___1857_25565.use_bv_sorts);
               qtbl_name_and_index = (uu___1857_25565.qtbl_name_and_index);
               normalized_eff_names = (uu___1857_25565.normalized_eff_names);
               fv_delta_depths = (uu___1857_25565.fv_delta_depths);
               proof_ns = (uu___1857_25565.proof_ns);
               synth_hook = (uu___1857_25565.synth_hook);
               try_solve_implicits_hook =
                 (uu___1857_25565.try_solve_implicits_hook);
               splice = (uu___1857_25565.splice);
               mpreprocess = (uu___1857_25565.mpreprocess);
               postprocess = (uu___1857_25565.postprocess);
               identifier_info = (uu___1857_25565.identifier_info);
               tc_hooks = (uu___1857_25565.tc_hooks);
               dsenv = (uu___1857_25565.dsenv);
               nbe = (uu___1857_25565.nbe);
               strict_args_tab = (uu___1857_25565.strict_args_tab);
               erasable_types_tab = (uu___1857_25565.erasable_types_tab)
             }))
    | uu____25566 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25595  ->
             match uu____25595 with | (x,uu____25603) -> push_bv env2 x) env1
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
            let uu___1871_25638 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1871_25638.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1871_25638.FStar_Syntax_Syntax.index);
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
        let uu____25711 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25711 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____25739 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25739)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1892_25755 = env1  in
      {
        solver = (uu___1892_25755.solver);
        range = (uu___1892_25755.range);
        curmodule = (uu___1892_25755.curmodule);
        gamma = (uu___1892_25755.gamma);
        gamma_sig = (uu___1892_25755.gamma_sig);
        gamma_cache = (uu___1892_25755.gamma_cache);
        modules = (uu___1892_25755.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1892_25755.sigtab);
        attrtab = (uu___1892_25755.attrtab);
        instantiate_imp = (uu___1892_25755.instantiate_imp);
        effects = (uu___1892_25755.effects);
        generalize = (uu___1892_25755.generalize);
        letrecs = (uu___1892_25755.letrecs);
        top_level = (uu___1892_25755.top_level);
        check_uvars = (uu___1892_25755.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1892_25755.use_eq_strict);
        is_iface = (uu___1892_25755.is_iface);
        admit = (uu___1892_25755.admit);
        lax = (uu___1892_25755.lax);
        lax_universes = (uu___1892_25755.lax_universes);
        phase1 = (uu___1892_25755.phase1);
        failhard = (uu___1892_25755.failhard);
        nosynth = (uu___1892_25755.nosynth);
        uvar_subtyping = (uu___1892_25755.uvar_subtyping);
        tc_term = (uu___1892_25755.tc_term);
        type_of = (uu___1892_25755.type_of);
        universe_of = (uu___1892_25755.universe_of);
        check_type_of = (uu___1892_25755.check_type_of);
        use_bv_sorts = (uu___1892_25755.use_bv_sorts);
        qtbl_name_and_index = (uu___1892_25755.qtbl_name_and_index);
        normalized_eff_names = (uu___1892_25755.normalized_eff_names);
        fv_delta_depths = (uu___1892_25755.fv_delta_depths);
        proof_ns = (uu___1892_25755.proof_ns);
        synth_hook = (uu___1892_25755.synth_hook);
        try_solve_implicits_hook = (uu___1892_25755.try_solve_implicits_hook);
        splice = (uu___1892_25755.splice);
        mpreprocess = (uu___1892_25755.mpreprocess);
        postprocess = (uu___1892_25755.postprocess);
        identifier_info = (uu___1892_25755.identifier_info);
        tc_hooks = (uu___1892_25755.tc_hooks);
        dsenv = (uu___1892_25755.dsenv);
        nbe = (uu___1892_25755.nbe);
        strict_args_tab = (uu___1892_25755.strict_args_tab);
        erasable_types_tab = (uu___1892_25755.erasable_types_tab)
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
    let uu____25786 = expected_typ env_  in
    ((let uu___1899_25792 = env_  in
      {
        solver = (uu___1899_25792.solver);
        range = (uu___1899_25792.range);
        curmodule = (uu___1899_25792.curmodule);
        gamma = (uu___1899_25792.gamma);
        gamma_sig = (uu___1899_25792.gamma_sig);
        gamma_cache = (uu___1899_25792.gamma_cache);
        modules = (uu___1899_25792.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1899_25792.sigtab);
        attrtab = (uu___1899_25792.attrtab);
        instantiate_imp = (uu___1899_25792.instantiate_imp);
        effects = (uu___1899_25792.effects);
        generalize = (uu___1899_25792.generalize);
        letrecs = (uu___1899_25792.letrecs);
        top_level = (uu___1899_25792.top_level);
        check_uvars = (uu___1899_25792.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1899_25792.use_eq_strict);
        is_iface = (uu___1899_25792.is_iface);
        admit = (uu___1899_25792.admit);
        lax = (uu___1899_25792.lax);
        lax_universes = (uu___1899_25792.lax_universes);
        phase1 = (uu___1899_25792.phase1);
        failhard = (uu___1899_25792.failhard);
        nosynth = (uu___1899_25792.nosynth);
        uvar_subtyping = (uu___1899_25792.uvar_subtyping);
        tc_term = (uu___1899_25792.tc_term);
        type_of = (uu___1899_25792.type_of);
        universe_of = (uu___1899_25792.universe_of);
        check_type_of = (uu___1899_25792.check_type_of);
        use_bv_sorts = (uu___1899_25792.use_bv_sorts);
        qtbl_name_and_index = (uu___1899_25792.qtbl_name_and_index);
        normalized_eff_names = (uu___1899_25792.normalized_eff_names);
        fv_delta_depths = (uu___1899_25792.fv_delta_depths);
        proof_ns = (uu___1899_25792.proof_ns);
        synth_hook = (uu___1899_25792.synth_hook);
        try_solve_implicits_hook = (uu___1899_25792.try_solve_implicits_hook);
        splice = (uu___1899_25792.splice);
        mpreprocess = (uu___1899_25792.mpreprocess);
        postprocess = (uu___1899_25792.postprocess);
        identifier_info = (uu___1899_25792.identifier_info);
        tc_hooks = (uu___1899_25792.tc_hooks);
        dsenv = (uu___1899_25792.dsenv);
        nbe = (uu___1899_25792.nbe);
        strict_args_tab = (uu___1899_25792.strict_args_tab);
        erasable_types_tab = (uu___1899_25792.erasable_types_tab)
      }), uu____25786)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25804 =
      let uu____25805 = FStar_Ident.id_of_text ""  in [uu____25805]  in
    FStar_Ident.lid_of_ids uu____25804  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____25812 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25812
        then
          let uu____25817 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25817 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1907_25845 = env1  in
       {
         solver = (uu___1907_25845.solver);
         range = (uu___1907_25845.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1907_25845.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1907_25845.expected_typ);
         sigtab = (uu___1907_25845.sigtab);
         attrtab = (uu___1907_25845.attrtab);
         instantiate_imp = (uu___1907_25845.instantiate_imp);
         effects = (uu___1907_25845.effects);
         generalize = (uu___1907_25845.generalize);
         letrecs = (uu___1907_25845.letrecs);
         top_level = (uu___1907_25845.top_level);
         check_uvars = (uu___1907_25845.check_uvars);
         use_eq = (uu___1907_25845.use_eq);
         use_eq_strict = (uu___1907_25845.use_eq_strict);
         is_iface = (uu___1907_25845.is_iface);
         admit = (uu___1907_25845.admit);
         lax = (uu___1907_25845.lax);
         lax_universes = (uu___1907_25845.lax_universes);
         phase1 = (uu___1907_25845.phase1);
         failhard = (uu___1907_25845.failhard);
         nosynth = (uu___1907_25845.nosynth);
         uvar_subtyping = (uu___1907_25845.uvar_subtyping);
         tc_term = (uu___1907_25845.tc_term);
         type_of = (uu___1907_25845.type_of);
         universe_of = (uu___1907_25845.universe_of);
         check_type_of = (uu___1907_25845.check_type_of);
         use_bv_sorts = (uu___1907_25845.use_bv_sorts);
         qtbl_name_and_index = (uu___1907_25845.qtbl_name_and_index);
         normalized_eff_names = (uu___1907_25845.normalized_eff_names);
         fv_delta_depths = (uu___1907_25845.fv_delta_depths);
         proof_ns = (uu___1907_25845.proof_ns);
         synth_hook = (uu___1907_25845.synth_hook);
         try_solve_implicits_hook =
           (uu___1907_25845.try_solve_implicits_hook);
         splice = (uu___1907_25845.splice);
         mpreprocess = (uu___1907_25845.mpreprocess);
         postprocess = (uu___1907_25845.postprocess);
         identifier_info = (uu___1907_25845.identifier_info);
         tc_hooks = (uu___1907_25845.tc_hooks);
         dsenv = (uu___1907_25845.dsenv);
         nbe = (uu___1907_25845.nbe);
         strict_args_tab = (uu___1907_25845.strict_args_tab);
         erasable_types_tab = (uu___1907_25845.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25897)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____25901,(uu____25902,t)))::tl
          ->
          let uu____25923 =
            let uu____25926 = FStar_Syntax_Free.uvars t  in
            ext out uu____25926  in
          aux uu____25923 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25929;
            FStar_Syntax_Syntax.index = uu____25930;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____25938 =
            let uu____25941 = FStar_Syntax_Free.uvars t  in
            ext out uu____25941  in
          aux uu____25938 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25999)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26003,(uu____26004,t)))::tl
          ->
          let uu____26025 =
            let uu____26028 = FStar_Syntax_Free.univs t  in
            ext out uu____26028  in
          aux uu____26025 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26031;
            FStar_Syntax_Syntax.index = uu____26032;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26040 =
            let uu____26043 = FStar_Syntax_Free.univs t  in
            ext out uu____26043  in
          aux uu____26040 tl
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
          let uu____26105 = FStar_Util.set_add uname out  in
          aux uu____26105 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26108,(uu____26109,t)))::tl
          ->
          let uu____26130 =
            let uu____26133 = FStar_Syntax_Free.univnames t  in
            ext out uu____26133  in
          aux uu____26130 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26136;
            FStar_Syntax_Syntax.index = uu____26137;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26145 =
            let uu____26148 = FStar_Syntax_Free.univnames t  in
            ext out uu____26148  in
          aux uu____26145 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26169  ->
            match uu___12_26169 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26173 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26186 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26197 =
      let uu____26206 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26206
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26197 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26254 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26267  ->
              match uu___13_26267 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26270 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26270
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26274 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26274
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26278) ->
                  let uu____26295 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26295))
       in
    FStar_All.pipe_right uu____26254 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26309  ->
    match uu___14_26309 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26315 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26315
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26338  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26393) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26426,uu____26427) -> false  in
      let uu____26441 =
        FStar_List.tryFind
          (fun uu____26463  ->
             match uu____26463 with | (p,uu____26474) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26441 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26493,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26523 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26523
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2050_26545 = e  in
        {
          solver = (uu___2050_26545.solver);
          range = (uu___2050_26545.range);
          curmodule = (uu___2050_26545.curmodule);
          gamma = (uu___2050_26545.gamma);
          gamma_sig = (uu___2050_26545.gamma_sig);
          gamma_cache = (uu___2050_26545.gamma_cache);
          modules = (uu___2050_26545.modules);
          expected_typ = (uu___2050_26545.expected_typ);
          sigtab = (uu___2050_26545.sigtab);
          attrtab = (uu___2050_26545.attrtab);
          instantiate_imp = (uu___2050_26545.instantiate_imp);
          effects = (uu___2050_26545.effects);
          generalize = (uu___2050_26545.generalize);
          letrecs = (uu___2050_26545.letrecs);
          top_level = (uu___2050_26545.top_level);
          check_uvars = (uu___2050_26545.check_uvars);
          use_eq = (uu___2050_26545.use_eq);
          use_eq_strict = (uu___2050_26545.use_eq_strict);
          is_iface = (uu___2050_26545.is_iface);
          admit = (uu___2050_26545.admit);
          lax = (uu___2050_26545.lax);
          lax_universes = (uu___2050_26545.lax_universes);
          phase1 = (uu___2050_26545.phase1);
          failhard = (uu___2050_26545.failhard);
          nosynth = (uu___2050_26545.nosynth);
          uvar_subtyping = (uu___2050_26545.uvar_subtyping);
          tc_term = (uu___2050_26545.tc_term);
          type_of = (uu___2050_26545.type_of);
          universe_of = (uu___2050_26545.universe_of);
          check_type_of = (uu___2050_26545.check_type_of);
          use_bv_sorts = (uu___2050_26545.use_bv_sorts);
          qtbl_name_and_index = (uu___2050_26545.qtbl_name_and_index);
          normalized_eff_names = (uu___2050_26545.normalized_eff_names);
          fv_delta_depths = (uu___2050_26545.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2050_26545.synth_hook);
          try_solve_implicits_hook =
            (uu___2050_26545.try_solve_implicits_hook);
          splice = (uu___2050_26545.splice);
          mpreprocess = (uu___2050_26545.mpreprocess);
          postprocess = (uu___2050_26545.postprocess);
          identifier_info = (uu___2050_26545.identifier_info);
          tc_hooks = (uu___2050_26545.tc_hooks);
          dsenv = (uu___2050_26545.dsenv);
          nbe = (uu___2050_26545.nbe);
          strict_args_tab = (uu___2050_26545.strict_args_tab);
          erasable_types_tab = (uu___2050_26545.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2059_26593 = e  in
      {
        solver = (uu___2059_26593.solver);
        range = (uu___2059_26593.range);
        curmodule = (uu___2059_26593.curmodule);
        gamma = (uu___2059_26593.gamma);
        gamma_sig = (uu___2059_26593.gamma_sig);
        gamma_cache = (uu___2059_26593.gamma_cache);
        modules = (uu___2059_26593.modules);
        expected_typ = (uu___2059_26593.expected_typ);
        sigtab = (uu___2059_26593.sigtab);
        attrtab = (uu___2059_26593.attrtab);
        instantiate_imp = (uu___2059_26593.instantiate_imp);
        effects = (uu___2059_26593.effects);
        generalize = (uu___2059_26593.generalize);
        letrecs = (uu___2059_26593.letrecs);
        top_level = (uu___2059_26593.top_level);
        check_uvars = (uu___2059_26593.check_uvars);
        use_eq = (uu___2059_26593.use_eq);
        use_eq_strict = (uu___2059_26593.use_eq_strict);
        is_iface = (uu___2059_26593.is_iface);
        admit = (uu___2059_26593.admit);
        lax = (uu___2059_26593.lax);
        lax_universes = (uu___2059_26593.lax_universes);
        phase1 = (uu___2059_26593.phase1);
        failhard = (uu___2059_26593.failhard);
        nosynth = (uu___2059_26593.nosynth);
        uvar_subtyping = (uu___2059_26593.uvar_subtyping);
        tc_term = (uu___2059_26593.tc_term);
        type_of = (uu___2059_26593.type_of);
        universe_of = (uu___2059_26593.universe_of);
        check_type_of = (uu___2059_26593.check_type_of);
        use_bv_sorts = (uu___2059_26593.use_bv_sorts);
        qtbl_name_and_index = (uu___2059_26593.qtbl_name_and_index);
        normalized_eff_names = (uu___2059_26593.normalized_eff_names);
        fv_delta_depths = (uu___2059_26593.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2059_26593.synth_hook);
        try_solve_implicits_hook = (uu___2059_26593.try_solve_implicits_hook);
        splice = (uu___2059_26593.splice);
        mpreprocess = (uu___2059_26593.mpreprocess);
        postprocess = (uu___2059_26593.postprocess);
        identifier_info = (uu___2059_26593.identifier_info);
        tc_hooks = (uu___2059_26593.tc_hooks);
        dsenv = (uu___2059_26593.dsenv);
        nbe = (uu___2059_26593.nbe);
        strict_args_tab = (uu___2059_26593.strict_args_tab);
        erasable_types_tab = (uu___2059_26593.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26609 = FStar_Syntax_Free.names t  in
      let uu____26612 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26609 uu____26612
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26635 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26635
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26645 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26645
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____26666 =
      match uu____26666 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26686 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26686)
       in
    let uu____26694 =
      let uu____26698 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____26698 FStar_List.rev  in
    FStar_All.pipe_right uu____26694 (FStar_String.concat " ")
  
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
                  (let uu____26766 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26766 with
                   | FStar_Pervasives_Native.Some uu____26770 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26773 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26783;
        FStar_TypeChecker_Common.univ_ineqs = uu____26784;
        FStar_TypeChecker_Common.implicits = uu____26785;_} -> true
    | uu____26795 -> false
  
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
          let uu___2103_26817 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2103_26817.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2103_26817.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2103_26817.FStar_TypeChecker_Common.implicits)
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
          let uu____26856 = FStar_Options.defensive ()  in
          if uu____26856
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26862 =
              let uu____26864 =
                let uu____26866 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26866  in
              Prims.op_Negation uu____26864  in
            (if uu____26862
             then
               let uu____26873 =
                 let uu____26879 =
                   let uu____26881 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26883 =
                     let uu____26885 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26885
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26881 uu____26883
                    in
                 (FStar_Errors.Warning_Defensive, uu____26879)  in
               FStar_Errors.log_issue rng uu____26873
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
          let uu____26925 =
            let uu____26927 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26927  in
          if uu____26925
          then ()
          else
            (let uu____26932 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26932 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26958 =
            let uu____26960 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26960  in
          if uu____26958
          then ()
          else
            (let uu____26965 = bound_vars e  in
             def_check_closed_in rng msg uu____26965 t)
  
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
          let uu___2140_27004 = g  in
          let uu____27005 =
            let uu____27006 =
              let uu____27007 =
                let uu____27014 =
                  let uu____27015 =
                    let uu____27032 =
                      let uu____27043 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27043]  in
                    (f, uu____27032)  in
                  FStar_Syntax_Syntax.Tm_app uu____27015  in
                FStar_Syntax_Syntax.mk uu____27014  in
              uu____27007 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27080  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27080) uu____27006
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27005;
            FStar_TypeChecker_Common.deferred =
              (uu___2140_27004.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2140_27004.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2140_27004.FStar_TypeChecker_Common.implicits)
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
          let uu___2147_27098 = g  in
          let uu____27099 =
            let uu____27100 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27100  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27099;
            FStar_TypeChecker_Common.deferred =
              (uu___2147_27098.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2147_27098.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2147_27098.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2152_27117 = g  in
          let uu____27118 =
            let uu____27119 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27119  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27118;
            FStar_TypeChecker_Common.deferred =
              (uu___2152_27117.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2152_27117.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2152_27117.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2156_27121 = g  in
          let uu____27122 =
            let uu____27123 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27123  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27122;
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27121.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27121.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27121.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27130 ->
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
                       let uu____27207 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27207
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2179_27214 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2179_27214.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2179_27214.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2179_27214.FStar_TypeChecker_Common.implicits)
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
               let uu____27248 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27248
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
            let uu___2194_27275 = g  in
            let uu____27276 =
              let uu____27277 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27277  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27276;
              FStar_TypeChecker_Common.deferred =
                (uu___2194_27275.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2194_27275.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2194_27275.FStar_TypeChecker_Common.implicits)
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
              let uu____27335 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27335 with
              | FStar_Pervasives_Native.Some
                  (uu____27360::(tm,uu____27362)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27426 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27444 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27444;
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
                    (let uu____27476 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27476
                     then
                       let uu____27480 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27480
                     else ());
                    (let g =
                       let uu___2218_27486 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2218_27486.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2218_27486.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2218_27486.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27540 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27597  ->
                      fun b  ->
                        match uu____27597 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27639 =
                              let uu____27652 = reason b  in
                              new_implicit_var_aux uu____27652 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27639 with
                             | (t,uu____27669,g_t) ->
                                 let uu____27683 =
                                   let uu____27686 =
                                     let uu____27689 =
                                       let uu____27690 =
                                         let uu____27697 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27697, t)  in
                                       FStar_Syntax_Syntax.NT uu____27690  in
                                     [uu____27689]  in
                                   FStar_List.append substs1 uu____27686  in
                                 let uu____27708 = conj_guard g g_t  in
                                 (uu____27683, (FStar_List.append uvars [t]),
                                   uu____27708))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27540
              (fun uu____27737  ->
                 match uu____27737 with | (uu____27754,uvars,g) -> (uvars, g))
  
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
                let uu____27795 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____27795 FStar_Util.must  in
              let uu____27812 = inst_tscheme_with post_ts [u]  in
              match uu____27812 with
              | (uu____27817,post) ->
                  let uu____27819 =
                    let uu____27824 =
                      let uu____27825 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____27825]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____27824  in
                  uu____27819 FStar_Pervasives_Native.None r
               in
            let uu____27858 =
              let uu____27863 =
                let uu____27864 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____27864]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____27863  in
            uu____27858 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____27900  -> ());
    push = (fun uu____27902  -> ());
    pop = (fun uu____27905  -> ());
    snapshot =
      (fun uu____27908  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____27927  -> fun uu____27928  -> ());
    encode_sig = (fun uu____27943  -> fun uu____27944  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____27950 =
             let uu____27957 = FStar_Options.peek ()  in (e, g, uu____27957)
              in
           [uu____27950]);
    solve = (fun uu____27973  -> fun uu____27974  -> fun uu____27975  -> ());
    finish = (fun uu____27982  -> ());
    refresh = (fun uu____27984  -> ())
  } 