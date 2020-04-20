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
    let uu____16392 =
      FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange  in
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
      | ((formals,t),uu____16494) ->
          let vs = mk_univ_subst formals us  in
          let uu____16518 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16518)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16535  ->
    match uu___1_16535 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16561  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16581 = inst_tscheme t  in
      match uu____16581 with
      | (us,t1) ->
          let uu____16592 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16592)
  
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
          let uu____16617 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16619 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16617 uu____16619
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
        fun uu____16646  ->
          match uu____16646 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16660 =
                    let uu____16662 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16666 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16670 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16672 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16662 uu____16666 uu____16670 uu____16672
                     in
                  failwith uu____16660)
               else ();
               (let uu____16677 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16677))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16695 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16706 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16717 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
      let uu____16731 =
        let uu____16733 = FStar_Ident.nsstr l  in
        let uu____16735 = FStar_Ident.string_of_lid cur  in
        uu____16733 = uu____16735  in
      if uu____16731
      then Yes
      else
        (let uu____16741 =
           let uu____16743 = FStar_Ident.nsstr l  in
           let uu____16745 = FStar_Ident.string_of_lid cur  in
           FStar_Util.starts_with uu____16743 uu____16745  in
         if uu____16741
         then
           let lns =
             let uu____16751 = FStar_Ident.ns_of_lid l  in
             let uu____16754 =
               let uu____16757 = FStar_Ident.ident_of_lid l  in [uu____16757]
                in
             FStar_List.append uu____16751 uu____16754  in
           let cur1 =
             let uu____16761 = FStar_Ident.ns_of_lid cur  in
             let uu____16764 =
               let uu____16767 = FStar_Ident.ident_of_lid cur  in
               [uu____16767]  in
             FStar_List.append uu____16761 uu____16764  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____16791) -> Maybe
             | (uu____16798,[]) -> No
             | (hd::tl,hd'::tl') when
                 let uu____16817 = FStar_Ident.text_of_id hd  in
                 let uu____16819 = FStar_Ident.text_of_id hd'  in
                 uu____16817 = uu____16819 -> aux tl tl'
             | uu____16822 -> No  in
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
        (let uu____16874 = FStar_Ident.string_of_lid lid  in
         FStar_Util.smap_add (gamma_cache env1) uu____16874 t);
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____16918 =
            let uu____16921 = FStar_Ident.string_of_lid lid  in
            FStar_Util.smap_try_find (gamma_cache env1) uu____16921  in
          match uu____16918 with
          | FStar_Pervasives_Native.None  ->
              let uu____16943 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_16987  ->
                     match uu___2_16987 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17026 = FStar_Ident.lid_equals lid l  in
                         if uu____17026
                         then
                           let uu____17049 =
                             let uu____17068 =
                               let uu____17083 = inst_tscheme t  in
                               FStar_Util.Inl uu____17083  in
                             let uu____17098 = FStar_Ident.range_of_lid l  in
                             (uu____17068, uu____17098)  in
                           FStar_Pervasives_Native.Some uu____17049
                         else FStar_Pervasives_Native.None
                     | uu____17151 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16943
                (fun uu____17189  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17199  ->
                        match uu___3_17199 with
                        | (uu____17202,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17204);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17205;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17206;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17207;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17208;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17209;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17231 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17231
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
                                  uu____17283 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17290 -> cache t  in
                            let uu____17291 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17291 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17297 =
                                   let uu____17298 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17298)
                                    in
                                 maybe_cache uu____17297)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17369 = find_in_sigtab env1 lid  in
         match uu____17369 with
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
      let uu____17450 = lookup_qname env1 lid  in
      match uu____17450 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17471,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17585 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17585 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17630 =
          let uu____17633 = lookup_attr env2 attr  in se1 :: uu____17633  in
        FStar_Util.smap_add (attrtab env2) attr uu____17630  in
      FStar_List.iter
        (fun attr  ->
           let uu____17643 =
             let uu____17644 = FStar_Syntax_Subst.compress attr  in
             uu____17644.FStar_Syntax_Syntax.n  in
           match uu____17643 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17648 =
                 let uu____17650 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_Ident.string_of_lid uu____17650  in
               add_one env1 se uu____17648
           | uu____17651 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17674) ->
          add_sigelts env1 ses
      | uu____17683 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                let uu____17691 = FStar_Ident.string_of_lid l  in
                FStar_Util.smap_add (sigtab env1) uu____17691 se) lids;
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
        (fun uu___4_17725  ->
           match uu___4_17725 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               let uu____17735 =
                 let uu____17742 =
                   FStar_Ident.range_of_id id.FStar_Syntax_Syntax.ppname  in
                 ((id.FStar_Syntax_Syntax.sort), uu____17742)  in
               FStar_Pervasives_Native.Some uu____17735
           | uu____17751 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17813,lb::[]),uu____17815) ->
            let uu____17824 =
              let uu____17833 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17842 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17833, uu____17842)  in
            FStar_Pervasives_Native.Some uu____17824
        | FStar_Syntax_Syntax.Sig_let ((uu____17855,lbs),uu____17857) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17889 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17902 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17902
                     then
                       let uu____17915 =
                         let uu____17924 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17933 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17924, uu____17933)  in
                       FStar_Pervasives_Native.Some uu____17915
                     else FStar_Pervasives_Native.None)
        | uu____17956 -> FStar_Pervasives_Native.None
  
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
                    let uu____18048 =
                      let uu____18050 =
                        let uu____18052 =
                          FStar_Ident.string_of_lid
                            ne.FStar_Syntax_Syntax.mname
                           in
                        let uu____18054 =
                          let uu____18056 =
                            let uu____18058 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18064 =
                              let uu____18066 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18066  in
                            Prims.op_Hat uu____18058 uu____18064  in
                          Prims.op_Hat ", expected " uu____18056  in
                        Prims.op_Hat uu____18052 uu____18054  in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18050
                       in
                    failwith uu____18048
                  else ());
             (let uu____18073 =
                let uu____18082 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18082, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18073))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18102,uu____18103) ->
            let uu____18108 =
              let uu____18117 =
                let uu____18122 =
                  let uu____18123 =
                    let uu____18126 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18126  in
                  (us, uu____18123)  in
                inst_ts us_opt uu____18122  in
              (uu____18117, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18108
        | uu____18145 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18234 =
          match uu____18234 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18330,uvs,t,uu____18333,uu____18334,uu____18335);
                      FStar_Syntax_Syntax.sigrng = uu____18336;
                      FStar_Syntax_Syntax.sigquals = uu____18337;
                      FStar_Syntax_Syntax.sigmeta = uu____18338;
                      FStar_Syntax_Syntax.sigattrs = uu____18339;
                      FStar_Syntax_Syntax.sigopts = uu____18340;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18365 =
                     let uu____18374 = inst_tscheme1 (uvs, t)  in
                     (uu____18374, rng)  in
                   FStar_Pervasives_Native.Some uu____18365
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18398;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18400;
                      FStar_Syntax_Syntax.sigattrs = uu____18401;
                      FStar_Syntax_Syntax.sigopts = uu____18402;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18421 =
                     let uu____18423 = in_cur_mod env1 l  in
                     uu____18423 = Yes  in
                   if uu____18421
                   then
                     let uu____18435 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18435
                      then
                        let uu____18451 =
                          let uu____18460 = inst_tscheme1 (uvs, t)  in
                          (uu____18460, rng)  in
                        FStar_Pervasives_Native.Some uu____18451
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18493 =
                        let uu____18502 = inst_tscheme1 (uvs, t)  in
                        (uu____18502, rng)  in
                      FStar_Pervasives_Native.Some uu____18493)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18527,uu____18528);
                      FStar_Syntax_Syntax.sigrng = uu____18529;
                      FStar_Syntax_Syntax.sigquals = uu____18530;
                      FStar_Syntax_Syntax.sigmeta = uu____18531;
                      FStar_Syntax_Syntax.sigattrs = uu____18532;
                      FStar_Syntax_Syntax.sigopts = uu____18533;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18576 =
                          let uu____18585 = inst_tscheme1 (uvs, k)  in
                          (uu____18585, rng)  in
                        FStar_Pervasives_Native.Some uu____18576
                    | uu____18606 ->
                        let uu____18607 =
                          let uu____18616 =
                            let uu____18621 =
                              let uu____18622 =
                                let uu____18625 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18625
                                 in
                              (uvs, uu____18622)  in
                            inst_tscheme1 uu____18621  in
                          (uu____18616, rng)  in
                        FStar_Pervasives_Native.Some uu____18607)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18648,uu____18649);
                      FStar_Syntax_Syntax.sigrng = uu____18650;
                      FStar_Syntax_Syntax.sigquals = uu____18651;
                      FStar_Syntax_Syntax.sigmeta = uu____18652;
                      FStar_Syntax_Syntax.sigattrs = uu____18653;
                      FStar_Syntax_Syntax.sigopts = uu____18654;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18698 =
                          let uu____18707 = inst_tscheme_with (uvs, k) us  in
                          (uu____18707, rng)  in
                        FStar_Pervasives_Native.Some uu____18698
                    | uu____18728 ->
                        let uu____18729 =
                          let uu____18738 =
                            let uu____18743 =
                              let uu____18744 =
                                let uu____18747 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18747
                                 in
                              (uvs, uu____18744)  in
                            inst_tscheme_with uu____18743 us  in
                          (uu____18738, rng)  in
                        FStar_Pervasives_Native.Some uu____18729)
               | FStar_Util.Inr se ->
                   let uu____18783 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18804;
                          FStar_Syntax_Syntax.sigrng = uu____18805;
                          FStar_Syntax_Syntax.sigquals = uu____18806;
                          FStar_Syntax_Syntax.sigmeta = uu____18807;
                          FStar_Syntax_Syntax.sigattrs = uu____18808;
                          FStar_Syntax_Syntax.sigopts = uu____18809;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18826 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____18783
                     (FStar_Util.map_option
                        (fun uu____18874  ->
                           match uu____18874 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18905 =
          let uu____18916 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____18916 mapper  in
        match uu____18905 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18990 =
              let uu____19001 =
                let uu____19008 =
                  let uu___854_19011 = t  in
                  let uu____19012 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___854_19011.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19012;
                    FStar_Syntax_Syntax.vars =
                      (uu___854_19011.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19008)  in
              (uu____19001, r)  in
            FStar_Pervasives_Native.Some uu____18990
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19061 = lookup_qname env1 l  in
      match uu____19061 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19082 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19136 = try_lookup_bv env1 bv  in
      match uu____19136 with
      | FStar_Pervasives_Native.None  ->
          let uu____19151 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19151 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19167 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19168 =
            let uu____19169 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19169  in
          (uu____19167, uu____19168)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19191 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19191 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19257 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19257  in
          let uu____19258 =
            let uu____19267 =
              let uu____19272 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19272)  in
            (uu____19267, r1)  in
          FStar_Pervasives_Native.Some uu____19258
  
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
        let uu____19307 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19307 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19340,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19365 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19365  in
            let uu____19366 =
              let uu____19371 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19371, r1)  in
            FStar_Pervasives_Native.Some uu____19366
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19395 = try_lookup_lid env1 l  in
      match uu____19395 with
      | FStar_Pervasives_Native.None  ->
          let uu____19422 = name_not_found l  in
          let uu____19428 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19422 uu____19428
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19473  ->
              match uu___5_19473 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  let uu____19476 = FStar_Ident.text_of_id x  in
                  let uu____19478 = FStar_Ident.text_of_id y  in
                  uu____19476 = uu____19478
              | uu____19481 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19502 = lookup_qname env1 lid  in
      match uu____19502 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19511,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19514;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19516;
              FStar_Syntax_Syntax.sigattrs = uu____19517;
              FStar_Syntax_Syntax.sigopts = uu____19518;_},FStar_Pervasives_Native.None
            ),uu____19519)
          ->
          let uu____19570 =
            let uu____19577 =
              let uu____19578 =
                let uu____19581 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19581 t  in
              (uvs, uu____19578)  in
            (uu____19577, q)  in
          FStar_Pervasives_Native.Some uu____19570
      | uu____19594 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19616 = lookup_qname env1 lid  in
      match uu____19616 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19621,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19624;
              FStar_Syntax_Syntax.sigquals = uu____19625;
              FStar_Syntax_Syntax.sigmeta = uu____19626;
              FStar_Syntax_Syntax.sigattrs = uu____19627;
              FStar_Syntax_Syntax.sigopts = uu____19628;_},FStar_Pervasives_Native.None
            ),uu____19629)
          ->
          let uu____19680 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19680 (uvs, t)
      | uu____19685 ->
          let uu____19686 = name_not_found lid  in
          let uu____19692 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19686 uu____19692
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19712 = lookup_qname env1 lid  in
      match uu____19712 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19717,uvs,t,uu____19720,uu____19721,uu____19722);
              FStar_Syntax_Syntax.sigrng = uu____19723;
              FStar_Syntax_Syntax.sigquals = uu____19724;
              FStar_Syntax_Syntax.sigmeta = uu____19725;
              FStar_Syntax_Syntax.sigattrs = uu____19726;
              FStar_Syntax_Syntax.sigopts = uu____19727;_},FStar_Pervasives_Native.None
            ),uu____19728)
          ->
          let uu____19785 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19785 (uvs, t)
      | uu____19790 ->
          let uu____19791 = name_not_found lid  in
          let uu____19797 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19791 uu____19797
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____19820 = lookup_qname env1 lid  in
      match uu____19820 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19828,uu____19829,uu____19830,uu____19831,uu____19832,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19834;
              FStar_Syntax_Syntax.sigquals = uu____19835;
              FStar_Syntax_Syntax.sigmeta = uu____19836;
              FStar_Syntax_Syntax.sigattrs = uu____19837;
              FStar_Syntax_Syntax.sigopts = uu____19838;_},uu____19839),uu____19840)
          -> (true, dcs)
      | uu____19905 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____19921 = lookup_qname env1 lid  in
      match uu____19921 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19922,uu____19923,uu____19924,l,uu____19926,uu____19927);
              FStar_Syntax_Syntax.sigrng = uu____19928;
              FStar_Syntax_Syntax.sigquals = uu____19929;
              FStar_Syntax_Syntax.sigmeta = uu____19930;
              FStar_Syntax_Syntax.sigattrs = uu____19931;
              FStar_Syntax_Syntax.sigopts = uu____19932;_},uu____19933),uu____19934)
          -> l
      | uu____19993 ->
          let uu____19994 =
            let uu____19996 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19996  in
          failwith uu____19994
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20066)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20123) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20147 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20147
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20182 -> FStar_Pervasives_Native.None)
          | uu____20191 -> FStar_Pervasives_Native.None
  
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
        let uu____20253 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20253
  
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
        let uu____20286 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20286
  
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv  ->
    fun qn  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20310 =
        let uu____20312 = FStar_Ident.nsstr lid  in uu____20312 = "Prims"  in
      if uu____20310
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None  ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____20342,uu____20343) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20392),uu____20393) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20442 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20460 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20470 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20487 ->
                  let uu____20494 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20494
              | FStar_Syntax_Syntax.Sig_let ((uu____20495,lbs),uu____20497)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20513 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20513
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20520 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20536 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_assume uu____20546 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20553 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20554 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20555 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20568 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20569 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      let uu____20592 =
        let uu____20594 = FStar_Ident.nsstr lid  in uu____20594 = "Prims"  in
      if uu____20592
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20601 =
           let uu____20604 = FStar_Ident.string_of_lid lid  in
           FStar_All.pipe_right uu____20604
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20601
           (fun d_opt  ->
              let uu____20616 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20616
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20626 =
                   let uu____20629 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20629  in
                 match uu____20626 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20630 =
                       let uu____20632 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20632
                        in
                     failwith uu____20630
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20637 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20637
                       then
                         let uu____20640 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20642 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20644 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20640 uu____20642 uu____20644
                       else ());
                      (let uu____20650 = FStar_Ident.string_of_lid lid  in
                       FStar_Util.smap_add env1.fv_delta_depths uu____20650 d);
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20671),uu____20672) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20721 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20743),uu____20744) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20793 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20815 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20815
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20848 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____20848 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20870 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20879 =
                        let uu____20880 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20880.FStar_Syntax_Syntax.n  in
                      match uu____20879 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20885 -> false))
               in
            (true, uu____20870)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20908 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____20908
  
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
          let uu____20980 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____20980  in
        let uu____20981 = FStar_Util.smap_try_find tab s  in
        match uu____20981 with
        | FStar_Pervasives_Native.None  ->
            let uu____20984 = f ()  in
            (match uu____20984 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____21022 =
        let uu____21023 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21023 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____21057 =
        let uu____21058 = FStar_Syntax_Util.unrefine t  in
        uu____21058.FStar_Syntax_Syntax.n  in
      match uu____21057 with
      | FStar_Syntax_Syntax.Tm_type uu____21062 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____21066) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21092) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21097,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21119 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21152 =
        let attrs =
          let uu____21158 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21158  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21198 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21198)
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
      let uu____21243 = lookup_qname env1 ftv  in
      match uu____21243 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21247) ->
          let uu____21292 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21292 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21313,t),r) ->
               let uu____21328 =
                 let uu____21329 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21329 t  in
               FStar_Pervasives_Native.Some uu____21328)
      | uu____21330 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21342 = try_lookup_effect_lid env1 ftv  in
      match uu____21342 with
      | FStar_Pervasives_Native.None  ->
          let uu____21345 = name_not_found ftv  in
          let uu____21351 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21345 uu____21351
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
        let uu____21375 = lookup_qname env1 lid0  in
        match uu____21375 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21386);
                FStar_Syntax_Syntax.sigrng = uu____21387;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21389;
                FStar_Syntax_Syntax.sigattrs = uu____21390;
                FStar_Syntax_Syntax.sigopts = uu____21391;_},FStar_Pervasives_Native.None
              ),uu____21392)
            ->
            let lid1 =
              let uu____21448 =
                let uu____21449 = FStar_Ident.range_of_lid lid  in
                let uu____21450 =
                  let uu____21451 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21451  in
                FStar_Range.set_use_range uu____21449 uu____21450  in
              FStar_Ident.set_lid_range lid uu____21448  in
            let uu____21452 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21458  ->
                      match uu___6_21458 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21461 -> false))
               in
            if uu____21452
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21480 =
                      let uu____21482 =
                        let uu____21484 = get_range env1  in
                        FStar_Range.string_of_range uu____21484  in
                      let uu____21485 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21487 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21482 uu____21485 uu____21487
                       in
                    failwith uu____21480)
                  in
               match (binders, univs) with
               | ([],uu____21508) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21534,uu____21535::uu____21536::uu____21537) ->
                   let uu____21558 =
                     let uu____21560 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21562 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21560 uu____21562
                      in
                   failwith uu____21558
               | uu____21573 ->
                   let uu____21588 =
                     let uu____21593 =
                       let uu____21594 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21594)  in
                     inst_tscheme_with uu____21593 insts  in
                   (match uu____21588 with
                    | (uu____21607,t) ->
                        let t1 =
                          let uu____21610 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21610 t  in
                        let uu____21611 =
                          let uu____21612 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21612.FStar_Syntax_Syntax.n  in
                        (match uu____21611 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21647 -> failwith "Impossible")))
        | uu____21655 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21679 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21679 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21692,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21699 = find l2  in
            (match uu____21699 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21706 =
          let uu____21709 = FStar_Ident.string_of_lid l  in
          FStar_Util.smap_try_find env1.normalized_eff_names uu____21709  in
        match uu____21706 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21712 = find l  in
            (match uu____21712 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 ((let uu____21717 = FStar_Ident.string_of_lid l  in
                   FStar_Util.smap_add env1.normalized_eff_names uu____21717
                     m);
                  m))
         in
      let uu____21719 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21719
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21740 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____21740 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21746) ->
            FStar_List.length bs
        | uu____21785 ->
            let uu____21786 =
              let uu____21792 =
                let uu____21794 = FStar_Ident.string_of_lid name  in
                let uu____21796 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21794 uu____21796
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21792)
               in
            FStar_Errors.raise_error uu____21786 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____21815 = lookup_qname env1 l1  in
      match uu____21815 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21818;
              FStar_Syntax_Syntax.sigrng = uu____21819;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21821;
              FStar_Syntax_Syntax.sigattrs = uu____21822;
              FStar_Syntax_Syntax.sigopts = uu____21823;_},uu____21824),uu____21825)
          -> q
      | uu____21878 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____21902 =
          let uu____21903 =
            let uu____21905 = FStar_Util.string_of_int i  in
            let uu____21907 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21905 uu____21907
             in
          failwith uu____21903  in
        let uu____21910 = lookup_datacon env1 lid  in
        match uu____21910 with
        | (uu____21915,t) ->
            let uu____21917 =
              let uu____21918 = FStar_Syntax_Subst.compress t  in
              uu____21918.FStar_Syntax_Syntax.n  in
            (match uu____21917 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21922) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____21968 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____21982 = lookup_qname env1 l  in
      match uu____21982 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21984,uu____21985,uu____21986);
              FStar_Syntax_Syntax.sigrng = uu____21987;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21989;
              FStar_Syntax_Syntax.sigattrs = uu____21990;
              FStar_Syntax_Syntax.sigopts = uu____21991;_},uu____21992),uu____21993)
          ->
          FStar_Util.for_some
            (fun uu___7_22048  ->
               match uu___7_22048 with
               | FStar_Syntax_Syntax.Projector uu____22050 -> true
               | uu____22056 -> false) quals
      | uu____22058 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22072 = lookup_qname env1 lid  in
      match uu____22072 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22074,uu____22075,uu____22076,uu____22077,uu____22078,uu____22079);
              FStar_Syntax_Syntax.sigrng = uu____22080;
              FStar_Syntax_Syntax.sigquals = uu____22081;
              FStar_Syntax_Syntax.sigmeta = uu____22082;
              FStar_Syntax_Syntax.sigattrs = uu____22083;
              FStar_Syntax_Syntax.sigopts = uu____22084;_},uu____22085),uu____22086)
          -> true
      | uu____22146 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22160 = lookup_qname env1 lid  in
      match uu____22160 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22162,uu____22163,uu____22164,uu____22165,uu____22166,uu____22167);
              FStar_Syntax_Syntax.sigrng = uu____22168;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22170;
              FStar_Syntax_Syntax.sigattrs = uu____22171;
              FStar_Syntax_Syntax.sigopts = uu____22172;_},uu____22173),uu____22174)
          ->
          FStar_Util.for_some
            (fun uu___8_22237  ->
               match uu___8_22237 with
               | FStar_Syntax_Syntax.RecordType uu____22239 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22249 -> true
               | uu____22259 -> false) quals
      | uu____22261 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22271,uu____22272);
            FStar_Syntax_Syntax.sigrng = uu____22273;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22275;
            FStar_Syntax_Syntax.sigattrs = uu____22276;
            FStar_Syntax_Syntax.sigopts = uu____22277;_},uu____22278),uu____22279)
        ->
        FStar_Util.for_some
          (fun uu___9_22338  ->
             match uu___9_22338 with
             | FStar_Syntax_Syntax.Action uu____22340 -> true
             | uu____22342 -> false) quals
    | uu____22344 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22358 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22358
  
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
      let uu____22375 =
        let uu____22376 = FStar_Syntax_Util.un_uinst head  in
        uu____22376.FStar_Syntax_Syntax.n  in
      match uu____22375 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22382 ->
               true
           | uu____22385 -> false)
      | uu____22387 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22401 = lookup_qname env1 l  in
      match uu____22401 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22404),uu____22405) ->
          FStar_Util.for_some
            (fun uu___10_22453  ->
               match uu___10_22453 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22456 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22458 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22534 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22552) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22570 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22578 ->
                 FStar_Pervasives_Native.Some true
             | uu____22597 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22600 =
        let uu____22604 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22604 mapper  in
      match uu____22600 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22664 = lookup_qname env1 lid  in
      match uu____22664 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22668,uu____22669,tps,uu____22671,uu____22672,uu____22673);
              FStar_Syntax_Syntax.sigrng = uu____22674;
              FStar_Syntax_Syntax.sigquals = uu____22675;
              FStar_Syntax_Syntax.sigmeta = uu____22676;
              FStar_Syntax_Syntax.sigattrs = uu____22677;
              FStar_Syntax_Syntax.sigopts = uu____22678;_},uu____22679),uu____22680)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22748 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22794  ->
              match uu____22794 with
              | (d,uu____22803) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____22819 = effect_decl_opt env1 l  in
      match uu____22819 with
      | FStar_Pervasives_Native.None  ->
          let uu____22834 = name_not_found l  in
          let uu____22840 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22834 uu____22840
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22868 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____22868 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22875  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22889  ->
            fun uu____22890  -> fun e  -> FStar_Util.return_all e))
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
        let uu____22924 = FStar_Ident.lid_equals l1 l2  in
        if uu____22924
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____22943 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22943
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____22962 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23015  ->
                        match uu____23015 with
                        | (m1,m2,uu____23029,uu____23030,uu____23031) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22962 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23056,uu____23057,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23105 = join_opt env1 l1 l2  in
        match uu____23105 with
        | FStar_Pervasives_Native.None  ->
            let uu____23126 =
              let uu____23132 =
                let uu____23134 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23136 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23134 uu____23136
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23132)  in
            FStar_Errors.raise_error uu____23126 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23179 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23179
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
  'uuuuuu23199 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23199) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23228 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23254  ->
                match uu____23254 with
                | (d,uu____23261) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23228 with
      | FStar_Pervasives_Native.None  ->
          let uu____23272 =
            let uu____23274 = FStar_Ident.string_of_lid m  in
            FStar_Util.format1
              "Impossible: declaration for monad %s not found" uu____23274
             in
          failwith uu____23272
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23289 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23289 with
           | (uu____23300,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23318)::(wp,uu____23320)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23376 -> failwith "Impossible"))
  
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
        | uu____23441 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23454 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23454 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23471 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23471 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23496 =
                     let uu____23502 =
                       let uu____23504 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23512 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23523 =
                         let uu____23525 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23525  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23504 uu____23512 uu____23523
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23502)
                      in
                   FStar_Errors.raise_error uu____23496
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23533 =
                     let uu____23544 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23544 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23581  ->
                        fun uu____23582  ->
                          match (uu____23581, uu____23582) with
                          | ((x,uu____23612),(t,uu____23614)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23533
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23645 =
                     let uu___1608_23646 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1608_23646.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1608_23646.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1608_23646.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1608_23646.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23645
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23658 .
    'uuuuuu23658 ->
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
            let uu____23699 =
              let uu____23706 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____23706)  in
            match uu____23699 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23730 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23732 = FStar_Util.string_of_int given  in
                     let uu____23734 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23730 uu____23732 uu____23734
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23739 = effect_decl_opt env1 effect_name  in
          match uu____23739 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23761) ->
              let uu____23772 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23772 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23790 =
                       let uu____23793 = get_range env1  in
                       let uu____23794 =
                         let uu____23801 =
                           let uu____23802 =
                             let uu____23819 =
                               let uu____23830 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23830 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23819)  in
                           FStar_Syntax_Syntax.Tm_app uu____23802  in
                         FStar_Syntax_Syntax.mk uu____23801  in
                       uu____23794 FStar_Pervasives_Native.None uu____23793
                        in
                     FStar_Pervasives_Native.Some uu____23790)))
  
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
           (fun uu___11_23930  ->
              match uu___11_23930 with
              | FStar_Syntax_Syntax.Reflectable uu____23932 -> true
              | uu____23934 -> false))
  
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
      | uu____23994 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____24009 =
        let uu____24010 = FStar_Syntax_Subst.compress t  in
        uu____24010.FStar_Syntax_Syntax.n  in
      match uu____24009 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24014,c) ->
          is_reifiable_comp env1 c
      | uu____24036 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24056 =
           let uu____24058 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____24058  in
         if uu____24056
         then
           let uu____24061 =
             let uu____24067 =
               let uu____24069 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24069
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24067)  in
           let uu____24073 = get_range env1  in
           FStar_Errors.raise_error uu____24061 uu____24073
         else ());
        (let uu____24076 = effect_repr_aux true env1 c u_c  in
         match uu____24076 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1685_24112 = env1  in
        {
          solver = (uu___1685_24112.solver);
          range = (uu___1685_24112.range);
          curmodule = (uu___1685_24112.curmodule);
          gamma = (uu___1685_24112.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1685_24112.gamma_cache);
          modules = (uu___1685_24112.modules);
          expected_typ = (uu___1685_24112.expected_typ);
          sigtab = (uu___1685_24112.sigtab);
          attrtab = (uu___1685_24112.attrtab);
          instantiate_imp = (uu___1685_24112.instantiate_imp);
          effects = (uu___1685_24112.effects);
          generalize = (uu___1685_24112.generalize);
          letrecs = (uu___1685_24112.letrecs);
          top_level = (uu___1685_24112.top_level);
          check_uvars = (uu___1685_24112.check_uvars);
          use_eq = (uu___1685_24112.use_eq);
          use_eq_strict = (uu___1685_24112.use_eq_strict);
          is_iface = (uu___1685_24112.is_iface);
          admit = (uu___1685_24112.admit);
          lax = (uu___1685_24112.lax);
          lax_universes = (uu___1685_24112.lax_universes);
          phase1 = (uu___1685_24112.phase1);
          failhard = (uu___1685_24112.failhard);
          nosynth = (uu___1685_24112.nosynth);
          uvar_subtyping = (uu___1685_24112.uvar_subtyping);
          tc_term = (uu___1685_24112.tc_term);
          type_of = (uu___1685_24112.type_of);
          universe_of = (uu___1685_24112.universe_of);
          check_type_of = (uu___1685_24112.check_type_of);
          use_bv_sorts = (uu___1685_24112.use_bv_sorts);
          qtbl_name_and_index = (uu___1685_24112.qtbl_name_and_index);
          normalized_eff_names = (uu___1685_24112.normalized_eff_names);
          fv_delta_depths = (uu___1685_24112.fv_delta_depths);
          proof_ns = (uu___1685_24112.proof_ns);
          synth_hook = (uu___1685_24112.synth_hook);
          try_solve_implicits_hook =
            (uu___1685_24112.try_solve_implicits_hook);
          splice = (uu___1685_24112.splice);
          mpreprocess = (uu___1685_24112.mpreprocess);
          postprocess = (uu___1685_24112.postprocess);
          identifier_info = (uu___1685_24112.identifier_info);
          tc_hooks = (uu___1685_24112.tc_hooks);
          dsenv = (uu___1685_24112.dsenv);
          nbe = (uu___1685_24112.nbe);
          strict_args_tab = (uu___1685_24112.strict_args_tab);
          erasable_types_tab = (uu___1685_24112.erasable_types_tab)
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
    fun uu____24131  ->
      match uu____24131 with
      | (ed,quals) ->
          let effects1 =
            let uu___1694_24145 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1694_24145.order);
              joins = (uu___1694_24145.joins);
              polymonadic_binds = (uu___1694_24145.polymonadic_binds)
            }  in
          let uu___1697_24154 = env1  in
          {
            solver = (uu___1697_24154.solver);
            range = (uu___1697_24154.range);
            curmodule = (uu___1697_24154.curmodule);
            gamma = (uu___1697_24154.gamma);
            gamma_sig = (uu___1697_24154.gamma_sig);
            gamma_cache = (uu___1697_24154.gamma_cache);
            modules = (uu___1697_24154.modules);
            expected_typ = (uu___1697_24154.expected_typ);
            sigtab = (uu___1697_24154.sigtab);
            attrtab = (uu___1697_24154.attrtab);
            instantiate_imp = (uu___1697_24154.instantiate_imp);
            effects = effects1;
            generalize = (uu___1697_24154.generalize);
            letrecs = (uu___1697_24154.letrecs);
            top_level = (uu___1697_24154.top_level);
            check_uvars = (uu___1697_24154.check_uvars);
            use_eq = (uu___1697_24154.use_eq);
            use_eq_strict = (uu___1697_24154.use_eq_strict);
            is_iface = (uu___1697_24154.is_iface);
            admit = (uu___1697_24154.admit);
            lax = (uu___1697_24154.lax);
            lax_universes = (uu___1697_24154.lax_universes);
            phase1 = (uu___1697_24154.phase1);
            failhard = (uu___1697_24154.failhard);
            nosynth = (uu___1697_24154.nosynth);
            uvar_subtyping = (uu___1697_24154.uvar_subtyping);
            tc_term = (uu___1697_24154.tc_term);
            type_of = (uu___1697_24154.type_of);
            universe_of = (uu___1697_24154.universe_of);
            check_type_of = (uu___1697_24154.check_type_of);
            use_bv_sorts = (uu___1697_24154.use_bv_sorts);
            qtbl_name_and_index = (uu___1697_24154.qtbl_name_and_index);
            normalized_eff_names = (uu___1697_24154.normalized_eff_names);
            fv_delta_depths = (uu___1697_24154.fv_delta_depths);
            proof_ns = (uu___1697_24154.proof_ns);
            synth_hook = (uu___1697_24154.synth_hook);
            try_solve_implicits_hook =
              (uu___1697_24154.try_solve_implicits_hook);
            splice = (uu___1697_24154.splice);
            mpreprocess = (uu___1697_24154.mpreprocess);
            postprocess = (uu___1697_24154.postprocess);
            identifier_info = (uu___1697_24154.identifier_info);
            tc_hooks = (uu___1697_24154.tc_hooks);
            dsenv = (uu___1697_24154.dsenv);
            nbe = (uu___1697_24154.nbe);
            strict_args_tab = (uu___1697_24154.strict_args_tab);
            erasable_types_tab = (uu___1697_24154.erasable_types_tab)
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
        let uu____24183 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24251  ->
                  match uu____24251 with
                  | (m1,n1,uu____24269,uu____24270) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24183 with
        | FStar_Pervasives_Native.Some (uu____24295,uu____24296,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24341 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24416 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24416
                  (fun uu____24437  ->
                     match uu____24437 with
                     | (c1,g1) ->
                         let uu____24448 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24448
                           (fun uu____24469  ->
                              match uu____24469 with
                              | (c2,g2) ->
                                  let uu____24480 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24480)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24602 = l1 u t e  in
                              l2 u t uu____24602))
                | uu____24603 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24671  ->
                    match uu____24671 with
                    | (e,uu____24679) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24702 =
            match uu____24702 with
            | (i,j) ->
                let uu____24713 = FStar_Ident.lid_equals i j  in
                if uu____24713
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____24720  ->
                       FStar_Pervasives_Native.Some uu____24720)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24749 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24759 = FStar_Ident.lid_equals i k  in
                        if uu____24759
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24773 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24773
                                  then []
                                  else
                                    (let uu____24780 =
                                       let uu____24789 =
                                         find_edge order1 (i, k)  in
                                       let uu____24792 =
                                         find_edge order1 (k, j)  in
                                       (uu____24789, uu____24792)  in
                                     match uu____24780 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24807 =
                                           compose_edges e1 e2  in
                                         [uu____24807]
                                     | uu____24808 -> [])))))
                 in
              FStar_List.append order1 uu____24749  in
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
                  let uu____24838 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24841 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____24841
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24838
                  then
                    let uu____24848 =
                      let uu____24854 =
                        let uu____24856 =
                          FStar_Ident.string_of_lid edge2.mtarget  in
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          uu____24856
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24854)
                       in
                    let uu____24860 = get_range env1  in
                    FStar_Errors.raise_error uu____24848 uu____24860
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____24938 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24938
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24990 =
                                             let uu____24999 =
                                               find_edge order2 (i, k)  in
                                             let uu____25002 =
                                               find_edge order2 (j, k)  in
                                             (uu____24999, uu____25002)  in
                                           match uu____24990 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25044,uu____25045)
                                                    ->
                                                    let uu____25052 =
                                                      let uu____25059 =
                                                        let uu____25061 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25061
                                                         in
                                                      let uu____25064 =
                                                        let uu____25066 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25066
                                                         in
                                                      (uu____25059,
                                                        uu____25064)
                                                       in
                                                    (match uu____25052 with
                                                     | (true ,true ) ->
                                                         let uu____25083 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25083
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
                                           | uu____25126 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25178 =
                                   let uu____25180 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25180
                                     FStar_Util.is_some
                                    in
                                 if uu____25178
                                 then
                                   let uu____25229 =
                                     let uu____25235 =
                                       let uu____25237 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25239 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25241 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25243 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25237 uu____25239 uu____25241
                                         uu____25243
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25235)
                                      in
                                   FStar_Errors.raise_error uu____25229
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1818_25282 = env1.effects  in
             {
               decls = (uu___1818_25282.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1818_25282.polymonadic_binds)
             }  in
           let uu___1821_25283 = env1  in
           {
             solver = (uu___1821_25283.solver);
             range = (uu___1821_25283.range);
             curmodule = (uu___1821_25283.curmodule);
             gamma = (uu___1821_25283.gamma);
             gamma_sig = (uu___1821_25283.gamma_sig);
             gamma_cache = (uu___1821_25283.gamma_cache);
             modules = (uu___1821_25283.modules);
             expected_typ = (uu___1821_25283.expected_typ);
             sigtab = (uu___1821_25283.sigtab);
             attrtab = (uu___1821_25283.attrtab);
             instantiate_imp = (uu___1821_25283.instantiate_imp);
             effects = effects1;
             generalize = (uu___1821_25283.generalize);
             letrecs = (uu___1821_25283.letrecs);
             top_level = (uu___1821_25283.top_level);
             check_uvars = (uu___1821_25283.check_uvars);
             use_eq = (uu___1821_25283.use_eq);
             use_eq_strict = (uu___1821_25283.use_eq_strict);
             is_iface = (uu___1821_25283.is_iface);
             admit = (uu___1821_25283.admit);
             lax = (uu___1821_25283.lax);
             lax_universes = (uu___1821_25283.lax_universes);
             phase1 = (uu___1821_25283.phase1);
             failhard = (uu___1821_25283.failhard);
             nosynth = (uu___1821_25283.nosynth);
             uvar_subtyping = (uu___1821_25283.uvar_subtyping);
             tc_term = (uu___1821_25283.tc_term);
             type_of = (uu___1821_25283.type_of);
             universe_of = (uu___1821_25283.universe_of);
             check_type_of = (uu___1821_25283.check_type_of);
             use_bv_sorts = (uu___1821_25283.use_bv_sorts);
             qtbl_name_and_index = (uu___1821_25283.qtbl_name_and_index);
             normalized_eff_names = (uu___1821_25283.normalized_eff_names);
             fv_delta_depths = (uu___1821_25283.fv_delta_depths);
             proof_ns = (uu___1821_25283.proof_ns);
             synth_hook = (uu___1821_25283.synth_hook);
             try_solve_implicits_hook =
               (uu___1821_25283.try_solve_implicits_hook);
             splice = (uu___1821_25283.splice);
             mpreprocess = (uu___1821_25283.mpreprocess);
             postprocess = (uu___1821_25283.postprocess);
             identifier_info = (uu___1821_25283.identifier_info);
             tc_hooks = (uu___1821_25283.tc_hooks);
             dsenv = (uu___1821_25283.dsenv);
             nbe = (uu___1821_25283.nbe);
             strict_args_tab = (uu___1821_25283.strict_args_tab);
             erasable_types_tab = (uu___1821_25283.erasable_types_tab)
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
              let uu____25331 = FStar_Ident.string_of_lid m  in
              let uu____25333 = FStar_Ident.string_of_lid n  in
              let uu____25335 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25331 uu____25333 uu____25335
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25344 =
              let uu____25346 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25346 FStar_Util.is_some  in
            if uu____25344
            then
              let uu____25383 =
                let uu____25389 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25389)
                 in
              FStar_Errors.raise_error uu____25383 env1.range
            else
              (let uu____25395 =
                 let uu____25397 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25397 FStar_Util.is_some  in
               if uu____25395
               then
                 let uu____25422 =
                   let uu____25428 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25428)
                    in
                 FStar_Errors.raise_error uu____25422 env1.range
               else
                 (let uu___1836_25434 = env1  in
                  {
                    solver = (uu___1836_25434.solver);
                    range = (uu___1836_25434.range);
                    curmodule = (uu___1836_25434.curmodule);
                    gamma = (uu___1836_25434.gamma);
                    gamma_sig = (uu___1836_25434.gamma_sig);
                    gamma_cache = (uu___1836_25434.gamma_cache);
                    modules = (uu___1836_25434.modules);
                    expected_typ = (uu___1836_25434.expected_typ);
                    sigtab = (uu___1836_25434.sigtab);
                    attrtab = (uu___1836_25434.attrtab);
                    instantiate_imp = (uu___1836_25434.instantiate_imp);
                    effects =
                      (let uu___1838_25436 = env1.effects  in
                       {
                         decls = (uu___1838_25436.decls);
                         order = (uu___1838_25436.order);
                         joins = (uu___1838_25436.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1836_25434.generalize);
                    letrecs = (uu___1836_25434.letrecs);
                    top_level = (uu___1836_25434.top_level);
                    check_uvars = (uu___1836_25434.check_uvars);
                    use_eq = (uu___1836_25434.use_eq);
                    use_eq_strict = (uu___1836_25434.use_eq_strict);
                    is_iface = (uu___1836_25434.is_iface);
                    admit = (uu___1836_25434.admit);
                    lax = (uu___1836_25434.lax);
                    lax_universes = (uu___1836_25434.lax_universes);
                    phase1 = (uu___1836_25434.phase1);
                    failhard = (uu___1836_25434.failhard);
                    nosynth = (uu___1836_25434.nosynth);
                    uvar_subtyping = (uu___1836_25434.uvar_subtyping);
                    tc_term = (uu___1836_25434.tc_term);
                    type_of = (uu___1836_25434.type_of);
                    universe_of = (uu___1836_25434.universe_of);
                    check_type_of = (uu___1836_25434.check_type_of);
                    use_bv_sorts = (uu___1836_25434.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1836_25434.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1836_25434.normalized_eff_names);
                    fv_delta_depths = (uu___1836_25434.fv_delta_depths);
                    proof_ns = (uu___1836_25434.proof_ns);
                    synth_hook = (uu___1836_25434.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1836_25434.try_solve_implicits_hook);
                    splice = (uu___1836_25434.splice);
                    mpreprocess = (uu___1836_25434.mpreprocess);
                    postprocess = (uu___1836_25434.postprocess);
                    identifier_info = (uu___1836_25434.identifier_info);
                    tc_hooks = (uu___1836_25434.tc_hooks);
                    dsenv = (uu___1836_25434.dsenv);
                    nbe = (uu___1836_25434.nbe);
                    strict_args_tab = (uu___1836_25434.strict_args_tab);
                    erasable_types_tab = (uu___1836_25434.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1842_25508 = env1  in
      {
        solver = (uu___1842_25508.solver);
        range = (uu___1842_25508.range);
        curmodule = (uu___1842_25508.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1842_25508.gamma_sig);
        gamma_cache = (uu___1842_25508.gamma_cache);
        modules = (uu___1842_25508.modules);
        expected_typ = (uu___1842_25508.expected_typ);
        sigtab = (uu___1842_25508.sigtab);
        attrtab = (uu___1842_25508.attrtab);
        instantiate_imp = (uu___1842_25508.instantiate_imp);
        effects = (uu___1842_25508.effects);
        generalize = (uu___1842_25508.generalize);
        letrecs = (uu___1842_25508.letrecs);
        top_level = (uu___1842_25508.top_level);
        check_uvars = (uu___1842_25508.check_uvars);
        use_eq = (uu___1842_25508.use_eq);
        use_eq_strict = (uu___1842_25508.use_eq_strict);
        is_iface = (uu___1842_25508.is_iface);
        admit = (uu___1842_25508.admit);
        lax = (uu___1842_25508.lax);
        lax_universes = (uu___1842_25508.lax_universes);
        phase1 = (uu___1842_25508.phase1);
        failhard = (uu___1842_25508.failhard);
        nosynth = (uu___1842_25508.nosynth);
        uvar_subtyping = (uu___1842_25508.uvar_subtyping);
        tc_term = (uu___1842_25508.tc_term);
        type_of = (uu___1842_25508.type_of);
        universe_of = (uu___1842_25508.universe_of);
        check_type_of = (uu___1842_25508.check_type_of);
        use_bv_sorts = (uu___1842_25508.use_bv_sorts);
        qtbl_name_and_index = (uu___1842_25508.qtbl_name_and_index);
        normalized_eff_names = (uu___1842_25508.normalized_eff_names);
        fv_delta_depths = (uu___1842_25508.fv_delta_depths);
        proof_ns = (uu___1842_25508.proof_ns);
        synth_hook = (uu___1842_25508.synth_hook);
        try_solve_implicits_hook = (uu___1842_25508.try_solve_implicits_hook);
        splice = (uu___1842_25508.splice);
        mpreprocess = (uu___1842_25508.mpreprocess);
        postprocess = (uu___1842_25508.postprocess);
        identifier_info = (uu___1842_25508.identifier_info);
        tc_hooks = (uu___1842_25508.tc_hooks);
        dsenv = (uu___1842_25508.dsenv);
        nbe = (uu___1842_25508.nbe);
        strict_args_tab = (uu___1842_25508.strict_args_tab);
        erasable_types_tab = (uu___1842_25508.erasable_types_tab)
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
            (let uu___1855_25566 = env1  in
             {
               solver = (uu___1855_25566.solver);
               range = (uu___1855_25566.range);
               curmodule = (uu___1855_25566.curmodule);
               gamma = rest;
               gamma_sig = (uu___1855_25566.gamma_sig);
               gamma_cache = (uu___1855_25566.gamma_cache);
               modules = (uu___1855_25566.modules);
               expected_typ = (uu___1855_25566.expected_typ);
               sigtab = (uu___1855_25566.sigtab);
               attrtab = (uu___1855_25566.attrtab);
               instantiate_imp = (uu___1855_25566.instantiate_imp);
               effects = (uu___1855_25566.effects);
               generalize = (uu___1855_25566.generalize);
               letrecs = (uu___1855_25566.letrecs);
               top_level = (uu___1855_25566.top_level);
               check_uvars = (uu___1855_25566.check_uvars);
               use_eq = (uu___1855_25566.use_eq);
               use_eq_strict = (uu___1855_25566.use_eq_strict);
               is_iface = (uu___1855_25566.is_iface);
               admit = (uu___1855_25566.admit);
               lax = (uu___1855_25566.lax);
               lax_universes = (uu___1855_25566.lax_universes);
               phase1 = (uu___1855_25566.phase1);
               failhard = (uu___1855_25566.failhard);
               nosynth = (uu___1855_25566.nosynth);
               uvar_subtyping = (uu___1855_25566.uvar_subtyping);
               tc_term = (uu___1855_25566.tc_term);
               type_of = (uu___1855_25566.type_of);
               universe_of = (uu___1855_25566.universe_of);
               check_type_of = (uu___1855_25566.check_type_of);
               use_bv_sorts = (uu___1855_25566.use_bv_sorts);
               qtbl_name_and_index = (uu___1855_25566.qtbl_name_and_index);
               normalized_eff_names = (uu___1855_25566.normalized_eff_names);
               fv_delta_depths = (uu___1855_25566.fv_delta_depths);
               proof_ns = (uu___1855_25566.proof_ns);
               synth_hook = (uu___1855_25566.synth_hook);
               try_solve_implicits_hook =
                 (uu___1855_25566.try_solve_implicits_hook);
               splice = (uu___1855_25566.splice);
               mpreprocess = (uu___1855_25566.mpreprocess);
               postprocess = (uu___1855_25566.postprocess);
               identifier_info = (uu___1855_25566.identifier_info);
               tc_hooks = (uu___1855_25566.tc_hooks);
               dsenv = (uu___1855_25566.dsenv);
               nbe = (uu___1855_25566.nbe);
               strict_args_tab = (uu___1855_25566.strict_args_tab);
               erasable_types_tab = (uu___1855_25566.erasable_types_tab)
             }))
    | uu____25567 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25596  ->
             match uu____25596 with | (x,uu____25604) -> push_bv env2 x) env1
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
            let uu___1869_25639 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1869_25639.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1869_25639.FStar_Syntax_Syntax.index);
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
        let uu____25712 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25712 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____25740 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25740)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1890_25756 = env1  in
      {
        solver = (uu___1890_25756.solver);
        range = (uu___1890_25756.range);
        curmodule = (uu___1890_25756.curmodule);
        gamma = (uu___1890_25756.gamma);
        gamma_sig = (uu___1890_25756.gamma_sig);
        gamma_cache = (uu___1890_25756.gamma_cache);
        modules = (uu___1890_25756.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1890_25756.sigtab);
        attrtab = (uu___1890_25756.attrtab);
        instantiate_imp = (uu___1890_25756.instantiate_imp);
        effects = (uu___1890_25756.effects);
        generalize = (uu___1890_25756.generalize);
        letrecs = (uu___1890_25756.letrecs);
        top_level = (uu___1890_25756.top_level);
        check_uvars = (uu___1890_25756.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1890_25756.use_eq_strict);
        is_iface = (uu___1890_25756.is_iface);
        admit = (uu___1890_25756.admit);
        lax = (uu___1890_25756.lax);
        lax_universes = (uu___1890_25756.lax_universes);
        phase1 = (uu___1890_25756.phase1);
        failhard = (uu___1890_25756.failhard);
        nosynth = (uu___1890_25756.nosynth);
        uvar_subtyping = (uu___1890_25756.uvar_subtyping);
        tc_term = (uu___1890_25756.tc_term);
        type_of = (uu___1890_25756.type_of);
        universe_of = (uu___1890_25756.universe_of);
        check_type_of = (uu___1890_25756.check_type_of);
        use_bv_sorts = (uu___1890_25756.use_bv_sorts);
        qtbl_name_and_index = (uu___1890_25756.qtbl_name_and_index);
        normalized_eff_names = (uu___1890_25756.normalized_eff_names);
        fv_delta_depths = (uu___1890_25756.fv_delta_depths);
        proof_ns = (uu___1890_25756.proof_ns);
        synth_hook = (uu___1890_25756.synth_hook);
        try_solve_implicits_hook = (uu___1890_25756.try_solve_implicits_hook);
        splice = (uu___1890_25756.splice);
        mpreprocess = (uu___1890_25756.mpreprocess);
        postprocess = (uu___1890_25756.postprocess);
        identifier_info = (uu___1890_25756.identifier_info);
        tc_hooks = (uu___1890_25756.tc_hooks);
        dsenv = (uu___1890_25756.dsenv);
        nbe = (uu___1890_25756.nbe);
        strict_args_tab = (uu___1890_25756.strict_args_tab);
        erasable_types_tab = (uu___1890_25756.erasable_types_tab)
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
    let uu____25787 = expected_typ env_  in
    ((let uu___1897_25793 = env_  in
      {
        solver = (uu___1897_25793.solver);
        range = (uu___1897_25793.range);
        curmodule = (uu___1897_25793.curmodule);
        gamma = (uu___1897_25793.gamma);
        gamma_sig = (uu___1897_25793.gamma_sig);
        gamma_cache = (uu___1897_25793.gamma_cache);
        modules = (uu___1897_25793.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1897_25793.sigtab);
        attrtab = (uu___1897_25793.attrtab);
        instantiate_imp = (uu___1897_25793.instantiate_imp);
        effects = (uu___1897_25793.effects);
        generalize = (uu___1897_25793.generalize);
        letrecs = (uu___1897_25793.letrecs);
        top_level = (uu___1897_25793.top_level);
        check_uvars = (uu___1897_25793.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1897_25793.use_eq_strict);
        is_iface = (uu___1897_25793.is_iface);
        admit = (uu___1897_25793.admit);
        lax = (uu___1897_25793.lax);
        lax_universes = (uu___1897_25793.lax_universes);
        phase1 = (uu___1897_25793.phase1);
        failhard = (uu___1897_25793.failhard);
        nosynth = (uu___1897_25793.nosynth);
        uvar_subtyping = (uu___1897_25793.uvar_subtyping);
        tc_term = (uu___1897_25793.tc_term);
        type_of = (uu___1897_25793.type_of);
        universe_of = (uu___1897_25793.universe_of);
        check_type_of = (uu___1897_25793.check_type_of);
        use_bv_sorts = (uu___1897_25793.use_bv_sorts);
        qtbl_name_and_index = (uu___1897_25793.qtbl_name_and_index);
        normalized_eff_names = (uu___1897_25793.normalized_eff_names);
        fv_delta_depths = (uu___1897_25793.fv_delta_depths);
        proof_ns = (uu___1897_25793.proof_ns);
        synth_hook = (uu___1897_25793.synth_hook);
        try_solve_implicits_hook = (uu___1897_25793.try_solve_implicits_hook);
        splice = (uu___1897_25793.splice);
        mpreprocess = (uu___1897_25793.mpreprocess);
        postprocess = (uu___1897_25793.postprocess);
        identifier_info = (uu___1897_25793.identifier_info);
        tc_hooks = (uu___1897_25793.tc_hooks);
        dsenv = (uu___1897_25793.dsenv);
        nbe = (uu___1897_25793.nbe);
        strict_args_tab = (uu___1897_25793.strict_args_tab);
        erasable_types_tab = (uu___1897_25793.erasable_types_tab)
      }), uu____25787)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25805 =
      let uu____25806 = FStar_Ident.id_of_text ""  in [uu____25806]  in
    FStar_Ident.lid_of_ids uu____25805  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____25813 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25813
        then
          let uu____25818 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25818 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1905_25846 = env1  in
       {
         solver = (uu___1905_25846.solver);
         range = (uu___1905_25846.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1905_25846.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1905_25846.expected_typ);
         sigtab = (uu___1905_25846.sigtab);
         attrtab = (uu___1905_25846.attrtab);
         instantiate_imp = (uu___1905_25846.instantiate_imp);
         effects = (uu___1905_25846.effects);
         generalize = (uu___1905_25846.generalize);
         letrecs = (uu___1905_25846.letrecs);
         top_level = (uu___1905_25846.top_level);
         check_uvars = (uu___1905_25846.check_uvars);
         use_eq = (uu___1905_25846.use_eq);
         use_eq_strict = (uu___1905_25846.use_eq_strict);
         is_iface = (uu___1905_25846.is_iface);
         admit = (uu___1905_25846.admit);
         lax = (uu___1905_25846.lax);
         lax_universes = (uu___1905_25846.lax_universes);
         phase1 = (uu___1905_25846.phase1);
         failhard = (uu___1905_25846.failhard);
         nosynth = (uu___1905_25846.nosynth);
         uvar_subtyping = (uu___1905_25846.uvar_subtyping);
         tc_term = (uu___1905_25846.tc_term);
         type_of = (uu___1905_25846.type_of);
         universe_of = (uu___1905_25846.universe_of);
         check_type_of = (uu___1905_25846.check_type_of);
         use_bv_sorts = (uu___1905_25846.use_bv_sorts);
         qtbl_name_and_index = (uu___1905_25846.qtbl_name_and_index);
         normalized_eff_names = (uu___1905_25846.normalized_eff_names);
         fv_delta_depths = (uu___1905_25846.fv_delta_depths);
         proof_ns = (uu___1905_25846.proof_ns);
         synth_hook = (uu___1905_25846.synth_hook);
         try_solve_implicits_hook =
           (uu___1905_25846.try_solve_implicits_hook);
         splice = (uu___1905_25846.splice);
         mpreprocess = (uu___1905_25846.mpreprocess);
         postprocess = (uu___1905_25846.postprocess);
         identifier_info = (uu___1905_25846.identifier_info);
         tc_hooks = (uu___1905_25846.tc_hooks);
         dsenv = (uu___1905_25846.dsenv);
         nbe = (uu___1905_25846.nbe);
         strict_args_tab = (uu___1905_25846.strict_args_tab);
         erasable_types_tab = (uu___1905_25846.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25898)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____25902,(uu____25903,t)))::tl
          ->
          let uu____25924 =
            let uu____25927 = FStar_Syntax_Free.uvars t  in
            ext out uu____25927  in
          aux uu____25924 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25930;
            FStar_Syntax_Syntax.index = uu____25931;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____25939 =
            let uu____25942 = FStar_Syntax_Free.uvars t  in
            ext out uu____25942  in
          aux uu____25939 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26000)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26004,(uu____26005,t)))::tl
          ->
          let uu____26026 =
            let uu____26029 = FStar_Syntax_Free.univs t  in
            ext out uu____26029  in
          aux uu____26026 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26032;
            FStar_Syntax_Syntax.index = uu____26033;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26041 =
            let uu____26044 = FStar_Syntax_Free.univs t  in
            ext out uu____26044  in
          aux uu____26041 tl
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
          let uu____26106 = FStar_Util.set_add uname out  in
          aux uu____26106 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26109,(uu____26110,t)))::tl
          ->
          let uu____26131 =
            let uu____26134 = FStar_Syntax_Free.univnames t  in
            ext out uu____26134  in
          aux uu____26131 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26137;
            FStar_Syntax_Syntax.index = uu____26138;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26146 =
            let uu____26149 = FStar_Syntax_Free.univnames t  in
            ext out uu____26149  in
          aux uu____26146 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26170  ->
            match uu___12_26170 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26174 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26187 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26198 =
      let uu____26207 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26207
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26198 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26255 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26268  ->
              match uu___13_26268 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26271 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26271
              | FStar_Syntax_Syntax.Binding_univ u ->
                  let uu____26275 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat "Binding_univ " uu____26275
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26279) ->
                  let uu____26296 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26296))
       in
    FStar_All.pipe_right uu____26255 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26310  ->
    match uu___14_26310 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26316 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26316
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26339  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26394) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26427,uu____26428) -> false  in
      let uu____26442 =
        FStar_List.tryFind
          (fun uu____26464  ->
             match uu____26464 with | (p,uu____26475) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26442 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26494,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26524 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26524
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2048_26546 = e  in
        {
          solver = (uu___2048_26546.solver);
          range = (uu___2048_26546.range);
          curmodule = (uu___2048_26546.curmodule);
          gamma = (uu___2048_26546.gamma);
          gamma_sig = (uu___2048_26546.gamma_sig);
          gamma_cache = (uu___2048_26546.gamma_cache);
          modules = (uu___2048_26546.modules);
          expected_typ = (uu___2048_26546.expected_typ);
          sigtab = (uu___2048_26546.sigtab);
          attrtab = (uu___2048_26546.attrtab);
          instantiate_imp = (uu___2048_26546.instantiate_imp);
          effects = (uu___2048_26546.effects);
          generalize = (uu___2048_26546.generalize);
          letrecs = (uu___2048_26546.letrecs);
          top_level = (uu___2048_26546.top_level);
          check_uvars = (uu___2048_26546.check_uvars);
          use_eq = (uu___2048_26546.use_eq);
          use_eq_strict = (uu___2048_26546.use_eq_strict);
          is_iface = (uu___2048_26546.is_iface);
          admit = (uu___2048_26546.admit);
          lax = (uu___2048_26546.lax);
          lax_universes = (uu___2048_26546.lax_universes);
          phase1 = (uu___2048_26546.phase1);
          failhard = (uu___2048_26546.failhard);
          nosynth = (uu___2048_26546.nosynth);
          uvar_subtyping = (uu___2048_26546.uvar_subtyping);
          tc_term = (uu___2048_26546.tc_term);
          type_of = (uu___2048_26546.type_of);
          universe_of = (uu___2048_26546.universe_of);
          check_type_of = (uu___2048_26546.check_type_of);
          use_bv_sorts = (uu___2048_26546.use_bv_sorts);
          qtbl_name_and_index = (uu___2048_26546.qtbl_name_and_index);
          normalized_eff_names = (uu___2048_26546.normalized_eff_names);
          fv_delta_depths = (uu___2048_26546.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2048_26546.synth_hook);
          try_solve_implicits_hook =
            (uu___2048_26546.try_solve_implicits_hook);
          splice = (uu___2048_26546.splice);
          mpreprocess = (uu___2048_26546.mpreprocess);
          postprocess = (uu___2048_26546.postprocess);
          identifier_info = (uu___2048_26546.identifier_info);
          tc_hooks = (uu___2048_26546.tc_hooks);
          dsenv = (uu___2048_26546.dsenv);
          nbe = (uu___2048_26546.nbe);
          strict_args_tab = (uu___2048_26546.strict_args_tab);
          erasable_types_tab = (uu___2048_26546.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2057_26594 = e  in
      {
        solver = (uu___2057_26594.solver);
        range = (uu___2057_26594.range);
        curmodule = (uu___2057_26594.curmodule);
        gamma = (uu___2057_26594.gamma);
        gamma_sig = (uu___2057_26594.gamma_sig);
        gamma_cache = (uu___2057_26594.gamma_cache);
        modules = (uu___2057_26594.modules);
        expected_typ = (uu___2057_26594.expected_typ);
        sigtab = (uu___2057_26594.sigtab);
        attrtab = (uu___2057_26594.attrtab);
        instantiate_imp = (uu___2057_26594.instantiate_imp);
        effects = (uu___2057_26594.effects);
        generalize = (uu___2057_26594.generalize);
        letrecs = (uu___2057_26594.letrecs);
        top_level = (uu___2057_26594.top_level);
        check_uvars = (uu___2057_26594.check_uvars);
        use_eq = (uu___2057_26594.use_eq);
        use_eq_strict = (uu___2057_26594.use_eq_strict);
        is_iface = (uu___2057_26594.is_iface);
        admit = (uu___2057_26594.admit);
        lax = (uu___2057_26594.lax);
        lax_universes = (uu___2057_26594.lax_universes);
        phase1 = (uu___2057_26594.phase1);
        failhard = (uu___2057_26594.failhard);
        nosynth = (uu___2057_26594.nosynth);
        uvar_subtyping = (uu___2057_26594.uvar_subtyping);
        tc_term = (uu___2057_26594.tc_term);
        type_of = (uu___2057_26594.type_of);
        universe_of = (uu___2057_26594.universe_of);
        check_type_of = (uu___2057_26594.check_type_of);
        use_bv_sorts = (uu___2057_26594.use_bv_sorts);
        qtbl_name_and_index = (uu___2057_26594.qtbl_name_and_index);
        normalized_eff_names = (uu___2057_26594.normalized_eff_names);
        fv_delta_depths = (uu___2057_26594.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2057_26594.synth_hook);
        try_solve_implicits_hook = (uu___2057_26594.try_solve_implicits_hook);
        splice = (uu___2057_26594.splice);
        mpreprocess = (uu___2057_26594.mpreprocess);
        postprocess = (uu___2057_26594.postprocess);
        identifier_info = (uu___2057_26594.identifier_info);
        tc_hooks = (uu___2057_26594.tc_hooks);
        dsenv = (uu___2057_26594.dsenv);
        nbe = (uu___2057_26594.nbe);
        strict_args_tab = (uu___2057_26594.strict_args_tab);
        erasable_types_tab = (uu___2057_26594.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26610 = FStar_Syntax_Free.names t  in
      let uu____26613 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26610 uu____26613
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26636 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26636
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26646 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26646
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____26667 =
      match uu____26667 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26687 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26687)
       in
    let uu____26695 =
      let uu____26699 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____26699 FStar_List.rev  in
    FStar_All.pipe_right uu____26695 (FStar_String.concat " ")
  
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
                  (let uu____26767 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26767 with
                   | FStar_Pervasives_Native.Some uu____26771 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26774 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26784;
        FStar_TypeChecker_Common.univ_ineqs = uu____26785;
        FStar_TypeChecker_Common.implicits = uu____26786;_} -> true
    | uu____26796 -> false
  
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
          let uu___2101_26818 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2101_26818.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2101_26818.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2101_26818.FStar_TypeChecker_Common.implicits)
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
          let uu____26857 = FStar_Options.defensive ()  in
          if uu____26857
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26863 =
              let uu____26865 =
                let uu____26867 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26867  in
              Prims.op_Negation uu____26865  in
            (if uu____26863
             then
               let uu____26874 =
                 let uu____26880 =
                   let uu____26882 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26884 =
                     let uu____26886 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26886
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26882 uu____26884
                    in
                 (FStar_Errors.Warning_Defensive, uu____26880)  in
               FStar_Errors.log_issue rng uu____26874
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
          let uu____26926 =
            let uu____26928 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26928  in
          if uu____26926
          then ()
          else
            (let uu____26933 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26933 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26959 =
            let uu____26961 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26961  in
          if uu____26959
          then ()
          else
            (let uu____26966 = bound_vars e  in
             def_check_closed_in rng msg uu____26966 t)
  
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
          let uu___2138_27005 = g  in
          let uu____27006 =
            let uu____27007 =
              let uu____27008 =
                let uu____27015 =
                  let uu____27016 =
                    let uu____27033 =
                      let uu____27044 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27044]  in
                    (f, uu____27033)  in
                  FStar_Syntax_Syntax.Tm_app uu____27016  in
                FStar_Syntax_Syntax.mk uu____27015  in
              uu____27008 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____27081  ->
                 FStar_TypeChecker_Common.NonTrivial uu____27081) uu____27007
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27006;
            FStar_TypeChecker_Common.deferred =
              (uu___2138_27005.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2138_27005.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2138_27005.FStar_TypeChecker_Common.implicits)
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
          let uu___2145_27099 = g  in
          let uu____27100 =
            let uu____27101 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27101  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27100;
            FStar_TypeChecker_Common.deferred =
              (uu___2145_27099.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2145_27099.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2145_27099.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2150_27118 = g  in
          let uu____27119 =
            let uu____27120 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27120  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27119;
            FStar_TypeChecker_Common.deferred =
              (uu___2150_27118.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2150_27118.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2150_27118.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2154_27122 = g  in
          let uu____27123 =
            let uu____27124 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27124  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27123;
            FStar_TypeChecker_Common.deferred =
              (uu___2154_27122.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2154_27122.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2154_27122.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27131 ->
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
                       let uu____27208 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27208
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2177_27215 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2177_27215.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2177_27215.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2177_27215.FStar_TypeChecker_Common.implicits)
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
               let uu____27249 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27249
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
            let uu___2192_27276 = g  in
            let uu____27277 =
              let uu____27278 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27278  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27277;
              FStar_TypeChecker_Common.deferred =
                (uu___2192_27276.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2192_27276.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2192_27276.FStar_TypeChecker_Common.implicits)
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
              let uu____27336 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27336 with
              | FStar_Pervasives_Native.Some
                  (uu____27361::(tm,uu____27363)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27427 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27445 = FStar_Syntax_Unionfind.fresh r  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27445;
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
                    (let uu____27479 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27479
                     then
                       let uu____27483 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27483
                     else ());
                    (let g =
                       let uu___2216_27489 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2216_27489.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2216_27489.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2216_27489.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27543 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27600  ->
                      fun b  ->
                        match uu____27600 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27642 =
                              let uu____27655 = reason b  in
                              new_implicit_var_aux uu____27655 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27642 with
                             | (t,uu____27672,g_t) ->
                                 let uu____27686 =
                                   let uu____27689 =
                                     let uu____27692 =
                                       let uu____27693 =
                                         let uu____27700 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27700, t)  in
                                       FStar_Syntax_Syntax.NT uu____27693  in
                                     [uu____27692]  in
                                   FStar_List.append substs1 uu____27689  in
                                 let uu____27711 = conj_guard g g_t  in
                                 (uu____27686, (FStar_List.append uvars [t]),
                                   uu____27711))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27543
              (fun uu____27740  ->
                 match uu____27740 with | (uu____27757,uvars,g) -> (uvars, g))
  
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
                let uu____27798 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____27798 FStar_Util.must  in
              let uu____27815 = inst_tscheme_with post_ts [u]  in
              match uu____27815 with
              | (uu____27820,post) ->
                  let uu____27822 =
                    let uu____27827 =
                      let uu____27828 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____27828]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____27827  in
                  uu____27822 FStar_Pervasives_Native.None r
               in
            let uu____27861 =
              let uu____27866 =
                let uu____27867 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____27867]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____27866  in
            uu____27861 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____27903  -> ());
    push = (fun uu____27905  -> ());
    pop = (fun uu____27908  -> ());
    snapshot =
      (fun uu____27911  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____27930  -> fun uu____27931  -> ());
    encode_sig = (fun uu____27946  -> fun uu____27947  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____27953 =
             let uu____27960 = FStar_Options.peek ()  in (e, g, uu____27960)
              in
           [uu____27953]);
    solve = (fun uu____27976  -> fun uu____27977  -> fun uu____27978  -> ());
    finish = (fun uu____27985  -> ());
    refresh = (fun uu____27987  -> ())
  } 