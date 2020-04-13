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
      (FStar_Options.should_verify (env1.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____13998) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14001,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14003,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14006 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'uuuuuu14020 . unit -> 'uuuuuu14020 FStar_Util.smap =
  fun uu____14027  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'uuuuuu14033 . unit -> 'uuuuuu14033 FStar_Util.smap =
  fun uu____14040  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____14178 = new_gamma_cache ()  in
                  let uu____14181 = new_sigtab ()  in
                  let uu____14184 = new_sigtab ()  in
                  let uu____14191 =
                    let uu____14206 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14206, FStar_Pervasives_Native.None)  in
                  let uu____14227 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14231 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14235 = FStar_Options.using_facts_from ()  in
                  let uu____14236 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14239 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14240 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14254 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14178;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14181;
                    attrtab = uu____14184;
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
                    qtbl_name_and_index = uu____14191;
                    normalized_eff_names = uu____14227;
                    fv_delta_depths = uu____14231;
                    proof_ns = uu____14235;
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
                    identifier_info = uu____14236;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14239;
                    nbe;
                    strict_args_tab = uu____14240;
                    erasable_types_tab = uu____14254
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
  fun uu____14445  ->
    let uu____14446 = FStar_ST.op_Bang query_indices  in
    match uu____14446 with
    | [] -> failwith "Empty query indices!"
    | uu____14501 ->
        let uu____14511 =
          let uu____14521 =
            let uu____14529 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14529  in
          let uu____14583 = FStar_ST.op_Bang query_indices  in uu____14521 ::
            uu____14583
           in
        FStar_ST.op_Colon_Equals query_indices uu____14511
  
let (pop_query_indices : unit -> unit) =
  fun uu____14679  ->
    let uu____14680 = FStar_ST.op_Bang query_indices  in
    match uu____14680 with
    | [] -> failwith "Empty query indices!"
    | hd::tl -> FStar_ST.op_Colon_Equals query_indices tl
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14807  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14844  ->
    match uu____14844 with
    | (l,n) ->
        let uu____14854 = FStar_ST.op_Bang query_indices  in
        (match uu____14854 with
         | hd::tl ->
             FStar_ST.op_Colon_Equals query_indices (((l, n) :: hd) :: tl)
         | uu____14976 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14999  ->
    let uu____15000 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15000
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env1  ->
    (let uu____15068 =
       let uu____15071 = FStar_ST.op_Bang stack  in env1 :: uu____15071  in
     FStar_ST.op_Colon_Equals stack uu____15068);
    (let uu___414_15120 = env1  in
     let uu____15121 = FStar_Util.smap_copy (gamma_cache env1)  in
     let uu____15124 = FStar_Util.smap_copy (sigtab env1)  in
     let uu____15127 = FStar_Util.smap_copy (attrtab env1)  in
     let uu____15134 =
       let uu____15149 =
         let uu____15153 =
           FStar_All.pipe_right env1.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15153  in
       let uu____15185 =
         FStar_All.pipe_right env1.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15149, uu____15185)  in
     let uu____15234 = FStar_Util.smap_copy env1.normalized_eff_names  in
     let uu____15237 = FStar_Util.smap_copy env1.fv_delta_depths  in
     let uu____15240 =
       let uu____15243 = FStar_ST.op_Bang env1.identifier_info  in
       FStar_Util.mk_ref uu____15243  in
     let uu____15263 = FStar_Util.smap_copy env1.strict_args_tab  in
     let uu____15276 = FStar_Util.smap_copy env1.erasable_types_tab  in
     {
       solver = (uu___414_15120.solver);
       range = (uu___414_15120.range);
       curmodule = (uu___414_15120.curmodule);
       gamma = (uu___414_15120.gamma);
       gamma_sig = (uu___414_15120.gamma_sig);
       gamma_cache = uu____15121;
       modules = (uu___414_15120.modules);
       expected_typ = (uu___414_15120.expected_typ);
       sigtab = uu____15124;
       attrtab = uu____15127;
       instantiate_imp = (uu___414_15120.instantiate_imp);
       effects = (uu___414_15120.effects);
       generalize = (uu___414_15120.generalize);
       letrecs = (uu___414_15120.letrecs);
       top_level = (uu___414_15120.top_level);
       check_uvars = (uu___414_15120.check_uvars);
       use_eq = (uu___414_15120.use_eq);
       use_eq_strict = (uu___414_15120.use_eq_strict);
       is_iface = (uu___414_15120.is_iface);
       admit = (uu___414_15120.admit);
       lax = (uu___414_15120.lax);
       lax_universes = (uu___414_15120.lax_universes);
       phase1 = (uu___414_15120.phase1);
       failhard = (uu___414_15120.failhard);
       nosynth = (uu___414_15120.nosynth);
       uvar_subtyping = (uu___414_15120.uvar_subtyping);
       tc_term = (uu___414_15120.tc_term);
       type_of = (uu___414_15120.type_of);
       universe_of = (uu___414_15120.universe_of);
       check_type_of = (uu___414_15120.check_type_of);
       use_bv_sorts = (uu___414_15120.use_bv_sorts);
       qtbl_name_and_index = uu____15134;
       normalized_eff_names = uu____15234;
       fv_delta_depths = uu____15237;
       proof_ns = (uu___414_15120.proof_ns);
       synth_hook = (uu___414_15120.synth_hook);
       try_solve_implicits_hook = (uu___414_15120.try_solve_implicits_hook);
       splice = (uu___414_15120.splice);
       mpreprocess = (uu___414_15120.mpreprocess);
       postprocess = (uu___414_15120.postprocess);
       identifier_info = uu____15240;
       tc_hooks = (uu___414_15120.tc_hooks);
       dsenv = (uu___414_15120.dsenv);
       nbe = (uu___414_15120.nbe);
       strict_args_tab = uu____15263;
       erasable_types_tab = uu____15276
     })
  
let (pop_stack : unit -> env) =
  fun uu____15286  ->
    let uu____15287 = FStar_ST.op_Bang stack  in
    match uu____15287 with
    | env1::tl -> (FStar_ST.op_Colon_Equals stack tl; env1)
    | uu____15341 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env1  -> FStar_Common.snapshot push_stack stack env1 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env1  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15431  ->
           let uu____15432 = snapshot_stack env1  in
           match uu____15432 with
           | (stack_depth,env2) ->
               let uu____15466 = snapshot_query_indices ()  in
               (match uu____15466 with
                | (query_indices_depth,()) ->
                    let uu____15499 = (env2.solver).snapshot msg  in
                    (match uu____15499 with
                     | (solver_depth,()) ->
                         let uu____15556 =
                           FStar_Syntax_DsEnv.snapshot env2.dsenv  in
                         (match uu____15556 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___439_15623 = env2  in
                                 {
                                   solver = (uu___439_15623.solver);
                                   range = (uu___439_15623.range);
                                   curmodule = (uu___439_15623.curmodule);
                                   gamma = (uu___439_15623.gamma);
                                   gamma_sig = (uu___439_15623.gamma_sig);
                                   gamma_cache = (uu___439_15623.gamma_cache);
                                   modules = (uu___439_15623.modules);
                                   expected_typ =
                                     (uu___439_15623.expected_typ);
                                   sigtab = (uu___439_15623.sigtab);
                                   attrtab = (uu___439_15623.attrtab);
                                   instantiate_imp =
                                     (uu___439_15623.instantiate_imp);
                                   effects = (uu___439_15623.effects);
                                   generalize = (uu___439_15623.generalize);
                                   letrecs = (uu___439_15623.letrecs);
                                   top_level = (uu___439_15623.top_level);
                                   check_uvars = (uu___439_15623.check_uvars);
                                   use_eq = (uu___439_15623.use_eq);
                                   use_eq_strict =
                                     (uu___439_15623.use_eq_strict);
                                   is_iface = (uu___439_15623.is_iface);
                                   admit = (uu___439_15623.admit);
                                   lax = (uu___439_15623.lax);
                                   lax_universes =
                                     (uu___439_15623.lax_universes);
                                   phase1 = (uu___439_15623.phase1);
                                   failhard = (uu___439_15623.failhard);
                                   nosynth = (uu___439_15623.nosynth);
                                   uvar_subtyping =
                                     (uu___439_15623.uvar_subtyping);
                                   tc_term = (uu___439_15623.tc_term);
                                   type_of = (uu___439_15623.type_of);
                                   universe_of = (uu___439_15623.universe_of);
                                   check_type_of =
                                     (uu___439_15623.check_type_of);
                                   use_bv_sorts =
                                     (uu___439_15623.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___439_15623.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___439_15623.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___439_15623.fv_delta_depths);
                                   proof_ns = (uu___439_15623.proof_ns);
                                   synth_hook = (uu___439_15623.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___439_15623.try_solve_implicits_hook);
                                   splice = (uu___439_15623.splice);
                                   mpreprocess = (uu___439_15623.mpreprocess);
                                   postprocess = (uu___439_15623.postprocess);
                                   identifier_info =
                                     (uu___439_15623.identifier_info);
                                   tc_hooks = (uu___439_15623.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___439_15623.nbe);
                                   strict_args_tab =
                                     (uu___439_15623.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___439_15623.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15657  ->
             let uu____15658 =
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
             match uu____15658 with
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
                             ((let uu____15838 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15838
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  ->
      let uu____15854 = snapshot env1 msg  in
      FStar_Pervasives_Native.snd uu____15854
  
let (pop : env -> Prims.string -> env) =
  fun env1  ->
    fun msg  -> rollback env1.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env1  ->
    let qix = peek_query_indices ()  in
    match env1.qtbl_name_and_index with
    | (uu____15886,FStar_Pervasives_Native.None ) -> env1
    | (tbl,FStar_Pervasives_Native.Some (l,n)) ->
        let uu____15928 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15958  ->
                  match uu____15958 with
                  | (m,uu____15966) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15928 with
         | FStar_Pervasives_Native.None  ->
             let next = n + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___484_15981 = env1  in
               {
                 solver = (uu___484_15981.solver);
                 range = (uu___484_15981.range);
                 curmodule = (uu___484_15981.curmodule);
                 gamma = (uu___484_15981.gamma);
                 gamma_sig = (uu___484_15981.gamma_sig);
                 gamma_cache = (uu___484_15981.gamma_cache);
                 modules = (uu___484_15981.modules);
                 expected_typ = (uu___484_15981.expected_typ);
                 sigtab = (uu___484_15981.sigtab);
                 attrtab = (uu___484_15981.attrtab);
                 instantiate_imp = (uu___484_15981.instantiate_imp);
                 effects = (uu___484_15981.effects);
                 generalize = (uu___484_15981.generalize);
                 letrecs = (uu___484_15981.letrecs);
                 top_level = (uu___484_15981.top_level);
                 check_uvars = (uu___484_15981.check_uvars);
                 use_eq = (uu___484_15981.use_eq);
                 use_eq_strict = (uu___484_15981.use_eq_strict);
                 is_iface = (uu___484_15981.is_iface);
                 admit = (uu___484_15981.admit);
                 lax = (uu___484_15981.lax);
                 lax_universes = (uu___484_15981.lax_universes);
                 phase1 = (uu___484_15981.phase1);
                 failhard = (uu___484_15981.failhard);
                 nosynth = (uu___484_15981.nosynth);
                 uvar_subtyping = (uu___484_15981.uvar_subtyping);
                 tc_term = (uu___484_15981.tc_term);
                 type_of = (uu___484_15981.type_of);
                 universe_of = (uu___484_15981.universe_of);
                 check_type_of = (uu___484_15981.check_type_of);
                 use_bv_sorts = (uu___484_15981.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___484_15981.normalized_eff_names);
                 fv_delta_depths = (uu___484_15981.fv_delta_depths);
                 proof_ns = (uu___484_15981.proof_ns);
                 synth_hook = (uu___484_15981.synth_hook);
                 try_solve_implicits_hook =
                   (uu___484_15981.try_solve_implicits_hook);
                 splice = (uu___484_15981.splice);
                 mpreprocess = (uu___484_15981.mpreprocess);
                 postprocess = (uu___484_15981.postprocess);
                 identifier_info = (uu___484_15981.identifier_info);
                 tc_hooks = (uu___484_15981.tc_hooks);
                 dsenv = (uu___484_15981.dsenv);
                 nbe = (uu___484_15981.nbe);
                 strict_args_tab = (uu___484_15981.strict_args_tab);
                 erasable_types_tab = (uu___484_15981.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15998,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___493_16014 = env1  in
               {
                 solver = (uu___493_16014.solver);
                 range = (uu___493_16014.range);
                 curmodule = (uu___493_16014.curmodule);
                 gamma = (uu___493_16014.gamma);
                 gamma_sig = (uu___493_16014.gamma_sig);
                 gamma_cache = (uu___493_16014.gamma_cache);
                 modules = (uu___493_16014.modules);
                 expected_typ = (uu___493_16014.expected_typ);
                 sigtab = (uu___493_16014.sigtab);
                 attrtab = (uu___493_16014.attrtab);
                 instantiate_imp = (uu___493_16014.instantiate_imp);
                 effects = (uu___493_16014.effects);
                 generalize = (uu___493_16014.generalize);
                 letrecs = (uu___493_16014.letrecs);
                 top_level = (uu___493_16014.top_level);
                 check_uvars = (uu___493_16014.check_uvars);
                 use_eq = (uu___493_16014.use_eq);
                 use_eq_strict = (uu___493_16014.use_eq_strict);
                 is_iface = (uu___493_16014.is_iface);
                 admit = (uu___493_16014.admit);
                 lax = (uu___493_16014.lax);
                 lax_universes = (uu___493_16014.lax_universes);
                 phase1 = (uu___493_16014.phase1);
                 failhard = (uu___493_16014.failhard);
                 nosynth = (uu___493_16014.nosynth);
                 uvar_subtyping = (uu___493_16014.uvar_subtyping);
                 tc_term = (uu___493_16014.tc_term);
                 type_of = (uu___493_16014.type_of);
                 universe_of = (uu___493_16014.universe_of);
                 check_type_of = (uu___493_16014.check_type_of);
                 use_bv_sorts = (uu___493_16014.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___493_16014.normalized_eff_names);
                 fv_delta_depths = (uu___493_16014.fv_delta_depths);
                 proof_ns = (uu___493_16014.proof_ns);
                 synth_hook = (uu___493_16014.synth_hook);
                 try_solve_implicits_hook =
                   (uu___493_16014.try_solve_implicits_hook);
                 splice = (uu___493_16014.splice);
                 mpreprocess = (uu___493_16014.mpreprocess);
                 postprocess = (uu___493_16014.postprocess);
                 identifier_info = (uu___493_16014.identifier_info);
                 tc_hooks = (uu___493_16014.tc_hooks);
                 dsenv = (uu___493_16014.dsenv);
                 nbe = (uu___493_16014.nbe);
                 strict_args_tab = (uu___493_16014.strict_args_tab);
                 erasable_types_tab = (uu___493_16014.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env1  ->
    fun l  -> FStar_Options.debug_at_level (env1.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___500_16057 = e  in
         {
           solver = (uu___500_16057.solver);
           range = r;
           curmodule = (uu___500_16057.curmodule);
           gamma = (uu___500_16057.gamma);
           gamma_sig = (uu___500_16057.gamma_sig);
           gamma_cache = (uu___500_16057.gamma_cache);
           modules = (uu___500_16057.modules);
           expected_typ = (uu___500_16057.expected_typ);
           sigtab = (uu___500_16057.sigtab);
           attrtab = (uu___500_16057.attrtab);
           instantiate_imp = (uu___500_16057.instantiate_imp);
           effects = (uu___500_16057.effects);
           generalize = (uu___500_16057.generalize);
           letrecs = (uu___500_16057.letrecs);
           top_level = (uu___500_16057.top_level);
           check_uvars = (uu___500_16057.check_uvars);
           use_eq = (uu___500_16057.use_eq);
           use_eq_strict = (uu___500_16057.use_eq_strict);
           is_iface = (uu___500_16057.is_iface);
           admit = (uu___500_16057.admit);
           lax = (uu___500_16057.lax);
           lax_universes = (uu___500_16057.lax_universes);
           phase1 = (uu___500_16057.phase1);
           failhard = (uu___500_16057.failhard);
           nosynth = (uu___500_16057.nosynth);
           uvar_subtyping = (uu___500_16057.uvar_subtyping);
           tc_term = (uu___500_16057.tc_term);
           type_of = (uu___500_16057.type_of);
           universe_of = (uu___500_16057.universe_of);
           check_type_of = (uu___500_16057.check_type_of);
           use_bv_sorts = (uu___500_16057.use_bv_sorts);
           qtbl_name_and_index = (uu___500_16057.qtbl_name_and_index);
           normalized_eff_names = (uu___500_16057.normalized_eff_names);
           fv_delta_depths = (uu___500_16057.fv_delta_depths);
           proof_ns = (uu___500_16057.proof_ns);
           synth_hook = (uu___500_16057.synth_hook);
           try_solve_implicits_hook =
             (uu___500_16057.try_solve_implicits_hook);
           splice = (uu___500_16057.splice);
           mpreprocess = (uu___500_16057.mpreprocess);
           postprocess = (uu___500_16057.postprocess);
           identifier_info = (uu___500_16057.identifier_info);
           tc_hooks = (uu___500_16057.tc_hooks);
           dsenv = (uu___500_16057.dsenv);
           nbe = (uu___500_16057.nbe);
           strict_args_tab = (uu___500_16057.strict_args_tab);
           erasable_types_tab = (uu___500_16057.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env1  ->
    fun enabled  ->
      let uu____16077 =
        let uu____16078 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16078 enabled  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16077
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun bv  ->
      fun ty  ->
        let uu____16133 =
          let uu____16134 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16134 bv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16133
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env1  ->
    fun fv  ->
      fun ty  ->
        let uu____16189 =
          let uu____16190 = FStar_ST.op_Bang env1.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16190 fv ty  in
        FStar_ST.op_Colon_Equals env1.identifier_info uu____16189
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env1  ->
    fun ty_map  ->
      let uu____16245 =
        let uu____16246 = FStar_ST.op_Bang env1.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16246 ty_map  in
      FStar_ST.op_Colon_Equals env1.identifier_info uu____16245
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env1  -> env1.modules 
let (current_module : env -> FStar_Ident.lident) =
  fun env1  -> env1.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env1  ->
    fun lid  ->
      let uu___517_16310 = env1  in
      {
        solver = (uu___517_16310.solver);
        range = (uu___517_16310.range);
        curmodule = lid;
        gamma = (uu___517_16310.gamma);
        gamma_sig = (uu___517_16310.gamma_sig);
        gamma_cache = (uu___517_16310.gamma_cache);
        modules = (uu___517_16310.modules);
        expected_typ = (uu___517_16310.expected_typ);
        sigtab = (uu___517_16310.sigtab);
        attrtab = (uu___517_16310.attrtab);
        instantiate_imp = (uu___517_16310.instantiate_imp);
        effects = (uu___517_16310.effects);
        generalize = (uu___517_16310.generalize);
        letrecs = (uu___517_16310.letrecs);
        top_level = (uu___517_16310.top_level);
        check_uvars = (uu___517_16310.check_uvars);
        use_eq = (uu___517_16310.use_eq);
        use_eq_strict = (uu___517_16310.use_eq_strict);
        is_iface = (uu___517_16310.is_iface);
        admit = (uu___517_16310.admit);
        lax = (uu___517_16310.lax);
        lax_universes = (uu___517_16310.lax_universes);
        phase1 = (uu___517_16310.phase1);
        failhard = (uu___517_16310.failhard);
        nosynth = (uu___517_16310.nosynth);
        uvar_subtyping = (uu___517_16310.uvar_subtyping);
        tc_term = (uu___517_16310.tc_term);
        type_of = (uu___517_16310.type_of);
        universe_of = (uu___517_16310.universe_of);
        check_type_of = (uu___517_16310.check_type_of);
        use_bv_sorts = (uu___517_16310.use_bv_sorts);
        qtbl_name_and_index = (uu___517_16310.qtbl_name_and_index);
        normalized_eff_names = (uu___517_16310.normalized_eff_names);
        fv_delta_depths = (uu___517_16310.fv_delta_depths);
        proof_ns = (uu___517_16310.proof_ns);
        synth_hook = (uu___517_16310.synth_hook);
        try_solve_implicits_hook = (uu___517_16310.try_solve_implicits_hook);
        splice = (uu___517_16310.splice);
        mpreprocess = (uu___517_16310.mpreprocess);
        postprocess = (uu___517_16310.postprocess);
        identifier_info = (uu___517_16310.identifier_info);
        tc_hooks = (uu___517_16310.tc_hooks);
        dsenv = (uu___517_16310.dsenv);
        nbe = (uu___517_16310.nbe);
        strict_args_tab = (uu___517_16310.strict_args_tab);
        erasable_types_tab = (uu___517_16310.erasable_types_tab)
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
      let uu____16341 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env1) uu____16341
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16354 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16354)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v  ->
    let uu____16369 =
      let uu____16371 = FStar_Syntax_Print.bv_to_string v  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16371  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16369)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16380  ->
    let uu____16381 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16381
  
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
      | ((formals,t),uu____16481) ->
          let vs = mk_univ_subst formals us  in
          let uu____16505 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16505)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16522  ->
    match uu___1_16522 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16548  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16568 = inst_tscheme t  in
      match uu____16568 with
      | (us,t1) ->
          let uu____16579 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16579)
  
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
          let uu____16604 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16606 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16604 uu____16606
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
        fun uu____16633  ->
          match uu____16633 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env1.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16647 =
                    let uu____16649 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16653 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16657 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16659 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16649 uu____16653 uu____16657 uu____16659
                     in
                  failwith uu____16647)
               else ();
               (let uu____16664 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16664))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16682 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16693 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16704 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env1  ->
    fun l  ->
      let cur = current_module env1  in
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
             | ([],uu____16752) -> Maybe
             | (uu____16759,[]) -> No
             | (hd::tl,hd'::tl') when
                 hd.FStar_Ident.idText = hd'.FStar_Ident.idText -> aux tl tl'
             | uu____16779 -> No  in
           aux cur1 lns)
        else No
  
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
        FStar_Util.smap_add (gamma_cache env1) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____16873 =
            FStar_Util.smap_try_find (gamma_cache env1) lid.FStar_Ident.str
             in
          match uu____16873 with
          | FStar_Pervasives_Native.None  ->
              let uu____16896 =
                FStar_Util.find_map env1.gamma
                  (fun uu___2_16940  ->
                     match uu___2_16940 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16979 = FStar_Ident.lid_equals lid l  in
                         if uu____16979
                         then
                           let uu____17002 =
                             let uu____17021 =
                               let uu____17036 = inst_tscheme t  in
                               FStar_Util.Inl uu____17036  in
                             let uu____17051 = FStar_Ident.range_of_lid l  in
                             (uu____17021, uu____17051)  in
                           FStar_Pervasives_Native.Some uu____17002
                         else FStar_Pervasives_Native.None
                     | uu____17104 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16896
                (fun uu____17142  ->
                   FStar_Util.find_map env1.gamma_sig
                     (fun uu___3_17152  ->
                        match uu___3_17152 with
                        | (uu____17155,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17157);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17158;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17159;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17160;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17161;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17162;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17184 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17184
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
                                  uu____17236 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17243 -> cache t  in
                            let uu____17244 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17244 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17250 =
                                   let uu____17251 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17251)
                                    in
                                 maybe_cache uu____17250)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17322 = find_in_sigtab env1 lid  in
         match uu____17322 with
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
      let uu____17403 = lookup_qname env1 lid  in
      match uu____17403 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17424,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env1  ->
    fun attr  ->
      let uu____17538 = FStar_Util.smap_try_find (attrtab env1) attr  in
      match uu____17538 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      let add_one env2 se1 attr =
        let uu____17583 =
          let uu____17586 = lookup_attr env2 attr  in se1 :: uu____17586  in
        FStar_Util.smap_add (attrtab env2) attr uu____17583  in
      FStar_List.iter
        (fun attr  ->
           let uu____17596 =
             let uu____17597 = FStar_Syntax_Subst.compress attr  in
             uu____17597.FStar_Syntax_Syntax.n  in
           match uu____17596 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17601 =
                 let uu____17603 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____17603.FStar_Ident.str  in
               add_one env1 se uu____17601
           | uu____17604 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env1  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17627) ->
          add_sigelts env1 ses
      | uu____17636 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  ->
                FStar_Util.smap_add (sigtab env1) l.FStar_Ident.str se) lids;
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
        (fun uu___4_17674  ->
           match uu___4_17674 with
           | FStar_Syntax_Syntax.Binding_var id when
               FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17692 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17754,lb::[]),uu____17756) ->
            let uu____17765 =
              let uu____17774 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17783 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17774, uu____17783)  in
            FStar_Pervasives_Native.Some uu____17765
        | FStar_Syntax_Syntax.Sig_let ((uu____17796,lbs),uu____17798) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17830 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17843 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17843
                     then
                       let uu____17856 =
                         let uu____17865 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17874 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17865, uu____17874)  in
                       FStar_Pervasives_Native.Some uu____17856
                     else FStar_Pervasives_Native.None)
        | uu____17897 -> FStar_Pervasives_Native.None
  
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
                    let uu____17989 =
                      let uu____17991 =
                        let uu____17993 =
                          let uu____17995 =
                            let uu____17997 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18003 =
                              let uu____18005 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18005  in
                            Prims.op_Hat uu____17997 uu____18003  in
                          Prims.op_Hat ", expected " uu____17995  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17993
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17991
                       in
                    failwith uu____17989
                  else ());
             (let uu____18012 =
                let uu____18021 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18021, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18012))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18041,uu____18042) ->
            let uu____18047 =
              let uu____18056 =
                let uu____18061 =
                  let uu____18062 =
                    let uu____18065 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18065  in
                  (us, uu____18062)  in
                inst_ts us_opt uu____18061  in
              (uu____18056, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18047
        | uu____18084 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____18173 =
          match uu____18173 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18269,uvs,t,uu____18272,uu____18273,uu____18274);
                      FStar_Syntax_Syntax.sigrng = uu____18275;
                      FStar_Syntax_Syntax.sigquals = uu____18276;
                      FStar_Syntax_Syntax.sigmeta = uu____18277;
                      FStar_Syntax_Syntax.sigattrs = uu____18278;
                      FStar_Syntax_Syntax.sigopts = uu____18279;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18304 =
                     let uu____18313 = inst_tscheme1 (uvs, t)  in
                     (uu____18313, rng)  in
                   FStar_Pervasives_Native.Some uu____18304
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18337;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18339;
                      FStar_Syntax_Syntax.sigattrs = uu____18340;
                      FStar_Syntax_Syntax.sigopts = uu____18341;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18360 =
                     let uu____18362 = in_cur_mod env1 l  in
                     uu____18362 = Yes  in
                   if uu____18360
                   then
                     let uu____18374 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env1.is_iface
                        in
                     (if uu____18374
                      then
                        let uu____18390 =
                          let uu____18399 = inst_tscheme1 (uvs, t)  in
                          (uu____18399, rng)  in
                        FStar_Pervasives_Native.Some uu____18390
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18432 =
                        let uu____18441 = inst_tscheme1 (uvs, t)  in
                        (uu____18441, rng)  in
                      FStar_Pervasives_Native.Some uu____18432)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18466,uu____18467);
                      FStar_Syntax_Syntax.sigrng = uu____18468;
                      FStar_Syntax_Syntax.sigquals = uu____18469;
                      FStar_Syntax_Syntax.sigmeta = uu____18470;
                      FStar_Syntax_Syntax.sigattrs = uu____18471;
                      FStar_Syntax_Syntax.sigopts = uu____18472;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18515 =
                          let uu____18524 = inst_tscheme1 (uvs, k)  in
                          (uu____18524, rng)  in
                        FStar_Pervasives_Native.Some uu____18515
                    | uu____18545 ->
                        let uu____18546 =
                          let uu____18555 =
                            let uu____18560 =
                              let uu____18561 =
                                let uu____18564 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18564
                                 in
                              (uvs, uu____18561)  in
                            inst_tscheme1 uu____18560  in
                          (uu____18555, rng)  in
                        FStar_Pervasives_Native.Some uu____18546)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18587,uu____18588);
                      FStar_Syntax_Syntax.sigrng = uu____18589;
                      FStar_Syntax_Syntax.sigquals = uu____18590;
                      FStar_Syntax_Syntax.sigmeta = uu____18591;
                      FStar_Syntax_Syntax.sigattrs = uu____18592;
                      FStar_Syntax_Syntax.sigopts = uu____18593;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18637 =
                          let uu____18646 = inst_tscheme_with (uvs, k) us  in
                          (uu____18646, rng)  in
                        FStar_Pervasives_Native.Some uu____18637
                    | uu____18667 ->
                        let uu____18668 =
                          let uu____18677 =
                            let uu____18682 =
                              let uu____18683 =
                                let uu____18686 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18686
                                 in
                              (uvs, uu____18683)  in
                            inst_tscheme_with uu____18682 us  in
                          (uu____18677, rng)  in
                        FStar_Pervasives_Native.Some uu____18668)
               | FStar_Util.Inr se ->
                   let uu____18722 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18743;
                          FStar_Syntax_Syntax.sigrng = uu____18744;
                          FStar_Syntax_Syntax.sigquals = uu____18745;
                          FStar_Syntax_Syntax.sigmeta = uu____18746;
                          FStar_Syntax_Syntax.sigattrs = uu____18747;
                          FStar_Syntax_Syntax.sigopts = uu____18748;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18765 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env1.range
                      in
                   FStar_All.pipe_right uu____18722
                     (FStar_Util.map_option
                        (fun uu____18813  ->
                           match uu____18813 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18844 =
          let uu____18855 = lookup_qname env1 lid  in
          FStar_Util.bind_opt uu____18855 mapper  in
        match uu____18844 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18929 =
              let uu____18940 =
                let uu____18947 =
                  let uu___854_18950 = t  in
                  let uu____18951 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___854_18950.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18951;
                    FStar_Syntax_Syntax.vars =
                      (uu___854_18950.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18947)  in
              (uu____18940, r)  in
            FStar_Pervasives_Native.Some uu____18929
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____19000 = lookup_qname env1 l  in
      match uu____19000 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19021 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env1  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19075 = try_lookup_bv env1 bv  in
      match uu____19075 with
      | FStar_Pervasives_Native.None  ->
          let uu____19090 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19090 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19106 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19107 =
            let uu____19108 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19108  in
          (uu____19106, uu____19107)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l  ->
      let uu____19130 =
        try_lookup_lid_aux FStar_Pervasives_Native.None env1 l  in
      match uu____19130 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19196 = FStar_Range.use_range use_range  in
            FStar_Range.set_use_range r uu____19196  in
          let uu____19197 =
            let uu____19206 =
              let uu____19211 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (us, uu____19211)  in
            (uu____19206, r1)  in
          FStar_Pervasives_Native.Some uu____19197
  
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
        let uu____19246 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env1 l  in
        match uu____19246 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19279,t),r) ->
            let use_range = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19304 = FStar_Range.use_range use_range  in
              FStar_Range.set_use_range r uu____19304  in
            let uu____19305 =
              let uu____19310 = FStar_Syntax_Subst.set_use_range use_range t
                 in
              (uu____19310, r1)  in
            FStar_Pervasives_Native.Some uu____19305
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env1  ->
    fun l  ->
      let uu____19334 = try_lookup_lid env1 l  in
      match uu____19334 with
      | FStar_Pervasives_Native.None  ->
          let uu____19361 = name_not_found l  in
          let uu____19367 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19361 uu____19367
      | FStar_Pervasives_Native.Some v -> v
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env1  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19410  ->
              match uu___5_19410 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19414 -> false) env1.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____19435 = lookup_qname env1 lid  in
      match uu____19435 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19444,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19447;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19449;
              FStar_Syntax_Syntax.sigattrs = uu____19450;
              FStar_Syntax_Syntax.sigopts = uu____19451;_},FStar_Pervasives_Native.None
            ),uu____19452)
          ->
          let uu____19503 =
            let uu____19510 =
              let uu____19511 =
                let uu____19514 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19514 t  in
              (uvs, uu____19511)  in
            (uu____19510, q)  in
          FStar_Pervasives_Native.Some uu____19503
      | uu____19527 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19549 = lookup_qname env1 lid  in
      match uu____19549 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19554,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19557;
              FStar_Syntax_Syntax.sigquals = uu____19558;
              FStar_Syntax_Syntax.sigmeta = uu____19559;
              FStar_Syntax_Syntax.sigattrs = uu____19560;
              FStar_Syntax_Syntax.sigopts = uu____19561;_},FStar_Pervasives_Native.None
            ),uu____19562)
          ->
          let uu____19613 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19613 (uvs, t)
      | uu____19618 ->
          let uu____19619 = name_not_found lid  in
          let uu____19625 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19619 uu____19625
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env1  ->
    fun lid  ->
      let uu____19645 = lookup_qname env1 lid  in
      match uu____19645 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19650,uvs,t,uu____19653,uu____19654,uu____19655);
              FStar_Syntax_Syntax.sigrng = uu____19656;
              FStar_Syntax_Syntax.sigquals = uu____19657;
              FStar_Syntax_Syntax.sigmeta = uu____19658;
              FStar_Syntax_Syntax.sigattrs = uu____19659;
              FStar_Syntax_Syntax.sigopts = uu____19660;_},FStar_Pervasives_Native.None
            ),uu____19661)
          ->
          let uu____19718 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19718 (uvs, t)
      | uu____19723 ->
          let uu____19724 = name_not_found lid  in
          let uu____19730 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19724 uu____19730
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env1  ->
    fun lid  ->
      let uu____19753 = lookup_qname env1 lid  in
      match uu____19753 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19761,uu____19762,uu____19763,uu____19764,uu____19765,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19767;
              FStar_Syntax_Syntax.sigquals = uu____19768;
              FStar_Syntax_Syntax.sigmeta = uu____19769;
              FStar_Syntax_Syntax.sigattrs = uu____19770;
              FStar_Syntax_Syntax.sigopts = uu____19771;_},uu____19772),uu____19773)
          -> (true, dcs)
      | uu____19838 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      let uu____19854 = lookup_qname env1 lid  in
      match uu____19854 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19855,uu____19856,uu____19857,l,uu____19859,uu____19860);
              FStar_Syntax_Syntax.sigrng = uu____19861;
              FStar_Syntax_Syntax.sigquals = uu____19862;
              FStar_Syntax_Syntax.sigmeta = uu____19863;
              FStar_Syntax_Syntax.sigattrs = uu____19864;
              FStar_Syntax_Syntax.sigopts = uu____19865;_},uu____19866),uu____19867)
          -> l
      | uu____19926 ->
          let uu____19927 =
            let uu____19929 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19929  in
          failwith uu____19927
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19999)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20056) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20080 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20080
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20115 -> FStar_Pervasives_Native.None)
          | uu____20124 -> FStar_Pervasives_Native.None
  
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
        let uu____20186 = lookup_qname env1 lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20186
  
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
        let uu____20219 = lookup_qname env1 lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20219
  
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
             (FStar_Util.Inl uu____20271,uu____20272) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20321),uu____20322) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20371 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20389 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20399 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20416 ->
                  let uu____20423 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20423
              | FStar_Syntax_Syntax.Sig_let ((uu____20424,lbs),uu____20426)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20442 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20442
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_fail uu____20449 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_splice uu____20465 ->
                  failwith "impossible: delta_depth_of_qninfo"
              | FStar_Syntax_Syntax.Sig_main uu____20475 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20476 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20483 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20484 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20485 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20498 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20499 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env1  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20527 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env1.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20527
           (fun d_opt  ->
              let uu____20540 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20540
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20550 =
                   let uu____20553 =
                     lookup_qname env1
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20553  in
                 match uu____20550 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20554 =
                       let uu____20556 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20556
                        in
                     failwith uu____20554
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20561 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20561
                       then
                         let uu____20564 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20566 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20568 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20564 uu____20566 uu____20568
                       else ());
                      FStar_Util.smap_add env1.fv_delta_depths
                        lid.FStar_Ident.str d;
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20593),uu____20594) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20643 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20665),uu____20666) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20715 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun lid  ->
      let uu____20737 = lookup_qname env1 lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20737
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20770 = lookup_attrs_of_lid env1 fv_lid  in
        match uu____20770 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20792 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20801 =
                        let uu____20802 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20802.FStar_Syntax_Syntax.n  in
                      match uu____20801 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20807 -> false))
               in
            (true, uu____20792)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env1  ->
    fun fv_lid  ->
      fun attr_lid  ->
        let uu____20830 = fv_exists_and_has_attr env1 fv_lid attr_lid  in
        FStar_Pervasives_Native.snd uu____20830
  
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
          let uu____20902 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20902.FStar_Ident.str  in
        let uu____20903 = FStar_Util.smap_try_find tab s  in
        match uu____20903 with
        | FStar_Pervasives_Native.None  ->
            let uu____20906 = f ()  in
            (match uu____20906 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env1  ->
    fun fv  ->
      let f uu____20944 =
        let uu____20945 =
          fv_exists_and_has_attr env1
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20945 with | (ex,erasable) -> (ex, erasable)  in
      cache_in_fv_tab env1.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____20979 =
        let uu____20980 = FStar_Syntax_Util.unrefine t  in
        uu____20980.FStar_Syntax_Syntax.n  in
      match uu____20979 with
      | FStar_Syntax_Syntax.Tm_type uu____20984 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env1 fv)
      | FStar_Syntax_Syntax.Tm_app (head,uu____20988) ->
          non_informative env1 head
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21014) ->
          non_informative env1 t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21019,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env1 (FStar_Syntax_Util.comp_result c))
      | uu____21041 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun fv  ->
      let f uu____21074 =
        let attrs =
          let uu____21080 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env1 uu____21080  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21120 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21120)
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
      let uu____21165 = lookup_qname env1 ftv  in
      match uu____21165 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21169) ->
          let uu____21214 =
            effect_signature FStar_Pervasives_Native.None se env1.range  in
          (match uu____21214 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21235,t),r) ->
               let uu____21250 =
                 let uu____21251 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21251 t  in
               FStar_Pervasives_Native.Some uu____21250)
      | uu____21252 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env1  ->
    fun ftv  ->
      let uu____21264 = try_lookup_effect_lid env1 ftv  in
      match uu____21264 with
      | FStar_Pervasives_Native.None  ->
          let uu____21267 = name_not_found ftv  in
          let uu____21273 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21267 uu____21273
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
        let uu____21297 = lookup_qname env1 lid0  in
        match uu____21297 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs,binders,c,uu____21308);
                FStar_Syntax_Syntax.sigrng = uu____21309;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21311;
                FStar_Syntax_Syntax.sigattrs = uu____21312;
                FStar_Syntax_Syntax.sigopts = uu____21313;_},FStar_Pervasives_Native.None
              ),uu____21314)
            ->
            let lid1 =
              let uu____21370 =
                let uu____21371 = FStar_Ident.range_of_lid lid  in
                let uu____21372 =
                  let uu____21373 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21373  in
                FStar_Range.set_use_range uu____21371 uu____21372  in
              FStar_Ident.set_lid_range lid uu____21370  in
            let uu____21374 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21380  ->
                      match uu___6_21380 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21383 -> false))
               in
            if uu____21374
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) = (FStar_List.length univs)
                 then univ_insts
                 else
                   (let uu____21402 =
                      let uu____21404 =
                        let uu____21406 = get_range env1  in
                        FStar_Range.string_of_range uu____21406  in
                      let uu____21407 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21409 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21404 uu____21407 uu____21409
                       in
                    failwith uu____21402)
                  in
               match (binders, univs) with
               | ([],uu____21430) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21456,uu____21457::uu____21458::uu____21459) ->
                   let uu____21480 =
                     let uu____21482 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21484 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21482 uu____21484
                      in
                   failwith uu____21480
               | uu____21495 ->
                   let uu____21510 =
                     let uu____21515 =
                       let uu____21516 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs, uu____21516)  in
                     inst_tscheme_with uu____21515 insts  in
                   (match uu____21510 with
                    | (uu____21529,t) ->
                        let t1 =
                          let uu____21532 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21532 t  in
                        let uu____21533 =
                          let uu____21534 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21534.FStar_Syntax_Syntax.n  in
                        (match uu____21533 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21569 -> failwith "Impossible")))
        | uu____21577 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env1  ->
    fun l  ->
      let rec find l1 =
        let uu____21601 =
          lookup_effect_abbrev env1 [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21601 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21614,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21621 = find l2  in
            (match uu____21621 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21628 =
          FStar_Util.smap_try_find env1.normalized_eff_names
            l.FStar_Ident.str
           in
        match uu____21628 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21632 = find l  in
            (match uu____21632 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env1.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____21637 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21637
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env1  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21658 =
            FStar_All.pipe_right name (lookup_effect_lid env1)  in
          FStar_All.pipe_right uu____21658 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21664) ->
            FStar_List.length bs
        | uu____21703 ->
            let uu____21704 =
              let uu____21710 =
                let uu____21712 = FStar_Ident.string_of_lid name  in
                let uu____21714 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21712 uu____21714
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21710)
               in
            FStar_Errors.raise_error uu____21704 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env1  ->
    fun l  ->
      let l1 = norm_eff_name env1 l  in
      let uu____21733 = lookup_qname env1 l1  in
      match uu____21733 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21736;
              FStar_Syntax_Syntax.sigrng = uu____21737;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21739;
              FStar_Syntax_Syntax.sigattrs = uu____21740;
              FStar_Syntax_Syntax.sigopts = uu____21741;_},uu____21742),uu____21743)
          -> q
      | uu____21796 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env1  ->
    fun lid  ->
      fun i  ->
        let fail uu____21820 =
          let uu____21821 =
            let uu____21823 = FStar_Util.string_of_int i  in
            let uu____21825 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21823 uu____21825
             in
          failwith uu____21821  in
        let uu____21828 = lookup_datacon env1 lid  in
        match uu____21828 with
        | (uu____21833,t) ->
            let uu____21835 =
              let uu____21836 = FStar_Syntax_Subst.compress t  in
              uu____21836.FStar_Syntax_Syntax.n  in
            (match uu____21835 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21840) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    FStar_Syntax_Util.mk_field_projector_name lid
                      (FStar_Pervasives_Native.fst b) i)
             | uu____21886 -> fail ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____21900 = lookup_qname env1 l  in
      match uu____21900 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21902,uu____21903,uu____21904);
              FStar_Syntax_Syntax.sigrng = uu____21905;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21907;
              FStar_Syntax_Syntax.sigattrs = uu____21908;
              FStar_Syntax_Syntax.sigopts = uu____21909;_},uu____21910),uu____21911)
          ->
          FStar_Util.for_some
            (fun uu___7_21966  ->
               match uu___7_21966 with
               | FStar_Syntax_Syntax.Projector uu____21968 -> true
               | uu____21974 -> false) quals
      | uu____21976 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____21990 = lookup_qname env1 lid  in
      match uu____21990 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21992,uu____21993,uu____21994,uu____21995,uu____21996,uu____21997);
              FStar_Syntax_Syntax.sigrng = uu____21998;
              FStar_Syntax_Syntax.sigquals = uu____21999;
              FStar_Syntax_Syntax.sigmeta = uu____22000;
              FStar_Syntax_Syntax.sigattrs = uu____22001;
              FStar_Syntax_Syntax.sigopts = uu____22002;_},uu____22003),uu____22004)
          -> true
      | uu____22064 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22078 = lookup_qname env1 lid  in
      match uu____22078 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22080,uu____22081,uu____22082,uu____22083,uu____22084,uu____22085);
              FStar_Syntax_Syntax.sigrng = uu____22086;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22088;
              FStar_Syntax_Syntax.sigattrs = uu____22089;
              FStar_Syntax_Syntax.sigopts = uu____22090;_},uu____22091),uu____22092)
          ->
          FStar_Util.for_some
            (fun uu___8_22155  ->
               match uu___8_22155 with
               | FStar_Syntax_Syntax.RecordType uu____22157 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22167 -> true
               | uu____22177 -> false) quals
      | uu____22179 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo1  ->
    match qninfo1 with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22189,uu____22190);
            FStar_Syntax_Syntax.sigrng = uu____22191;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22193;
            FStar_Syntax_Syntax.sigattrs = uu____22194;
            FStar_Syntax_Syntax.sigopts = uu____22195;_},uu____22196),uu____22197)
        ->
        FStar_Util.for_some
          (fun uu___9_22256  ->
             match uu___9_22256 with
             | FStar_Syntax_Syntax.Action uu____22258 -> true
             | uu____22260 -> false) quals
    | uu____22262 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____22276 = lookup_qname env1 lid  in
      FStar_All.pipe_left qninfo_is_action uu____22276
  
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
      let uu____22293 =
        let uu____22294 = FStar_Syntax_Util.un_uinst head  in
        uu____22294.FStar_Syntax_Syntax.n  in
      match uu____22293 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22300 ->
               true
           | uu____22303 -> false)
      | uu____22305 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22319 = lookup_qname env1 l  in
      match uu____22319 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22322),uu____22323) ->
          FStar_Util.for_some
            (fun uu___10_22371  ->
               match uu___10_22371 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22374 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22376 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22452 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22470) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22488 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22496 ->
                 FStar_Pervasives_Native.Some true
             | uu____22515 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22518 =
        let uu____22522 = lookup_qname env1 lid  in
        FStar_Util.bind_opt uu____22522 mapper  in
      match uu____22518 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env1  ->
    fun lid  ->
      let uu____22582 = lookup_qname env1 lid  in
      match uu____22582 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22586,uu____22587,tps,uu____22589,uu____22590,uu____22591);
              FStar_Syntax_Syntax.sigrng = uu____22592;
              FStar_Syntax_Syntax.sigquals = uu____22593;
              FStar_Syntax_Syntax.sigmeta = uu____22594;
              FStar_Syntax_Syntax.sigattrs = uu____22595;
              FStar_Syntax_Syntax.sigopts = uu____22596;_},uu____22597),uu____22598)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22666 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22712  ->
              match uu____22712 with
              | (d,uu____22721) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env1  ->
    fun l  ->
      let uu____22737 = effect_decl_opt env1 l  in
      match uu____22737 with
      | FStar_Pervasives_Native.None  ->
          let uu____22752 = name_not_found l  in
          let uu____22758 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22752 uu____22758
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun l  ->
      let uu____22786 = FStar_All.pipe_right l (get_effect_decl env1)  in
      FStar_All.pipe_right uu____22786 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22793  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22807  ->
            fun uu____22808  -> fun e  -> FStar_Util.return_all e))
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
        let uu____22842 = FStar_Ident.lid_equals l1 l2  in
        if uu____22842
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____22861 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22861
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____22880 =
                FStar_All.pipe_right (env1.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22933  ->
                        match uu____22933 with
                        | (m1,m2,uu____22947,uu____22948,uu____22949) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22880 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____22974,uu____22975,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23023 = join_opt env1 l1 l2  in
        match uu____23023 with
        | FStar_Pervasives_Native.None  ->
            let uu____23044 =
              let uu____23050 =
                let uu____23052 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23054 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23052 uu____23054
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23050)  in
            FStar_Errors.raise_error uu____23044 env1.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun l1  ->
      fun l2  ->
        let uu____23097 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23097
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
  'uuuuuu23117 .
    (FStar_Syntax_Syntax.eff_decl * 'uuuuuu23117) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23146 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23172  ->
                match uu____23172 with
                | (d,uu____23179) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23146 with
      | FStar_Pervasives_Native.None  ->
          let uu____23190 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23190
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23205 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23205 with
           | (uu____23216,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23234)::(wp,uu____23236)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23292 -> failwith "Impossible"))
  
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
        | uu____23357 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env1  ->
    fun comp  ->
      let c = comp_to_comp_typ env1 comp  in
      let uu____23370 =
        lookup_effect_abbrev env1 c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23370 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23387 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23387 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23412 =
                     let uu____23418 =
                       let uu____23420 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23428 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23439 =
                         let uu____23441 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23441  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23420 uu____23428 uu____23439
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23418)
                      in
                   FStar_Errors.raise_error uu____23412
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst =
                   let uu____23449 =
                     let uu____23460 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23460 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23497  ->
                        fun uu____23498  ->
                          match (uu____23497, uu____23498) with
                          | ((x,uu____23528),(t,uu____23530)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23449
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst cdef1  in
                 let c2 =
                   let uu____23561 =
                     let uu___1610_23562 = comp_to_comp_typ env1 c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1610_23562.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1610_23562.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1610_23562.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1610_23562.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23561
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env1 c2)))
  
let effect_repr_aux :
  'uuuuuu23574 .
    'uuuuuu23574 ->
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
            let uu____23615 =
              let uu____23622 = num_effect_indices env1 eff_name r  in
              ((FStar_List.length args), uu____23622)  in
            match uu____23615 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23646 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23648 = FStar_Util.string_of_int given  in
                     let uu____23650 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23646 uu____23648 uu____23650
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env1 (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23655 = effect_decl_opt env1 effect_name  in
          match uu____23655 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23677) ->
              let uu____23688 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23688 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env1 c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env1 ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23706 =
                       let uu____23709 = get_range env1  in
                       let uu____23710 =
                         let uu____23717 =
                           let uu____23718 =
                             let uu____23735 =
                               let uu____23746 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23746 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23735)  in
                           FStar_Syntax_Syntax.Tm_app uu____23718  in
                         FStar_Syntax_Syntax.mk uu____23717  in
                       uu____23710 FStar_Pervasives_Native.None uu____23709
                        in
                     FStar_Pervasives_Native.Some uu____23706)))
  
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
           (fun uu___11_23846  ->
              match uu___11_23846 with
              | FStar_Syntax_Syntax.Reflectable uu____23848 -> true
              | uu____23850 -> false))
  
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
      | uu____23910 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let uu____23925 =
        let uu____23926 = FStar_Syntax_Subst.compress t  in
        uu____23926.FStar_Syntax_Syntax.n  in
      match uu____23925 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23930,c) ->
          is_reifiable_comp env1 c
      | uu____23952 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23972 =
           let uu____23974 = is_reifiable_effect env1 l  in
           Prims.op_Negation uu____23974  in
         if uu____23972
         then
           let uu____23977 =
             let uu____23983 =
               let uu____23985 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23985
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23983)  in
           let uu____23989 = get_range env1  in
           FStar_Errors.raise_error uu____23977 uu____23989
         else ());
        (let uu____23992 = effect_repr_aux true env1 c u_c  in
         match uu____23992 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env1  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env2 =
        let uu___1687_24028 = env1  in
        {
          solver = (uu___1687_24028.solver);
          range = (uu___1687_24028.range);
          curmodule = (uu___1687_24028.curmodule);
          gamma = (uu___1687_24028.gamma);
          gamma_sig = (sb :: (env1.gamma_sig));
          gamma_cache = (uu___1687_24028.gamma_cache);
          modules = (uu___1687_24028.modules);
          expected_typ = (uu___1687_24028.expected_typ);
          sigtab = (uu___1687_24028.sigtab);
          attrtab = (uu___1687_24028.attrtab);
          instantiate_imp = (uu___1687_24028.instantiate_imp);
          effects = (uu___1687_24028.effects);
          generalize = (uu___1687_24028.generalize);
          letrecs = (uu___1687_24028.letrecs);
          top_level = (uu___1687_24028.top_level);
          check_uvars = (uu___1687_24028.check_uvars);
          use_eq = (uu___1687_24028.use_eq);
          use_eq_strict = (uu___1687_24028.use_eq_strict);
          is_iface = (uu___1687_24028.is_iface);
          admit = (uu___1687_24028.admit);
          lax = (uu___1687_24028.lax);
          lax_universes = (uu___1687_24028.lax_universes);
          phase1 = (uu___1687_24028.phase1);
          failhard = (uu___1687_24028.failhard);
          nosynth = (uu___1687_24028.nosynth);
          uvar_subtyping = (uu___1687_24028.uvar_subtyping);
          tc_term = (uu___1687_24028.tc_term);
          type_of = (uu___1687_24028.type_of);
          universe_of = (uu___1687_24028.universe_of);
          check_type_of = (uu___1687_24028.check_type_of);
          use_bv_sorts = (uu___1687_24028.use_bv_sorts);
          qtbl_name_and_index = (uu___1687_24028.qtbl_name_and_index);
          normalized_eff_names = (uu___1687_24028.normalized_eff_names);
          fv_delta_depths = (uu___1687_24028.fv_delta_depths);
          proof_ns = (uu___1687_24028.proof_ns);
          synth_hook = (uu___1687_24028.synth_hook);
          try_solve_implicits_hook =
            (uu___1687_24028.try_solve_implicits_hook);
          splice = (uu___1687_24028.splice);
          mpreprocess = (uu___1687_24028.mpreprocess);
          postprocess = (uu___1687_24028.postprocess);
          identifier_info = (uu___1687_24028.identifier_info);
          tc_hooks = (uu___1687_24028.tc_hooks);
          dsenv = (uu___1687_24028.dsenv);
          nbe = (uu___1687_24028.nbe);
          strict_args_tab = (uu___1687_24028.strict_args_tab);
          erasable_types_tab = (uu___1687_24028.erasable_types_tab)
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
    fun uu____24047  ->
      match uu____24047 with
      | (ed,quals) ->
          let effects1 =
            let uu___1696_24061 = env1.effects  in
            {
              decls = ((ed, quals) :: ((env1.effects).decls));
              order = (uu___1696_24061.order);
              joins = (uu___1696_24061.joins);
              polymonadic_binds = (uu___1696_24061.polymonadic_binds)
            }  in
          let uu___1699_24070 = env1  in
          {
            solver = (uu___1699_24070.solver);
            range = (uu___1699_24070.range);
            curmodule = (uu___1699_24070.curmodule);
            gamma = (uu___1699_24070.gamma);
            gamma_sig = (uu___1699_24070.gamma_sig);
            gamma_cache = (uu___1699_24070.gamma_cache);
            modules = (uu___1699_24070.modules);
            expected_typ = (uu___1699_24070.expected_typ);
            sigtab = (uu___1699_24070.sigtab);
            attrtab = (uu___1699_24070.attrtab);
            instantiate_imp = (uu___1699_24070.instantiate_imp);
            effects = effects1;
            generalize = (uu___1699_24070.generalize);
            letrecs = (uu___1699_24070.letrecs);
            top_level = (uu___1699_24070.top_level);
            check_uvars = (uu___1699_24070.check_uvars);
            use_eq = (uu___1699_24070.use_eq);
            use_eq_strict = (uu___1699_24070.use_eq_strict);
            is_iface = (uu___1699_24070.is_iface);
            admit = (uu___1699_24070.admit);
            lax = (uu___1699_24070.lax);
            lax_universes = (uu___1699_24070.lax_universes);
            phase1 = (uu___1699_24070.phase1);
            failhard = (uu___1699_24070.failhard);
            nosynth = (uu___1699_24070.nosynth);
            uvar_subtyping = (uu___1699_24070.uvar_subtyping);
            tc_term = (uu___1699_24070.tc_term);
            type_of = (uu___1699_24070.type_of);
            universe_of = (uu___1699_24070.universe_of);
            check_type_of = (uu___1699_24070.check_type_of);
            use_bv_sorts = (uu___1699_24070.use_bv_sorts);
            qtbl_name_and_index = (uu___1699_24070.qtbl_name_and_index);
            normalized_eff_names = (uu___1699_24070.normalized_eff_names);
            fv_delta_depths = (uu___1699_24070.fv_delta_depths);
            proof_ns = (uu___1699_24070.proof_ns);
            synth_hook = (uu___1699_24070.synth_hook);
            try_solve_implicits_hook =
              (uu___1699_24070.try_solve_implicits_hook);
            splice = (uu___1699_24070.splice);
            mpreprocess = (uu___1699_24070.mpreprocess);
            postprocess = (uu___1699_24070.postprocess);
            identifier_info = (uu___1699_24070.identifier_info);
            tc_hooks = (uu___1699_24070.tc_hooks);
            dsenv = (uu___1699_24070.dsenv);
            nbe = (uu___1699_24070.nbe);
            strict_args_tab = (uu___1699_24070.strict_args_tab);
            erasable_types_tab = (uu___1699_24070.erasable_types_tab)
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
        let uu____24099 =
          FStar_All.pipe_right (env1.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24167  ->
                  match uu____24167 with
                  | (m1,n1,uu____24185,uu____24186) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n n1)))
           in
        match uu____24099 with
        | FStar_Pervasives_Native.Some (uu____24211,uu____24212,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24257 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env1  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env2 c =
                let uu____24332 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env2)  in
                FStar_All.pipe_right uu____24332
                  (fun uu____24353  ->
                     match uu____24353 with
                     | (c1,g1) ->
                         let uu____24364 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env2)
                            in
                         FStar_All.pipe_right uu____24364
                           (fun uu____24385  ->
                              match uu____24385 with
                              | (c2,g2) ->
                                  let uu____24396 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24396)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24518 = l1 u t e  in
                              l2 u t uu____24518))
                | uu____24519 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24587  ->
                    match uu____24587 with
                    | (e,uu____24595) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24618 =
            match uu____24618 with
            | (i,j) ->
                let uu____24629 = FStar_Ident.lid_equals i j  in
                if uu____24629
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun uu____24636  ->
                       FStar_Pervasives_Native.Some uu____24636)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24665 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24675 = FStar_Ident.lid_equals i k  in
                        if uu____24675
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24689 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24689
                                  then []
                                  else
                                    (let uu____24696 =
                                       let uu____24705 =
                                         find_edge order1 (i, k)  in
                                       let uu____24708 =
                                         find_edge order1 (k, j)  in
                                       (uu____24705, uu____24708)  in
                                     match uu____24696 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24723 =
                                           compose_edges e1 e2  in
                                         [uu____24723]
                                     | uu____24724 -> [])))))
                 in
              FStar_List.append order1 uu____24665  in
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
                  let uu____24754 =
                    (FStar_Ident.lid_equals edge2.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24757 =
                         lookup_effect_quals env1 edge2.mtarget  in
                       FStar_All.pipe_right uu____24757
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24754
                  then
                    let uu____24764 =
                      let uu____24770 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge2.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24770)
                       in
                    let uu____24774 = get_range env1  in
                    FStar_Errors.raise_error uu____24764 uu____24774
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____24852 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24852
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24904 =
                                             let uu____24913 =
                                               find_edge order2 (i, k)  in
                                             let uu____24916 =
                                               find_edge order2 (j, k)  in
                                             (uu____24913, uu____24916)  in
                                           match uu____24904 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____24958,uu____24959)
                                                    ->
                                                    let uu____24966 =
                                                      let uu____24973 =
                                                        let uu____24975 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24975
                                                         in
                                                      let uu____24978 =
                                                        let uu____24980 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24980
                                                         in
                                                      (uu____24973,
                                                        uu____24978)
                                                       in
                                                    (match uu____24966 with
                                                     | (true ,true ) ->
                                                         let uu____24997 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____24997
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
                                           | uu____25040 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25092 =
                                   let uu____25094 =
                                     exists_polymonadic_bind env1 i j  in
                                   FStar_All.pipe_right uu____25094
                                     FStar_Util.is_some
                                    in
                                 if uu____25092
                                 then
                                   let uu____25143 =
                                     let uu____25149 =
                                       let uu____25151 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25153 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25155 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25157 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25151 uu____25153 uu____25155
                                         uu____25157
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25149)
                                      in
                                   FStar_Errors.raise_error uu____25143
                                     env1.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects1 =
             let uu___1820_25196 = env1.effects  in
             {
               decls = (uu___1820_25196.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1820_25196.polymonadic_binds)
             }  in
           let uu___1823_25197 = env1  in
           {
             solver = (uu___1823_25197.solver);
             range = (uu___1823_25197.range);
             curmodule = (uu___1823_25197.curmodule);
             gamma = (uu___1823_25197.gamma);
             gamma_sig = (uu___1823_25197.gamma_sig);
             gamma_cache = (uu___1823_25197.gamma_cache);
             modules = (uu___1823_25197.modules);
             expected_typ = (uu___1823_25197.expected_typ);
             sigtab = (uu___1823_25197.sigtab);
             attrtab = (uu___1823_25197.attrtab);
             instantiate_imp = (uu___1823_25197.instantiate_imp);
             effects = effects1;
             generalize = (uu___1823_25197.generalize);
             letrecs = (uu___1823_25197.letrecs);
             top_level = (uu___1823_25197.top_level);
             check_uvars = (uu___1823_25197.check_uvars);
             use_eq = (uu___1823_25197.use_eq);
             use_eq_strict = (uu___1823_25197.use_eq_strict);
             is_iface = (uu___1823_25197.is_iface);
             admit = (uu___1823_25197.admit);
             lax = (uu___1823_25197.lax);
             lax_universes = (uu___1823_25197.lax_universes);
             phase1 = (uu___1823_25197.phase1);
             failhard = (uu___1823_25197.failhard);
             nosynth = (uu___1823_25197.nosynth);
             uvar_subtyping = (uu___1823_25197.uvar_subtyping);
             tc_term = (uu___1823_25197.tc_term);
             type_of = (uu___1823_25197.type_of);
             universe_of = (uu___1823_25197.universe_of);
             check_type_of = (uu___1823_25197.check_type_of);
             use_bv_sorts = (uu___1823_25197.use_bv_sorts);
             qtbl_name_and_index = (uu___1823_25197.qtbl_name_and_index);
             normalized_eff_names = (uu___1823_25197.normalized_eff_names);
             fv_delta_depths = (uu___1823_25197.fv_delta_depths);
             proof_ns = (uu___1823_25197.proof_ns);
             synth_hook = (uu___1823_25197.synth_hook);
             try_solve_implicits_hook =
               (uu___1823_25197.try_solve_implicits_hook);
             splice = (uu___1823_25197.splice);
             mpreprocess = (uu___1823_25197.mpreprocess);
             postprocess = (uu___1823_25197.postprocess);
             identifier_info = (uu___1823_25197.identifier_info);
             tc_hooks = (uu___1823_25197.tc_hooks);
             dsenv = (uu___1823_25197.dsenv);
             nbe = (uu___1823_25197.nbe);
             strict_args_tab = (uu___1823_25197.strict_args_tab);
             erasable_types_tab = (uu___1823_25197.erasable_types_tab)
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
              let uu____25245 = FStar_Ident.string_of_lid m  in
              let uu____25247 = FStar_Ident.string_of_lid n  in
              let uu____25249 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25245 uu____25247 uu____25249
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25258 =
              let uu____25260 = exists_polymonadic_bind env1 m n  in
              FStar_All.pipe_right uu____25260 FStar_Util.is_some  in
            if uu____25258
            then
              let uu____25297 =
                let uu____25303 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25303)
                 in
              FStar_Errors.raise_error uu____25297 env1.range
            else
              (let uu____25309 =
                 let uu____25311 = join_opt env1 m n  in
                 FStar_All.pipe_right uu____25311 FStar_Util.is_some  in
               if uu____25309
               then
                 let uu____25336 =
                   let uu____25342 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25342)
                    in
                 FStar_Errors.raise_error uu____25336 env1.range
               else
                 (let uu___1838_25348 = env1  in
                  {
                    solver = (uu___1838_25348.solver);
                    range = (uu___1838_25348.range);
                    curmodule = (uu___1838_25348.curmodule);
                    gamma = (uu___1838_25348.gamma);
                    gamma_sig = (uu___1838_25348.gamma_sig);
                    gamma_cache = (uu___1838_25348.gamma_cache);
                    modules = (uu___1838_25348.modules);
                    expected_typ = (uu___1838_25348.expected_typ);
                    sigtab = (uu___1838_25348.sigtab);
                    attrtab = (uu___1838_25348.attrtab);
                    instantiate_imp = (uu___1838_25348.instantiate_imp);
                    effects =
                      (let uu___1840_25350 = env1.effects  in
                       {
                         decls = (uu___1840_25350.decls);
                         order = (uu___1840_25350.order);
                         joins = (uu___1840_25350.joins);
                         polymonadic_binds = ((m, n, p, ty) ::
                           ((env1.effects).polymonadic_binds))
                       });
                    generalize = (uu___1838_25348.generalize);
                    letrecs = (uu___1838_25348.letrecs);
                    top_level = (uu___1838_25348.top_level);
                    check_uvars = (uu___1838_25348.check_uvars);
                    use_eq = (uu___1838_25348.use_eq);
                    use_eq_strict = (uu___1838_25348.use_eq_strict);
                    is_iface = (uu___1838_25348.is_iface);
                    admit = (uu___1838_25348.admit);
                    lax = (uu___1838_25348.lax);
                    lax_universes = (uu___1838_25348.lax_universes);
                    phase1 = (uu___1838_25348.phase1);
                    failhard = (uu___1838_25348.failhard);
                    nosynth = (uu___1838_25348.nosynth);
                    uvar_subtyping = (uu___1838_25348.uvar_subtyping);
                    tc_term = (uu___1838_25348.tc_term);
                    type_of = (uu___1838_25348.type_of);
                    universe_of = (uu___1838_25348.universe_of);
                    check_type_of = (uu___1838_25348.check_type_of);
                    use_bv_sorts = (uu___1838_25348.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1838_25348.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1838_25348.normalized_eff_names);
                    fv_delta_depths = (uu___1838_25348.fv_delta_depths);
                    proof_ns = (uu___1838_25348.proof_ns);
                    synth_hook = (uu___1838_25348.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1838_25348.try_solve_implicits_hook);
                    splice = (uu___1838_25348.splice);
                    mpreprocess = (uu___1838_25348.mpreprocess);
                    postprocess = (uu___1838_25348.postprocess);
                    identifier_info = (uu___1838_25348.identifier_info);
                    tc_hooks = (uu___1838_25348.tc_hooks);
                    dsenv = (uu___1838_25348.dsenv);
                    nbe = (uu___1838_25348.nbe);
                    strict_args_tab = (uu___1838_25348.strict_args_tab);
                    erasable_types_tab = (uu___1838_25348.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env1  ->
    fun b  ->
      let uu___1844_25422 = env1  in
      {
        solver = (uu___1844_25422.solver);
        range = (uu___1844_25422.range);
        curmodule = (uu___1844_25422.curmodule);
        gamma = (b :: (env1.gamma));
        gamma_sig = (uu___1844_25422.gamma_sig);
        gamma_cache = (uu___1844_25422.gamma_cache);
        modules = (uu___1844_25422.modules);
        expected_typ = (uu___1844_25422.expected_typ);
        sigtab = (uu___1844_25422.sigtab);
        attrtab = (uu___1844_25422.attrtab);
        instantiate_imp = (uu___1844_25422.instantiate_imp);
        effects = (uu___1844_25422.effects);
        generalize = (uu___1844_25422.generalize);
        letrecs = (uu___1844_25422.letrecs);
        top_level = (uu___1844_25422.top_level);
        check_uvars = (uu___1844_25422.check_uvars);
        use_eq = (uu___1844_25422.use_eq);
        use_eq_strict = (uu___1844_25422.use_eq_strict);
        is_iface = (uu___1844_25422.is_iface);
        admit = (uu___1844_25422.admit);
        lax = (uu___1844_25422.lax);
        lax_universes = (uu___1844_25422.lax_universes);
        phase1 = (uu___1844_25422.phase1);
        failhard = (uu___1844_25422.failhard);
        nosynth = (uu___1844_25422.nosynth);
        uvar_subtyping = (uu___1844_25422.uvar_subtyping);
        tc_term = (uu___1844_25422.tc_term);
        type_of = (uu___1844_25422.type_of);
        universe_of = (uu___1844_25422.universe_of);
        check_type_of = (uu___1844_25422.check_type_of);
        use_bv_sorts = (uu___1844_25422.use_bv_sorts);
        qtbl_name_and_index = (uu___1844_25422.qtbl_name_and_index);
        normalized_eff_names = (uu___1844_25422.normalized_eff_names);
        fv_delta_depths = (uu___1844_25422.fv_delta_depths);
        proof_ns = (uu___1844_25422.proof_ns);
        synth_hook = (uu___1844_25422.synth_hook);
        try_solve_implicits_hook = (uu___1844_25422.try_solve_implicits_hook);
        splice = (uu___1844_25422.splice);
        mpreprocess = (uu___1844_25422.mpreprocess);
        postprocess = (uu___1844_25422.postprocess);
        identifier_info = (uu___1844_25422.identifier_info);
        tc_hooks = (uu___1844_25422.tc_hooks);
        dsenv = (uu___1844_25422.dsenv);
        nbe = (uu___1844_25422.nbe);
        strict_args_tab = (uu___1844_25422.strict_args_tab);
        erasable_types_tab = (uu___1844_25422.erasable_types_tab)
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
            (let uu___1857_25480 = env1  in
             {
               solver = (uu___1857_25480.solver);
               range = (uu___1857_25480.range);
               curmodule = (uu___1857_25480.curmodule);
               gamma = rest;
               gamma_sig = (uu___1857_25480.gamma_sig);
               gamma_cache = (uu___1857_25480.gamma_cache);
               modules = (uu___1857_25480.modules);
               expected_typ = (uu___1857_25480.expected_typ);
               sigtab = (uu___1857_25480.sigtab);
               attrtab = (uu___1857_25480.attrtab);
               instantiate_imp = (uu___1857_25480.instantiate_imp);
               effects = (uu___1857_25480.effects);
               generalize = (uu___1857_25480.generalize);
               letrecs = (uu___1857_25480.letrecs);
               top_level = (uu___1857_25480.top_level);
               check_uvars = (uu___1857_25480.check_uvars);
               use_eq = (uu___1857_25480.use_eq);
               use_eq_strict = (uu___1857_25480.use_eq_strict);
               is_iface = (uu___1857_25480.is_iface);
               admit = (uu___1857_25480.admit);
               lax = (uu___1857_25480.lax);
               lax_universes = (uu___1857_25480.lax_universes);
               phase1 = (uu___1857_25480.phase1);
               failhard = (uu___1857_25480.failhard);
               nosynth = (uu___1857_25480.nosynth);
               uvar_subtyping = (uu___1857_25480.uvar_subtyping);
               tc_term = (uu___1857_25480.tc_term);
               type_of = (uu___1857_25480.type_of);
               universe_of = (uu___1857_25480.universe_of);
               check_type_of = (uu___1857_25480.check_type_of);
               use_bv_sorts = (uu___1857_25480.use_bv_sorts);
               qtbl_name_and_index = (uu___1857_25480.qtbl_name_and_index);
               normalized_eff_names = (uu___1857_25480.normalized_eff_names);
               fv_delta_depths = (uu___1857_25480.fv_delta_depths);
               proof_ns = (uu___1857_25480.proof_ns);
               synth_hook = (uu___1857_25480.synth_hook);
               try_solve_implicits_hook =
                 (uu___1857_25480.try_solve_implicits_hook);
               splice = (uu___1857_25480.splice);
               mpreprocess = (uu___1857_25480.mpreprocess);
               postprocess = (uu___1857_25480.postprocess);
               identifier_info = (uu___1857_25480.identifier_info);
               tc_hooks = (uu___1857_25480.tc_hooks);
               dsenv = (uu___1857_25480.dsenv);
               nbe = (uu___1857_25480.nbe);
               strict_args_tab = (uu___1857_25480.strict_args_tab);
               erasable_types_tab = (uu___1857_25480.erasable_types_tab)
             }))
    | uu____25481 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env1  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env2  ->
           fun uu____25510  ->
             match uu____25510 with | (x,uu____25518) -> push_bv env2 x) env1
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
            let uu___1871_25553 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1871_25553.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1871_25553.FStar_Syntax_Syntax.index);
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
        let uu____25626 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25626 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env1 univ_vars  in
            let uu____25654 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25654)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env1  ->
    fun t  ->
      let uu___1892_25670 = env1  in
      {
        solver = (uu___1892_25670.solver);
        range = (uu___1892_25670.range);
        curmodule = (uu___1892_25670.curmodule);
        gamma = (uu___1892_25670.gamma);
        gamma_sig = (uu___1892_25670.gamma_sig);
        gamma_cache = (uu___1892_25670.gamma_cache);
        modules = (uu___1892_25670.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1892_25670.sigtab);
        attrtab = (uu___1892_25670.attrtab);
        instantiate_imp = (uu___1892_25670.instantiate_imp);
        effects = (uu___1892_25670.effects);
        generalize = (uu___1892_25670.generalize);
        letrecs = (uu___1892_25670.letrecs);
        top_level = (uu___1892_25670.top_level);
        check_uvars = (uu___1892_25670.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1892_25670.use_eq_strict);
        is_iface = (uu___1892_25670.is_iface);
        admit = (uu___1892_25670.admit);
        lax = (uu___1892_25670.lax);
        lax_universes = (uu___1892_25670.lax_universes);
        phase1 = (uu___1892_25670.phase1);
        failhard = (uu___1892_25670.failhard);
        nosynth = (uu___1892_25670.nosynth);
        uvar_subtyping = (uu___1892_25670.uvar_subtyping);
        tc_term = (uu___1892_25670.tc_term);
        type_of = (uu___1892_25670.type_of);
        universe_of = (uu___1892_25670.universe_of);
        check_type_of = (uu___1892_25670.check_type_of);
        use_bv_sorts = (uu___1892_25670.use_bv_sorts);
        qtbl_name_and_index = (uu___1892_25670.qtbl_name_and_index);
        normalized_eff_names = (uu___1892_25670.normalized_eff_names);
        fv_delta_depths = (uu___1892_25670.fv_delta_depths);
        proof_ns = (uu___1892_25670.proof_ns);
        synth_hook = (uu___1892_25670.synth_hook);
        try_solve_implicits_hook = (uu___1892_25670.try_solve_implicits_hook);
        splice = (uu___1892_25670.splice);
        mpreprocess = (uu___1892_25670.mpreprocess);
        postprocess = (uu___1892_25670.postprocess);
        identifier_info = (uu___1892_25670.identifier_info);
        tc_hooks = (uu___1892_25670.tc_hooks);
        dsenv = (uu___1892_25670.dsenv);
        nbe = (uu___1892_25670.nbe);
        strict_args_tab = (uu___1892_25670.strict_args_tab);
        erasable_types_tab = (uu___1892_25670.erasable_types_tab)
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
    let uu____25701 = expected_typ env_  in
    ((let uu___1899_25707 = env_  in
      {
        solver = (uu___1899_25707.solver);
        range = (uu___1899_25707.range);
        curmodule = (uu___1899_25707.curmodule);
        gamma = (uu___1899_25707.gamma);
        gamma_sig = (uu___1899_25707.gamma_sig);
        gamma_cache = (uu___1899_25707.gamma_cache);
        modules = (uu___1899_25707.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1899_25707.sigtab);
        attrtab = (uu___1899_25707.attrtab);
        instantiate_imp = (uu___1899_25707.instantiate_imp);
        effects = (uu___1899_25707.effects);
        generalize = (uu___1899_25707.generalize);
        letrecs = (uu___1899_25707.letrecs);
        top_level = (uu___1899_25707.top_level);
        check_uvars = (uu___1899_25707.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1899_25707.use_eq_strict);
        is_iface = (uu___1899_25707.is_iface);
        admit = (uu___1899_25707.admit);
        lax = (uu___1899_25707.lax);
        lax_universes = (uu___1899_25707.lax_universes);
        phase1 = (uu___1899_25707.phase1);
        failhard = (uu___1899_25707.failhard);
        nosynth = (uu___1899_25707.nosynth);
        uvar_subtyping = (uu___1899_25707.uvar_subtyping);
        tc_term = (uu___1899_25707.tc_term);
        type_of = (uu___1899_25707.type_of);
        universe_of = (uu___1899_25707.universe_of);
        check_type_of = (uu___1899_25707.check_type_of);
        use_bv_sorts = (uu___1899_25707.use_bv_sorts);
        qtbl_name_and_index = (uu___1899_25707.qtbl_name_and_index);
        normalized_eff_names = (uu___1899_25707.normalized_eff_names);
        fv_delta_depths = (uu___1899_25707.fv_delta_depths);
        proof_ns = (uu___1899_25707.proof_ns);
        synth_hook = (uu___1899_25707.synth_hook);
        try_solve_implicits_hook = (uu___1899_25707.try_solve_implicits_hook);
        splice = (uu___1899_25707.splice);
        mpreprocess = (uu___1899_25707.mpreprocess);
        postprocess = (uu___1899_25707.postprocess);
        identifier_info = (uu___1899_25707.identifier_info);
        tc_hooks = (uu___1899_25707.tc_hooks);
        dsenv = (uu___1899_25707.dsenv);
        nbe = (uu___1899_25707.nbe);
        strict_args_tab = (uu___1899_25707.strict_args_tab);
        erasable_types_tab = (uu___1899_25707.erasable_types_tab)
      }), uu____25701)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25719 =
      let uu____25722 = FStar_Ident.id_of_text ""  in [uu____25722]  in
    FStar_Ident.lid_of_ids uu____25719  in
  fun env1  ->
    fun m  ->
      let sigs =
        let uu____25729 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25729
        then
          let uu____25734 =
            FStar_All.pipe_right env1.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25734 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env1 sigs;
      (let uu___1907_25762 = env1  in
       {
         solver = (uu___1907_25762.solver);
         range = (uu___1907_25762.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1907_25762.gamma_cache);
         modules = (m :: (env1.modules));
         expected_typ = (uu___1907_25762.expected_typ);
         sigtab = (uu___1907_25762.sigtab);
         attrtab = (uu___1907_25762.attrtab);
         instantiate_imp = (uu___1907_25762.instantiate_imp);
         effects = (uu___1907_25762.effects);
         generalize = (uu___1907_25762.generalize);
         letrecs = (uu___1907_25762.letrecs);
         top_level = (uu___1907_25762.top_level);
         check_uvars = (uu___1907_25762.check_uvars);
         use_eq = (uu___1907_25762.use_eq);
         use_eq_strict = (uu___1907_25762.use_eq_strict);
         is_iface = (uu___1907_25762.is_iface);
         admit = (uu___1907_25762.admit);
         lax = (uu___1907_25762.lax);
         lax_universes = (uu___1907_25762.lax_universes);
         phase1 = (uu___1907_25762.phase1);
         failhard = (uu___1907_25762.failhard);
         nosynth = (uu___1907_25762.nosynth);
         uvar_subtyping = (uu___1907_25762.uvar_subtyping);
         tc_term = (uu___1907_25762.tc_term);
         type_of = (uu___1907_25762.type_of);
         universe_of = (uu___1907_25762.universe_of);
         check_type_of = (uu___1907_25762.check_type_of);
         use_bv_sorts = (uu___1907_25762.use_bv_sorts);
         qtbl_name_and_index = (uu___1907_25762.qtbl_name_and_index);
         normalized_eff_names = (uu___1907_25762.normalized_eff_names);
         fv_delta_depths = (uu___1907_25762.fv_delta_depths);
         proof_ns = (uu___1907_25762.proof_ns);
         synth_hook = (uu___1907_25762.synth_hook);
         try_solve_implicits_hook =
           (uu___1907_25762.try_solve_implicits_hook);
         splice = (uu___1907_25762.splice);
         mpreprocess = (uu___1907_25762.mpreprocess);
         postprocess = (uu___1907_25762.postprocess);
         identifier_info = (uu___1907_25762.identifier_info);
         tc_hooks = (uu___1907_25762.tc_hooks);
         dsenv = (uu___1907_25762.dsenv);
         nbe = (uu___1907_25762.nbe);
         strict_args_tab = (uu___1907_25762.strict_args_tab);
         erasable_types_tab = (uu___1907_25762.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env1  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25814)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____25818,(uu____25819,t)))::tl
          ->
          let uu____25840 =
            let uu____25843 = FStar_Syntax_Free.uvars t  in
            ext out uu____25843  in
          aux uu____25840 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25846;
            FStar_Syntax_Syntax.index = uu____25847;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____25855 =
            let uu____25858 = FStar_Syntax_Free.uvars t  in
            ext out uu____25858  in
          aux uu____25855 tl
       in
    aux no_uvs env1.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env1  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25916)::tl -> aux out tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____25920,(uu____25921,t)))::tl
          ->
          let uu____25942 =
            let uu____25945 = FStar_Syntax_Free.univs t  in
            ext out uu____25945  in
          aux uu____25942 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25948;
            FStar_Syntax_Syntax.index = uu____25949;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____25957 =
            let uu____25960 = FStar_Syntax_Free.univs t  in
            ext out uu____25960  in
          aux uu____25957 tl
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
          let uu____26022 = FStar_Util.set_add uname out  in
          aux uu____26022 tl
      | (FStar_Syntax_Syntax.Binding_lid (uu____26025,(uu____26026,t)))::tl
          ->
          let uu____26047 =
            let uu____26050 = FStar_Syntax_Free.univnames t  in
            ext out uu____26050  in
          aux uu____26047 tl
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26053;
            FStar_Syntax_Syntax.index = uu____26054;
            FStar_Syntax_Syntax.sort = t;_})::tl
          ->
          let uu____26062 =
            let uu____26065 = FStar_Syntax_Free.univnames t  in
            ext out uu____26065  in
          aux uu____26062 tl
       in
    aux no_univ_names env1.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26086  ->
            match uu___12_26086 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26090 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26103 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26114 =
      let uu____26123 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26123
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26114 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env1  -> bound_vars_of_bindings env1.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env1  -> binders_of_bindings env1.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26171 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26184  ->
              match uu___13_26184 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26187 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26187
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26193) ->
                  let uu____26210 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26210))
       in
    FStar_All.pipe_right uu____26171 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26224  ->
    match uu___14_26224 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26230 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26230
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env1  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env1.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env1)
      (fun uu____26253  ->
         fun v  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env1  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26308) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26341,uu____26342) -> false  in
      let uu____26356 =
        FStar_List.tryFind
          (fun uu____26378  ->
             match uu____26378 with | (p,uu____26389) -> str_i_prefix p path)
          env1.proof_ns
         in
      match uu____26356 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26408,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env1  ->
    fun lid  ->
      let uu____26438 = FStar_Ident.path_of_lid lid  in
      should_enc_path env1 uu____26438
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2050_26460 = e  in
        {
          solver = (uu___2050_26460.solver);
          range = (uu___2050_26460.range);
          curmodule = (uu___2050_26460.curmodule);
          gamma = (uu___2050_26460.gamma);
          gamma_sig = (uu___2050_26460.gamma_sig);
          gamma_cache = (uu___2050_26460.gamma_cache);
          modules = (uu___2050_26460.modules);
          expected_typ = (uu___2050_26460.expected_typ);
          sigtab = (uu___2050_26460.sigtab);
          attrtab = (uu___2050_26460.attrtab);
          instantiate_imp = (uu___2050_26460.instantiate_imp);
          effects = (uu___2050_26460.effects);
          generalize = (uu___2050_26460.generalize);
          letrecs = (uu___2050_26460.letrecs);
          top_level = (uu___2050_26460.top_level);
          check_uvars = (uu___2050_26460.check_uvars);
          use_eq = (uu___2050_26460.use_eq);
          use_eq_strict = (uu___2050_26460.use_eq_strict);
          is_iface = (uu___2050_26460.is_iface);
          admit = (uu___2050_26460.admit);
          lax = (uu___2050_26460.lax);
          lax_universes = (uu___2050_26460.lax_universes);
          phase1 = (uu___2050_26460.phase1);
          failhard = (uu___2050_26460.failhard);
          nosynth = (uu___2050_26460.nosynth);
          uvar_subtyping = (uu___2050_26460.uvar_subtyping);
          tc_term = (uu___2050_26460.tc_term);
          type_of = (uu___2050_26460.type_of);
          universe_of = (uu___2050_26460.universe_of);
          check_type_of = (uu___2050_26460.check_type_of);
          use_bv_sorts = (uu___2050_26460.use_bv_sorts);
          qtbl_name_and_index = (uu___2050_26460.qtbl_name_and_index);
          normalized_eff_names = (uu___2050_26460.normalized_eff_names);
          fv_delta_depths = (uu___2050_26460.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2050_26460.synth_hook);
          try_solve_implicits_hook =
            (uu___2050_26460.try_solve_implicits_hook);
          splice = (uu___2050_26460.splice);
          mpreprocess = (uu___2050_26460.mpreprocess);
          postprocess = (uu___2050_26460.postprocess);
          identifier_info = (uu___2050_26460.identifier_info);
          tc_hooks = (uu___2050_26460.tc_hooks);
          dsenv = (uu___2050_26460.dsenv);
          nbe = (uu___2050_26460.nbe);
          strict_args_tab = (uu___2050_26460.strict_args_tab);
          erasable_types_tab = (uu___2050_26460.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2059_26508 = e  in
      {
        solver = (uu___2059_26508.solver);
        range = (uu___2059_26508.range);
        curmodule = (uu___2059_26508.curmodule);
        gamma = (uu___2059_26508.gamma);
        gamma_sig = (uu___2059_26508.gamma_sig);
        gamma_cache = (uu___2059_26508.gamma_cache);
        modules = (uu___2059_26508.modules);
        expected_typ = (uu___2059_26508.expected_typ);
        sigtab = (uu___2059_26508.sigtab);
        attrtab = (uu___2059_26508.attrtab);
        instantiate_imp = (uu___2059_26508.instantiate_imp);
        effects = (uu___2059_26508.effects);
        generalize = (uu___2059_26508.generalize);
        letrecs = (uu___2059_26508.letrecs);
        top_level = (uu___2059_26508.top_level);
        check_uvars = (uu___2059_26508.check_uvars);
        use_eq = (uu___2059_26508.use_eq);
        use_eq_strict = (uu___2059_26508.use_eq_strict);
        is_iface = (uu___2059_26508.is_iface);
        admit = (uu___2059_26508.admit);
        lax = (uu___2059_26508.lax);
        lax_universes = (uu___2059_26508.lax_universes);
        phase1 = (uu___2059_26508.phase1);
        failhard = (uu___2059_26508.failhard);
        nosynth = (uu___2059_26508.nosynth);
        uvar_subtyping = (uu___2059_26508.uvar_subtyping);
        tc_term = (uu___2059_26508.tc_term);
        type_of = (uu___2059_26508.type_of);
        universe_of = (uu___2059_26508.universe_of);
        check_type_of = (uu___2059_26508.check_type_of);
        use_bv_sorts = (uu___2059_26508.use_bv_sorts);
        qtbl_name_and_index = (uu___2059_26508.qtbl_name_and_index);
        normalized_eff_names = (uu___2059_26508.normalized_eff_names);
        fv_delta_depths = (uu___2059_26508.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2059_26508.synth_hook);
        try_solve_implicits_hook = (uu___2059_26508.try_solve_implicits_hook);
        splice = (uu___2059_26508.splice);
        mpreprocess = (uu___2059_26508.mpreprocess);
        postprocess = (uu___2059_26508.postprocess);
        identifier_info = (uu___2059_26508.identifier_info);
        tc_hooks = (uu___2059_26508.tc_hooks);
        dsenv = (uu___2059_26508.dsenv);
        nbe = (uu___2059_26508.nbe);
        strict_args_tab = (uu___2059_26508.strict_args_tab);
        erasable_types_tab = (uu___2059_26508.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26524 = FStar_Syntax_Free.names t  in
      let uu____26527 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26524 uu____26527
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26550 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26550
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26560 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26560
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env1  ->
    let aux uu____26581 =
      match uu____26581 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26601 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26601)
       in
    let uu____26609 =
      let uu____26613 = FStar_List.map aux env1.proof_ns  in
      FStar_All.pipe_right uu____26613 FStar_List.rev  in
    FStar_All.pipe_right uu____26609 (FStar_String.concat " ")
  
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
                  (let uu____26681 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26681 with
                   | FStar_Pervasives_Native.Some uu____26685 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26688 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26698;
        FStar_TypeChecker_Common.univ_ineqs = uu____26699;
        FStar_TypeChecker_Common.implicits = uu____26700;_} -> true
    | uu____26710 -> false
  
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
          let uu___2103_26732 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2103_26732.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2103_26732.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2103_26732.FStar_TypeChecker_Common.implicits)
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
          let uu____26771 = FStar_Options.defensive ()  in
          if uu____26771
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26777 =
              let uu____26779 =
                let uu____26781 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26781  in
              Prims.op_Negation uu____26779  in
            (if uu____26777
             then
               let uu____26788 =
                 let uu____26794 =
                   let uu____26796 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26798 =
                     let uu____26800 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26800
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26796 uu____26798
                    in
                 (FStar_Errors.Warning_Defensive, uu____26794)  in
               FStar_Errors.log_issue rng uu____26788
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
          let uu____26840 =
            let uu____26842 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26842  in
          if uu____26840
          then ()
          else
            (let uu____26847 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26847 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26873 =
            let uu____26875 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26875  in
          if uu____26873
          then ()
          else
            (let uu____26880 = bound_vars e  in
             def_check_closed_in rng msg uu____26880 t)
  
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
          let uu___2140_26919 = g  in
          let uu____26920 =
            let uu____26921 =
              let uu____26922 =
                let uu____26929 =
                  let uu____26930 =
                    let uu____26947 =
                      let uu____26958 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____26958]  in
                    (f, uu____26947)  in
                  FStar_Syntax_Syntax.Tm_app uu____26930  in
                FStar_Syntax_Syntax.mk uu____26929  in
              uu____26922 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun uu____26995  ->
                 FStar_TypeChecker_Common.NonTrivial uu____26995) uu____26921
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____26920;
            FStar_TypeChecker_Common.deferred =
              (uu___2140_26919.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2140_26919.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2140_26919.FStar_TypeChecker_Common.implicits)
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
          let uu___2147_27013 = g  in
          let uu____27014 =
            let uu____27015 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27015  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27014;
            FStar_TypeChecker_Common.deferred =
              (uu___2147_27013.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2147_27013.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2147_27013.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2152_27032 = g  in
          let uu____27033 =
            let uu____27034 = map FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27034  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27033;
            FStar_TypeChecker_Common.deferred =
              (uu___2152_27032.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2152_27032.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2152_27032.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2156_27036 = g  in
          let uu____27037 =
            let uu____27038 = map f  in
            FStar_TypeChecker_Common.NonTrivial uu____27038  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27037;
            FStar_TypeChecker_Common.deferred =
              (uu___2156_27036.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2156_27036.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2156_27036.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27045 ->
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
                       let uu____27122 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27122
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2179_27129 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2179_27129.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2179_27129.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2179_27129.FStar_TypeChecker_Common.implicits)
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
               let uu____27163 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27163
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
            let uu___2194_27190 = g  in
            let uu____27191 =
              let uu____27192 = close_forall env1 binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27192  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27191;
              FStar_TypeChecker_Common.deferred =
                (uu___2194_27190.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2194_27190.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2194_27190.FStar_TypeChecker_Common.implicits)
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
              let uu____27250 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27250 with
              | FStar_Pervasives_Native.Some
                  (uu____27275::(tm,uu____27277)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27341 ->
                  let binders = all_binders env1  in
                  let gamma = env1.gamma  in
                  let ctx_uvar =
                    let uu____27359 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27359;
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
                    (let uu____27391 =
                       debug env1 (FStar_Options.Other "ImplicitTrace")  in
                     if uu____27391
                     then
                       let uu____27395 =
                         FStar_Syntax_Print.uvar_to_string
                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                          in
                       FStar_Util.print1
                         "Just created uvar for implicit {%s}\n" uu____27395
                     else ());
                    (let g =
                       let uu___2218_27401 = trivial_guard  in
                       {
                         FStar_TypeChecker_Common.guard_f =
                           (uu___2218_27401.FStar_TypeChecker_Common.guard_f);
                         FStar_TypeChecker_Common.deferred =
                           (uu___2218_27401.FStar_TypeChecker_Common.deferred);
                         FStar_TypeChecker_Common.univ_ineqs =
                           (uu___2218_27401.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27455 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27512  ->
                      fun b  ->
                        match uu____27512 with
                        | (substs1,uvars,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27554 =
                              let uu____27567 = reason b  in
                              new_implicit_var_aux uu____27567 r env1 sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27554 with
                             | (t,uu____27584,g_t) ->
                                 let uu____27598 =
                                   let uu____27601 =
                                     let uu____27604 =
                                       let uu____27605 =
                                         let uu____27612 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27612, t)  in
                                       FStar_Syntax_Syntax.NT uu____27605  in
                                     [uu____27604]  in
                                   FStar_List.append substs1 uu____27601  in
                                 let uu____27623 = conj_guard g g_t  in
                                 (uu____27598, (FStar_List.append uvars [t]),
                                   uu____27623))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27455
              (fun uu____27652  ->
                 match uu____27652 with | (uu____27669,uvars,g) -> (uvars, g))
  
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
                let uu____27710 =
                  lookup_definition [NoDelta] env1
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____27710 FStar_Util.must  in
              let uu____27727 = inst_tscheme_with post_ts [u]  in
              match uu____27727 with
              | (uu____27732,post) ->
                  let uu____27734 =
                    let uu____27739 =
                      let uu____27740 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____27740]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____27739  in
                  uu____27734 FStar_Pervasives_Native.None r
               in
            let uu____27773 =
              let uu____27778 =
                let uu____27779 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____27779]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____27778  in
            uu____27773 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____27815  -> ());
    push = (fun uu____27817  -> ());
    pop = (fun uu____27820  -> ());
    snapshot =
      (fun uu____27823  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____27842  -> fun uu____27843  -> ());
    encode_sig = (fun uu____27858  -> fun uu____27859  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____27865 =
             let uu____27872 = FStar_Options.peek ()  in (e, g, uu____27872)
              in
           [uu____27865]);
    solve = (fun uu____27888  -> fun uu____27889  -> fun uu____27890  -> ());
    finish = (fun uu____27897  -> ());
    refresh = (fun uu____27899  -> ())
  } 