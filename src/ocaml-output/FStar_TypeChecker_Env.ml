open Prims
type step =
  | Beta 
  | Iota 
  | Zeta 
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
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____139 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____157 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____168 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____179 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____190 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____201 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____212 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____224 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____245 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____272 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____299 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____323 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____334 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____345 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____356 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____367 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____378 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____389 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____400 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____411 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____422 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____433 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____444 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____455 -> false
  
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1  ->
    fun s2  ->
      match (s1, s2) with
      | (Beta ,Beta ) -> true
      | (Iota ,Iota ) -> true
      | (Zeta ,Zeta ) -> true
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
      | uu____515 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____541 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____552 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____563 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____575 -> false
  
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
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
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
    match projectee with | { msource; mtarget; mlift;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mlift
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> tc_term
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> universe_of
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} ->
        qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} ->
        normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} ->
        try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> splice1
  
let (__proj__Mkenv__item__mpreprocess :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> mpreprocess
  
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
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} ->
        is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> dsenv
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; mpreprocess;
        postprocess; is_native_tactic; identifier_info; tc_hooks; dsenv;
        nbe = nbe1; strict_args_tab; erasable_types_tab;_} ->
        erasable_types_tab
  
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> init1
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> push1
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> pop1
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> snapshot1
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
        unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> rollback1
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> finish1
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> refresh
  
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
  = fun env  -> fun tau  -> fun tm  -> env.mpreprocess env tau tm 
let (postprocess :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  -> fun tau  -> fun ty  -> fun tm  -> env.postprocess env tau ty tm 
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___0_14008  ->
              match uu___0_14008 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____14011 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____14011  in
                  let uu____14012 =
                    let uu____14013 = FStar_Syntax_Subst.compress y  in
                    uu____14013.FStar_Syntax_Syntax.n  in
                  (match uu____14012 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____14017 =
                         let uu___321_14018 = y1  in
                         let uu____14019 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___321_14018.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___321_14018.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____14019
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____14017
                   | uu____14022 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___327_14036 = env  in
      let uu____14037 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___327_14036.solver);
        range = (uu___327_14036.range);
        curmodule = (uu___327_14036.curmodule);
        gamma = uu____14037;
        gamma_sig = (uu___327_14036.gamma_sig);
        gamma_cache = (uu___327_14036.gamma_cache);
        modules = (uu___327_14036.modules);
        expected_typ = (uu___327_14036.expected_typ);
        sigtab = (uu___327_14036.sigtab);
        attrtab = (uu___327_14036.attrtab);
        instantiate_imp = (uu___327_14036.instantiate_imp);
        effects = (uu___327_14036.effects);
        generalize = (uu___327_14036.generalize);
        letrecs = (uu___327_14036.letrecs);
        top_level = (uu___327_14036.top_level);
        check_uvars = (uu___327_14036.check_uvars);
        use_eq = (uu___327_14036.use_eq);
        is_iface = (uu___327_14036.is_iface);
        admit = (uu___327_14036.admit);
        lax = (uu___327_14036.lax);
        lax_universes = (uu___327_14036.lax_universes);
        phase1 = (uu___327_14036.phase1);
        failhard = (uu___327_14036.failhard);
        nosynth = (uu___327_14036.nosynth);
        uvar_subtyping = (uu___327_14036.uvar_subtyping);
        tc_term = (uu___327_14036.tc_term);
        type_of = (uu___327_14036.type_of);
        universe_of = (uu___327_14036.universe_of);
        check_type_of = (uu___327_14036.check_type_of);
        use_bv_sorts = (uu___327_14036.use_bv_sorts);
        qtbl_name_and_index = (uu___327_14036.qtbl_name_and_index);
        normalized_eff_names = (uu___327_14036.normalized_eff_names);
        fv_delta_depths = (uu___327_14036.fv_delta_depths);
        proof_ns = (uu___327_14036.proof_ns);
        synth_hook = (uu___327_14036.synth_hook);
        try_solve_implicits_hook = (uu___327_14036.try_solve_implicits_hook);
        splice = (uu___327_14036.splice);
        mpreprocess = (uu___327_14036.mpreprocess);
        postprocess = (uu___327_14036.postprocess);
        is_native_tactic = (uu___327_14036.is_native_tactic);
        identifier_info = (uu___327_14036.identifier_info);
        tc_hooks = (uu___327_14036.tc_hooks);
        dsenv = (uu___327_14036.dsenv);
        nbe = (uu___327_14036.nbe);
        strict_args_tab = (uu___327_14036.strict_args_tab);
        erasable_types_tab = (uu___327_14036.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____14045  -> fun uu____14046  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___334_14068 = env  in
      {
        solver = (uu___334_14068.solver);
        range = (uu___334_14068.range);
        curmodule = (uu___334_14068.curmodule);
        gamma = (uu___334_14068.gamma);
        gamma_sig = (uu___334_14068.gamma_sig);
        gamma_cache = (uu___334_14068.gamma_cache);
        modules = (uu___334_14068.modules);
        expected_typ = (uu___334_14068.expected_typ);
        sigtab = (uu___334_14068.sigtab);
        attrtab = (uu___334_14068.attrtab);
        instantiate_imp = (uu___334_14068.instantiate_imp);
        effects = (uu___334_14068.effects);
        generalize = (uu___334_14068.generalize);
        letrecs = (uu___334_14068.letrecs);
        top_level = (uu___334_14068.top_level);
        check_uvars = (uu___334_14068.check_uvars);
        use_eq = (uu___334_14068.use_eq);
        is_iface = (uu___334_14068.is_iface);
        admit = (uu___334_14068.admit);
        lax = (uu___334_14068.lax);
        lax_universes = (uu___334_14068.lax_universes);
        phase1 = (uu___334_14068.phase1);
        failhard = (uu___334_14068.failhard);
        nosynth = (uu___334_14068.nosynth);
        uvar_subtyping = (uu___334_14068.uvar_subtyping);
        tc_term = (uu___334_14068.tc_term);
        type_of = (uu___334_14068.type_of);
        universe_of = (uu___334_14068.universe_of);
        check_type_of = (uu___334_14068.check_type_of);
        use_bv_sorts = (uu___334_14068.use_bv_sorts);
        qtbl_name_and_index = (uu___334_14068.qtbl_name_and_index);
        normalized_eff_names = (uu___334_14068.normalized_eff_names);
        fv_delta_depths = (uu___334_14068.fv_delta_depths);
        proof_ns = (uu___334_14068.proof_ns);
        synth_hook = (uu___334_14068.synth_hook);
        try_solve_implicits_hook = (uu___334_14068.try_solve_implicits_hook);
        splice = (uu___334_14068.splice);
        mpreprocess = (uu___334_14068.mpreprocess);
        postprocess = (uu___334_14068.postprocess);
        is_native_tactic = (uu___334_14068.is_native_tactic);
        identifier_info = (uu___334_14068.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___334_14068.dsenv);
        nbe = (uu___334_14068.nbe);
        strict_args_tab = (uu___334_14068.strict_args_tab);
        erasable_types_tab = (uu___334_14068.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___338_14080 = e  in
      let uu____14081 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___338_14080.solver);
        range = (uu___338_14080.range);
        curmodule = (uu___338_14080.curmodule);
        gamma = (uu___338_14080.gamma);
        gamma_sig = (uu___338_14080.gamma_sig);
        gamma_cache = (uu___338_14080.gamma_cache);
        modules = (uu___338_14080.modules);
        expected_typ = (uu___338_14080.expected_typ);
        sigtab = (uu___338_14080.sigtab);
        attrtab = (uu___338_14080.attrtab);
        instantiate_imp = (uu___338_14080.instantiate_imp);
        effects = (uu___338_14080.effects);
        generalize = (uu___338_14080.generalize);
        letrecs = (uu___338_14080.letrecs);
        top_level = (uu___338_14080.top_level);
        check_uvars = (uu___338_14080.check_uvars);
        use_eq = (uu___338_14080.use_eq);
        is_iface = (uu___338_14080.is_iface);
        admit = (uu___338_14080.admit);
        lax = (uu___338_14080.lax);
        lax_universes = (uu___338_14080.lax_universes);
        phase1 = (uu___338_14080.phase1);
        failhard = (uu___338_14080.failhard);
        nosynth = (uu___338_14080.nosynth);
        uvar_subtyping = (uu___338_14080.uvar_subtyping);
        tc_term = (uu___338_14080.tc_term);
        type_of = (uu___338_14080.type_of);
        universe_of = (uu___338_14080.universe_of);
        check_type_of = (uu___338_14080.check_type_of);
        use_bv_sorts = (uu___338_14080.use_bv_sorts);
        qtbl_name_and_index = (uu___338_14080.qtbl_name_and_index);
        normalized_eff_names = (uu___338_14080.normalized_eff_names);
        fv_delta_depths = (uu___338_14080.fv_delta_depths);
        proof_ns = (uu___338_14080.proof_ns);
        synth_hook = (uu___338_14080.synth_hook);
        try_solve_implicits_hook = (uu___338_14080.try_solve_implicits_hook);
        splice = (uu___338_14080.splice);
        mpreprocess = (uu___338_14080.mpreprocess);
        postprocess = (uu___338_14080.postprocess);
        is_native_tactic = (uu___338_14080.is_native_tactic);
        identifier_info = (uu___338_14080.identifier_info);
        tc_hooks = (uu___338_14080.tc_hooks);
        dsenv = uu____14081;
        nbe = (uu___338_14080.nbe);
        strict_args_tab = (uu___338_14080.strict_args_tab);
        erasable_types_tab = (uu___338_14080.erasable_types_tab)
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e  -> FStar_Syntax_DsEnv.dep_graph e.dsenv 
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____14110) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____14113,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____14115,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____14118 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____14132 . unit -> 'Auu____14132 FStar_Util.smap =
  fun uu____14139  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____14145 . unit -> 'Auu____14145 FStar_Util.smap =
  fun uu____14152  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                fun nbe1  ->
                  let uu____14290 = new_gamma_cache ()  in
                  let uu____14293 = new_sigtab ()  in
                  let uu____14296 = new_sigtab ()  in
                  let uu____14303 =
                    let uu____14318 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____14318, FStar_Pervasives_Native.None)  in
                  let uu____14339 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14343 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14347 = FStar_Options.using_facts_from ()  in
                  let uu____14348 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14351 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14352 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14366 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____14290;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____14293;
                    attrtab = uu____14296;
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
                    qtbl_name_and_index = uu____14303;
                    normalized_eff_names = uu____14339;
                    fv_delta_depths = uu____14343;
                    proof_ns = uu____14347;
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
                    is_native_tactic = (fun uu____14480  -> false);
                    identifier_info = uu____14348;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14351;
                    nbe = nbe1;
                    strict_args_tab = uu____14352;
                    erasable_types_tab = uu____14366
                  }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env  -> env.attrtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____14559  ->
    let uu____14560 = FStar_ST.op_Bang query_indices  in
    match uu____14560 with
    | [] -> failwith "Empty query indices!"
    | uu____14615 ->
        let uu____14625 =
          let uu____14635 =
            let uu____14643 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14643  in
          let uu____14697 = FStar_ST.op_Bang query_indices  in uu____14635 ::
            uu____14697
           in
        FStar_ST.op_Colon_Equals query_indices uu____14625
  
let (pop_query_indices : unit -> unit) =
  fun uu____14793  ->
    let uu____14794 = FStar_ST.op_Bang query_indices  in
    match uu____14794 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14921  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14958  ->
    match uu____14958 with
    | (l,n1) ->
        let uu____14968 = FStar_ST.op_Bang query_indices  in
        (match uu____14968 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____15090 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____15113  ->
    let uu____15114 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____15114
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____15182 =
       let uu____15185 = FStar_ST.op_Bang stack  in env :: uu____15185  in
     FStar_ST.op_Colon_Equals stack uu____15182);
    (let uu___412_15234 = env  in
     let uu____15235 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____15238 = FStar_Util.smap_copy (sigtab env)  in
     let uu____15241 = FStar_Util.smap_copy (attrtab env)  in
     let uu____15248 =
       let uu____15263 =
         let uu____15267 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____15267  in
       let uu____15299 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____15263, uu____15299)  in
     let uu____15348 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____15351 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____15354 =
       let uu____15357 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____15357  in
     let uu____15377 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15390 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___412_15234.solver);
       range = (uu___412_15234.range);
       curmodule = (uu___412_15234.curmodule);
       gamma = (uu___412_15234.gamma);
       gamma_sig = (uu___412_15234.gamma_sig);
       gamma_cache = uu____15235;
       modules = (uu___412_15234.modules);
       expected_typ = (uu___412_15234.expected_typ);
       sigtab = uu____15238;
       attrtab = uu____15241;
       instantiate_imp = (uu___412_15234.instantiate_imp);
       effects = (uu___412_15234.effects);
       generalize = (uu___412_15234.generalize);
       letrecs = (uu___412_15234.letrecs);
       top_level = (uu___412_15234.top_level);
       check_uvars = (uu___412_15234.check_uvars);
       use_eq = (uu___412_15234.use_eq);
       is_iface = (uu___412_15234.is_iface);
       admit = (uu___412_15234.admit);
       lax = (uu___412_15234.lax);
       lax_universes = (uu___412_15234.lax_universes);
       phase1 = (uu___412_15234.phase1);
       failhard = (uu___412_15234.failhard);
       nosynth = (uu___412_15234.nosynth);
       uvar_subtyping = (uu___412_15234.uvar_subtyping);
       tc_term = (uu___412_15234.tc_term);
       type_of = (uu___412_15234.type_of);
       universe_of = (uu___412_15234.universe_of);
       check_type_of = (uu___412_15234.check_type_of);
       use_bv_sorts = (uu___412_15234.use_bv_sorts);
       qtbl_name_and_index = uu____15248;
       normalized_eff_names = uu____15348;
       fv_delta_depths = uu____15351;
       proof_ns = (uu___412_15234.proof_ns);
       synth_hook = (uu___412_15234.synth_hook);
       try_solve_implicits_hook = (uu___412_15234.try_solve_implicits_hook);
       splice = (uu___412_15234.splice);
       mpreprocess = (uu___412_15234.mpreprocess);
       postprocess = (uu___412_15234.postprocess);
       is_native_tactic = (uu___412_15234.is_native_tactic);
       identifier_info = uu____15354;
       tc_hooks = (uu___412_15234.tc_hooks);
       dsenv = (uu___412_15234.dsenv);
       nbe = (uu___412_15234.nbe);
       strict_args_tab = uu____15377;
       erasable_types_tab = uu____15390
     })
  
let (pop_stack : unit -> env) =
  fun uu____15400  ->
    let uu____15401 = FStar_ST.op_Bang stack  in
    match uu____15401 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15455 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15545  ->
           let uu____15546 = snapshot_stack env  in
           match uu____15546 with
           | (stack_depth,env1) ->
               let uu____15580 = snapshot_query_indices ()  in
               (match uu____15580 with
                | (query_indices_depth,()) ->
                    let uu____15613 = (env1.solver).snapshot msg  in
                    (match uu____15613 with
                     | (solver_depth,()) ->
                         let uu____15670 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____15670 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___437_15737 = env1  in
                                 {
                                   solver = (uu___437_15737.solver);
                                   range = (uu___437_15737.range);
                                   curmodule = (uu___437_15737.curmodule);
                                   gamma = (uu___437_15737.gamma);
                                   gamma_sig = (uu___437_15737.gamma_sig);
                                   gamma_cache = (uu___437_15737.gamma_cache);
                                   modules = (uu___437_15737.modules);
                                   expected_typ =
                                     (uu___437_15737.expected_typ);
                                   sigtab = (uu___437_15737.sigtab);
                                   attrtab = (uu___437_15737.attrtab);
                                   instantiate_imp =
                                     (uu___437_15737.instantiate_imp);
                                   effects = (uu___437_15737.effects);
                                   generalize = (uu___437_15737.generalize);
                                   letrecs = (uu___437_15737.letrecs);
                                   top_level = (uu___437_15737.top_level);
                                   check_uvars = (uu___437_15737.check_uvars);
                                   use_eq = (uu___437_15737.use_eq);
                                   is_iface = (uu___437_15737.is_iface);
                                   admit = (uu___437_15737.admit);
                                   lax = (uu___437_15737.lax);
                                   lax_universes =
                                     (uu___437_15737.lax_universes);
                                   phase1 = (uu___437_15737.phase1);
                                   failhard = (uu___437_15737.failhard);
                                   nosynth = (uu___437_15737.nosynth);
                                   uvar_subtyping =
                                     (uu___437_15737.uvar_subtyping);
                                   tc_term = (uu___437_15737.tc_term);
                                   type_of = (uu___437_15737.type_of);
                                   universe_of = (uu___437_15737.universe_of);
                                   check_type_of =
                                     (uu___437_15737.check_type_of);
                                   use_bv_sorts =
                                     (uu___437_15737.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___437_15737.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___437_15737.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___437_15737.fv_delta_depths);
                                   proof_ns = (uu___437_15737.proof_ns);
                                   synth_hook = (uu___437_15737.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___437_15737.try_solve_implicits_hook);
                                   splice = (uu___437_15737.splice);
                                   mpreprocess = (uu___437_15737.mpreprocess);
                                   postprocess = (uu___437_15737.postprocess);
                                   is_native_tactic =
                                     (uu___437_15737.is_native_tactic);
                                   identifier_info =
                                     (uu___437_15737.identifier_info);
                                   tc_hooks = (uu___437_15737.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___437_15737.nbe);
                                   strict_args_tab =
                                     (uu___437_15737.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___437_15737.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15771  ->
             let uu____15772 =
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
             match uu____15772 with
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
                             ((let uu____15952 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15952
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15968 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15968
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____16000,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____16042 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____16072  ->
                  match uu____16072 with
                  | (m,uu____16080) -> FStar_Ident.lid_equals l m))
           in
        (match uu____16042 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___482_16095 = env  in
               {
                 solver = (uu___482_16095.solver);
                 range = (uu___482_16095.range);
                 curmodule = (uu___482_16095.curmodule);
                 gamma = (uu___482_16095.gamma);
                 gamma_sig = (uu___482_16095.gamma_sig);
                 gamma_cache = (uu___482_16095.gamma_cache);
                 modules = (uu___482_16095.modules);
                 expected_typ = (uu___482_16095.expected_typ);
                 sigtab = (uu___482_16095.sigtab);
                 attrtab = (uu___482_16095.attrtab);
                 instantiate_imp = (uu___482_16095.instantiate_imp);
                 effects = (uu___482_16095.effects);
                 generalize = (uu___482_16095.generalize);
                 letrecs = (uu___482_16095.letrecs);
                 top_level = (uu___482_16095.top_level);
                 check_uvars = (uu___482_16095.check_uvars);
                 use_eq = (uu___482_16095.use_eq);
                 is_iface = (uu___482_16095.is_iface);
                 admit = (uu___482_16095.admit);
                 lax = (uu___482_16095.lax);
                 lax_universes = (uu___482_16095.lax_universes);
                 phase1 = (uu___482_16095.phase1);
                 failhard = (uu___482_16095.failhard);
                 nosynth = (uu___482_16095.nosynth);
                 uvar_subtyping = (uu___482_16095.uvar_subtyping);
                 tc_term = (uu___482_16095.tc_term);
                 type_of = (uu___482_16095.type_of);
                 universe_of = (uu___482_16095.universe_of);
                 check_type_of = (uu___482_16095.check_type_of);
                 use_bv_sorts = (uu___482_16095.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___482_16095.normalized_eff_names);
                 fv_delta_depths = (uu___482_16095.fv_delta_depths);
                 proof_ns = (uu___482_16095.proof_ns);
                 synth_hook = (uu___482_16095.synth_hook);
                 try_solve_implicits_hook =
                   (uu___482_16095.try_solve_implicits_hook);
                 splice = (uu___482_16095.splice);
                 mpreprocess = (uu___482_16095.mpreprocess);
                 postprocess = (uu___482_16095.postprocess);
                 is_native_tactic = (uu___482_16095.is_native_tactic);
                 identifier_info = (uu___482_16095.identifier_info);
                 tc_hooks = (uu___482_16095.tc_hooks);
                 dsenv = (uu___482_16095.dsenv);
                 nbe = (uu___482_16095.nbe);
                 strict_args_tab = (uu___482_16095.strict_args_tab);
                 erasable_types_tab = (uu___482_16095.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____16112,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___491_16128 = env  in
               {
                 solver = (uu___491_16128.solver);
                 range = (uu___491_16128.range);
                 curmodule = (uu___491_16128.curmodule);
                 gamma = (uu___491_16128.gamma);
                 gamma_sig = (uu___491_16128.gamma_sig);
                 gamma_cache = (uu___491_16128.gamma_cache);
                 modules = (uu___491_16128.modules);
                 expected_typ = (uu___491_16128.expected_typ);
                 sigtab = (uu___491_16128.sigtab);
                 attrtab = (uu___491_16128.attrtab);
                 instantiate_imp = (uu___491_16128.instantiate_imp);
                 effects = (uu___491_16128.effects);
                 generalize = (uu___491_16128.generalize);
                 letrecs = (uu___491_16128.letrecs);
                 top_level = (uu___491_16128.top_level);
                 check_uvars = (uu___491_16128.check_uvars);
                 use_eq = (uu___491_16128.use_eq);
                 is_iface = (uu___491_16128.is_iface);
                 admit = (uu___491_16128.admit);
                 lax = (uu___491_16128.lax);
                 lax_universes = (uu___491_16128.lax_universes);
                 phase1 = (uu___491_16128.phase1);
                 failhard = (uu___491_16128.failhard);
                 nosynth = (uu___491_16128.nosynth);
                 uvar_subtyping = (uu___491_16128.uvar_subtyping);
                 tc_term = (uu___491_16128.tc_term);
                 type_of = (uu___491_16128.type_of);
                 universe_of = (uu___491_16128.universe_of);
                 check_type_of = (uu___491_16128.check_type_of);
                 use_bv_sorts = (uu___491_16128.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___491_16128.normalized_eff_names);
                 fv_delta_depths = (uu___491_16128.fv_delta_depths);
                 proof_ns = (uu___491_16128.proof_ns);
                 synth_hook = (uu___491_16128.synth_hook);
                 try_solve_implicits_hook =
                   (uu___491_16128.try_solve_implicits_hook);
                 splice = (uu___491_16128.splice);
                 mpreprocess = (uu___491_16128.mpreprocess);
                 postprocess = (uu___491_16128.postprocess);
                 is_native_tactic = (uu___491_16128.is_native_tactic);
                 identifier_info = (uu___491_16128.identifier_info);
                 tc_hooks = (uu___491_16128.tc_hooks);
                 dsenv = (uu___491_16128.dsenv);
                 nbe = (uu___491_16128.nbe);
                 strict_args_tab = (uu___491_16128.strict_args_tab);
                 erasable_types_tab = (uu___491_16128.erasable_types_tab)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___498_16171 = e  in
         {
           solver = (uu___498_16171.solver);
           range = r;
           curmodule = (uu___498_16171.curmodule);
           gamma = (uu___498_16171.gamma);
           gamma_sig = (uu___498_16171.gamma_sig);
           gamma_cache = (uu___498_16171.gamma_cache);
           modules = (uu___498_16171.modules);
           expected_typ = (uu___498_16171.expected_typ);
           sigtab = (uu___498_16171.sigtab);
           attrtab = (uu___498_16171.attrtab);
           instantiate_imp = (uu___498_16171.instantiate_imp);
           effects = (uu___498_16171.effects);
           generalize = (uu___498_16171.generalize);
           letrecs = (uu___498_16171.letrecs);
           top_level = (uu___498_16171.top_level);
           check_uvars = (uu___498_16171.check_uvars);
           use_eq = (uu___498_16171.use_eq);
           is_iface = (uu___498_16171.is_iface);
           admit = (uu___498_16171.admit);
           lax = (uu___498_16171.lax);
           lax_universes = (uu___498_16171.lax_universes);
           phase1 = (uu___498_16171.phase1);
           failhard = (uu___498_16171.failhard);
           nosynth = (uu___498_16171.nosynth);
           uvar_subtyping = (uu___498_16171.uvar_subtyping);
           tc_term = (uu___498_16171.tc_term);
           type_of = (uu___498_16171.type_of);
           universe_of = (uu___498_16171.universe_of);
           check_type_of = (uu___498_16171.check_type_of);
           use_bv_sorts = (uu___498_16171.use_bv_sorts);
           qtbl_name_and_index = (uu___498_16171.qtbl_name_and_index);
           normalized_eff_names = (uu___498_16171.normalized_eff_names);
           fv_delta_depths = (uu___498_16171.fv_delta_depths);
           proof_ns = (uu___498_16171.proof_ns);
           synth_hook = (uu___498_16171.synth_hook);
           try_solve_implicits_hook =
             (uu___498_16171.try_solve_implicits_hook);
           splice = (uu___498_16171.splice);
           mpreprocess = (uu___498_16171.mpreprocess);
           postprocess = (uu___498_16171.postprocess);
           is_native_tactic = (uu___498_16171.is_native_tactic);
           identifier_info = (uu___498_16171.identifier_info);
           tc_hooks = (uu___498_16171.tc_hooks);
           dsenv = (uu___498_16171.dsenv);
           nbe = (uu___498_16171.nbe);
           strict_args_tab = (uu___498_16171.strict_args_tab);
           erasable_types_tab = (uu___498_16171.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____16191 =
        let uu____16192 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____16192 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16191
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____16247 =
          let uu____16248 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____16248 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16247
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____16303 =
          let uu____16304 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____16304 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____16303
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16359 =
        let uu____16360 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16360 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16359
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___515_16424 = env  in
      {
        solver = (uu___515_16424.solver);
        range = (uu___515_16424.range);
        curmodule = lid;
        gamma = (uu___515_16424.gamma);
        gamma_sig = (uu___515_16424.gamma_sig);
        gamma_cache = (uu___515_16424.gamma_cache);
        modules = (uu___515_16424.modules);
        expected_typ = (uu___515_16424.expected_typ);
        sigtab = (uu___515_16424.sigtab);
        attrtab = (uu___515_16424.attrtab);
        instantiate_imp = (uu___515_16424.instantiate_imp);
        effects = (uu___515_16424.effects);
        generalize = (uu___515_16424.generalize);
        letrecs = (uu___515_16424.letrecs);
        top_level = (uu___515_16424.top_level);
        check_uvars = (uu___515_16424.check_uvars);
        use_eq = (uu___515_16424.use_eq);
        is_iface = (uu___515_16424.is_iface);
        admit = (uu___515_16424.admit);
        lax = (uu___515_16424.lax);
        lax_universes = (uu___515_16424.lax_universes);
        phase1 = (uu___515_16424.phase1);
        failhard = (uu___515_16424.failhard);
        nosynth = (uu___515_16424.nosynth);
        uvar_subtyping = (uu___515_16424.uvar_subtyping);
        tc_term = (uu___515_16424.tc_term);
        type_of = (uu___515_16424.type_of);
        universe_of = (uu___515_16424.universe_of);
        check_type_of = (uu___515_16424.check_type_of);
        use_bv_sorts = (uu___515_16424.use_bv_sorts);
        qtbl_name_and_index = (uu___515_16424.qtbl_name_and_index);
        normalized_eff_names = (uu___515_16424.normalized_eff_names);
        fv_delta_depths = (uu___515_16424.fv_delta_depths);
        proof_ns = (uu___515_16424.proof_ns);
        synth_hook = (uu___515_16424.synth_hook);
        try_solve_implicits_hook = (uu___515_16424.try_solve_implicits_hook);
        splice = (uu___515_16424.splice);
        mpreprocess = (uu___515_16424.mpreprocess);
        postprocess = (uu___515_16424.postprocess);
        is_native_tactic = (uu___515_16424.is_native_tactic);
        identifier_info = (uu___515_16424.identifier_info);
        tc_hooks = (uu___515_16424.tc_hooks);
        dsenv = (uu___515_16424.dsenv);
        nbe = (uu___515_16424.nbe);
        strict_args_tab = (uu___515_16424.strict_args_tab);
        erasable_types_tab = (uu___515_16424.erasable_types_tab)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____16455 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16455
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16468 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16468)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16483 =
      let uu____16485 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16485  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16483)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16494  ->
    let uu____16495 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16495
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - Prims.int_one  in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____16595) ->
          let vs = mk_univ_subst formals us  in
          let uu____16619 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16619)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16636  ->
    match uu___1_16636 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16662  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16682 = inst_tscheme t  in
      match uu____16682 with
      | (us,t1) ->
          let uu____16693 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16693)
  
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
          let uu____16718 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16720 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16718 uu____16720
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
    fun env  ->
      fun ed  ->
        fun uu____16747  ->
          match uu____16747 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16761 =
                    let uu____16763 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16767 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16771 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16773 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16763 uu____16767 uu____16771 uu____16773
                     in
                  failwith uu____16761)
               else ();
               (let uu____16778 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16778))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16796 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16807 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16818 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
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
             | ([],uu____16866) -> Maybe
             | (uu____16873,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16893 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____16987 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16987 with
          | FStar_Pervasives_Native.None  ->
              let uu____17010 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_17054  ->
                     match uu___2_17054 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____17093 = FStar_Ident.lid_equals lid l  in
                         if uu____17093
                         then
                           let uu____17116 =
                             let uu____17135 =
                               let uu____17150 = inst_tscheme t  in
                               FStar_Util.Inl uu____17150  in
                             let uu____17165 = FStar_Ident.range_of_lid l  in
                             (uu____17135, uu____17165)  in
                           FStar_Pervasives_Native.Some uu____17116
                         else FStar_Pervasives_Native.None
                     | uu____17218 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____17010
                (fun uu____17256  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_17266  ->
                        match uu___3_17266 with
                        | (uu____17269,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____17271);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____17272;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____17273;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____17274;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____17275;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____17276;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____17298 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____17298
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
                                  uu____17350 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____17357 -> cache t  in
                            let uu____17358 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____17358 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17364 =
                                   let uu____17365 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17365)
                                    in
                                 maybe_cache uu____17364)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17436 = find_in_sigtab env lid  in
         match uu____17436 with
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
  fun env  ->
    fun lid  ->
      let uu____17517 = lookup_qname env lid  in
      match uu____17517 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17538,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17652 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17652 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____17697 =
          let uu____17700 = lookup_attr env1 attr  in se1 :: uu____17700  in
        FStar_Util.smap_add (attrtab env1) attr uu____17697  in
      FStar_List.iter
        (fun attr  ->
           let uu____17710 =
             let uu____17711 = FStar_Syntax_Subst.compress attr  in
             uu____17711.FStar_Syntax_Syntax.n  in
           match uu____17710 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17715 =
                 let uu____17717 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____17717.FStar_Ident.str  in
               add_one1 env se uu____17715
           | uu____17718 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17741) ->
          add_sigelts env ses
      | uu____17750 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se)

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ * FStar_Range.range)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___4_17788  ->
           match uu___4_17788 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17806 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17868,lb::[]),uu____17870) ->
            let uu____17879 =
              let uu____17888 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17897 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17888, uu____17897)  in
            FStar_Pervasives_Native.Some uu____17879
        | FStar_Syntax_Syntax.Sig_let ((uu____17910,lbs),uu____17912) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17944 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17957 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17957
                     then
                       let uu____17970 =
                         let uu____17979 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17988 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17979, uu____17988)  in
                       FStar_Pervasives_Native.Some uu____17970
                     else FStar_Pervasives_Native.None)
        | uu____18011 -> FStar_Pervasives_Native.None
  
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
                    let uu____18103 =
                      let uu____18105 =
                        let uu____18107 =
                          let uu____18109 =
                            let uu____18111 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____18117 =
                              let uu____18119 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____18119  in
                            Prims.op_Hat uu____18111 uu____18117  in
                          Prims.op_Hat ", expected " uu____18109  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____18107
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____18105
                       in
                    failwith uu____18103
                  else ());
             (let uu____18126 =
                let uu____18135 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____18135, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____18126))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____18155,uu____18156) ->
            let uu____18161 =
              let uu____18170 =
                let uu____18175 =
                  let uu____18176 =
                    let uu____18179 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____18179  in
                  (us, uu____18176)  in
                inst_ts us_opt uu____18175  in
              (uu____18170, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____18161
        | uu____18198 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____18287 =
          match uu____18287 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18383,uvs,t,uu____18386,uu____18387,uu____18388);
                      FStar_Syntax_Syntax.sigrng = uu____18389;
                      FStar_Syntax_Syntax.sigquals = uu____18390;
                      FStar_Syntax_Syntax.sigmeta = uu____18391;
                      FStar_Syntax_Syntax.sigattrs = uu____18392;
                      FStar_Syntax_Syntax.sigopts = uu____18393;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18418 =
                     let uu____18427 = inst_tscheme1 (uvs, t)  in
                     (uu____18427, rng)  in
                   FStar_Pervasives_Native.Some uu____18418
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18451;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18453;
                      FStar_Syntax_Syntax.sigattrs = uu____18454;
                      FStar_Syntax_Syntax.sigopts = uu____18455;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18474 =
                     let uu____18476 = in_cur_mod env l  in uu____18476 = Yes
                      in
                   if uu____18474
                   then
                     let uu____18488 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18488
                      then
                        let uu____18504 =
                          let uu____18513 = inst_tscheme1 (uvs, t)  in
                          (uu____18513, rng)  in
                        FStar_Pervasives_Native.Some uu____18504
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18546 =
                        let uu____18555 = inst_tscheme1 (uvs, t)  in
                        (uu____18555, rng)  in
                      FStar_Pervasives_Native.Some uu____18546)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18580,uu____18581);
                      FStar_Syntax_Syntax.sigrng = uu____18582;
                      FStar_Syntax_Syntax.sigquals = uu____18583;
                      FStar_Syntax_Syntax.sigmeta = uu____18584;
                      FStar_Syntax_Syntax.sigattrs = uu____18585;
                      FStar_Syntax_Syntax.sigopts = uu____18586;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18629 =
                          let uu____18638 = inst_tscheme1 (uvs, k)  in
                          (uu____18638, rng)  in
                        FStar_Pervasives_Native.Some uu____18629
                    | uu____18659 ->
                        let uu____18660 =
                          let uu____18669 =
                            let uu____18674 =
                              let uu____18675 =
                                let uu____18678 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18678
                                 in
                              (uvs, uu____18675)  in
                            inst_tscheme1 uu____18674  in
                          (uu____18669, rng)  in
                        FStar_Pervasives_Native.Some uu____18660)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18701,uu____18702);
                      FStar_Syntax_Syntax.sigrng = uu____18703;
                      FStar_Syntax_Syntax.sigquals = uu____18704;
                      FStar_Syntax_Syntax.sigmeta = uu____18705;
                      FStar_Syntax_Syntax.sigattrs = uu____18706;
                      FStar_Syntax_Syntax.sigopts = uu____18707;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18751 =
                          let uu____18760 = inst_tscheme_with (uvs, k) us  in
                          (uu____18760, rng)  in
                        FStar_Pervasives_Native.Some uu____18751
                    | uu____18781 ->
                        let uu____18782 =
                          let uu____18791 =
                            let uu____18796 =
                              let uu____18797 =
                                let uu____18800 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18800
                                 in
                              (uvs, uu____18797)  in
                            inst_tscheme_with uu____18796 us  in
                          (uu____18791, rng)  in
                        FStar_Pervasives_Native.Some uu____18782)
               | FStar_Util.Inr se ->
                   let uu____18836 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18857;
                          FStar_Syntax_Syntax.sigrng = uu____18858;
                          FStar_Syntax_Syntax.sigquals = uu____18859;
                          FStar_Syntax_Syntax.sigmeta = uu____18860;
                          FStar_Syntax_Syntax.sigattrs = uu____18861;
                          FStar_Syntax_Syntax.sigopts = uu____18862;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18879 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18836
                     (FStar_Util.map_option
                        (fun uu____18927  ->
                           match uu____18927 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18958 =
          let uu____18969 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18969 mapper  in
        match uu____18958 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____19043 =
              let uu____19054 =
                let uu____19061 =
                  let uu___852_19064 = t  in
                  let uu____19065 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___852_19064.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____19065;
                    FStar_Syntax_Syntax.vars =
                      (uu___852_19064.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____19061)  in
              (uu____19054, r)  in
            FStar_Pervasives_Native.Some uu____19043
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19114 = lookup_qname env l  in
      match uu____19114 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____19135 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____19189 = try_lookup_bv env bv  in
      match uu____19189 with
      | FStar_Pervasives_Native.None  ->
          let uu____19204 = variable_not_found bv  in
          FStar_Errors.raise_error uu____19204 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____19220 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____19221 =
            let uu____19222 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____19222  in
          (uu____19220, uu____19221)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____19244 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____19244 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____19310 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____19310  in
          let uu____19311 =
            let uu____19320 =
              let uu____19325 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____19325)  in
            (uu____19320, r1)  in
          FStar_Pervasives_Native.Some uu____19311
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ * FStar_Range.range)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____19360 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19360 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19393,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19418 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19418  in
            let uu____19419 =
              let uu____19424 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19424, r1)  in
            FStar_Pervasives_Native.Some uu____19419
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19448 = try_lookup_lid env l  in
      match uu____19448 with
      | FStar_Pervasives_Native.None  ->
          let uu____19475 = name_not_found l  in
          let uu____19481 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19475 uu____19481
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19524  ->
              match uu___5_19524 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19528 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19549 = lookup_qname env lid  in
      match uu____19549 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19558,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19561;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19563;
              FStar_Syntax_Syntax.sigattrs = uu____19564;
              FStar_Syntax_Syntax.sigopts = uu____19565;_},FStar_Pervasives_Native.None
            ),uu____19566)
          ->
          let uu____19617 =
            let uu____19624 =
              let uu____19625 =
                let uu____19628 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19628 t  in
              (uvs, uu____19625)  in
            (uu____19624, q)  in
          FStar_Pervasives_Native.Some uu____19617
      | uu____19641 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19663 = lookup_qname env lid  in
      match uu____19663 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19668,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19671;
              FStar_Syntax_Syntax.sigquals = uu____19672;
              FStar_Syntax_Syntax.sigmeta = uu____19673;
              FStar_Syntax_Syntax.sigattrs = uu____19674;
              FStar_Syntax_Syntax.sigopts = uu____19675;_},FStar_Pervasives_Native.None
            ),uu____19676)
          ->
          let uu____19727 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19727 (uvs, t)
      | uu____19732 ->
          let uu____19733 = name_not_found lid  in
          let uu____19739 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19733 uu____19739
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19759 = lookup_qname env lid  in
      match uu____19759 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19764,uvs,t,uu____19767,uu____19768,uu____19769);
              FStar_Syntax_Syntax.sigrng = uu____19770;
              FStar_Syntax_Syntax.sigquals = uu____19771;
              FStar_Syntax_Syntax.sigmeta = uu____19772;
              FStar_Syntax_Syntax.sigattrs = uu____19773;
              FStar_Syntax_Syntax.sigopts = uu____19774;_},FStar_Pervasives_Native.None
            ),uu____19775)
          ->
          let uu____19832 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19832 (uvs, t)
      | uu____19837 ->
          let uu____19838 = name_not_found lid  in
          let uu____19844 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19838 uu____19844
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19867 = lookup_qname env lid  in
      match uu____19867 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19875,uu____19876,uu____19877,uu____19878,uu____19879,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19881;
              FStar_Syntax_Syntax.sigquals = uu____19882;
              FStar_Syntax_Syntax.sigmeta = uu____19883;
              FStar_Syntax_Syntax.sigattrs = uu____19884;
              FStar_Syntax_Syntax.sigopts = uu____19885;_},uu____19886),uu____19887)
          -> (true, dcs)
      | uu____19952 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19968 = lookup_qname env lid  in
      match uu____19968 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19969,uu____19970,uu____19971,l,uu____19973,uu____19974);
              FStar_Syntax_Syntax.sigrng = uu____19975;
              FStar_Syntax_Syntax.sigquals = uu____19976;
              FStar_Syntax_Syntax.sigmeta = uu____19977;
              FStar_Syntax_Syntax.sigattrs = uu____19978;
              FStar_Syntax_Syntax.sigopts = uu____19979;_},uu____19980),uu____19981)
          -> l
      | uu____20040 ->
          let uu____20041 =
            let uu____20043 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____20043  in
          failwith uu____20041
  
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
        fun qninfo  ->
          let visible quals =
            FStar_All.pipe_right delta_levels
              (FStar_Util.for_some
                 (fun dl  ->
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some (visible_at dl))))
             in
          match qninfo with
          | FStar_Pervasives_Native.Some
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20113)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____20170) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____20194 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____20194
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____20229 -> FStar_Pervasives_Native.None)
          | uu____20238 -> FStar_Pervasives_Native.None
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        lookup_definition_qninfo_aux true delta_levels lid qninfo
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____20300 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____20300
  
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____20333 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____20333
  
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
             (FStar_Util.Inl uu____20385,uu____20386) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20435),uu____20436) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20485 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20503 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20513 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20530 ->
                  let uu____20537 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20537
              | FStar_Syntax_Syntax.Sig_let ((uu____20538,lbs),uu____20540)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20556 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20556
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____20563 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____20571 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20572 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20579 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20580 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20581 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20594 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20595 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20623 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20623
           (fun d_opt  ->
              let uu____20636 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20636
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20646 =
                   let uu____20649 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20649  in
                 match uu____20646 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20650 =
                       let uu____20652 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20652
                        in
                     failwith uu____20650
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20657 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20657
                       then
                         let uu____20660 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20662 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20664 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20660 uu____20662 uu____20664
                       else ());
                      FStar_Util.smap_add env.fv_delta_depths
                        lid.FStar_Ident.str d;
                      d))))
  
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20689),uu____20690) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20739 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20761),uu____20762) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20811 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20833 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20833
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20866 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20866 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20888 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20897 =
                        let uu____20898 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20898.FStar_Syntax_Syntax.n  in
                      match uu____20897 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20903 -> false))
               in
            (true, uu____20888)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20926 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20926
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
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
          let uu____20998 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20998.FStar_Ident.str  in
        let uu____20999 = FStar_Util.smap_try_find tab s  in
        match uu____20999 with
        | FStar_Pervasives_Native.None  ->
            let uu____21002 = f ()  in
            (match uu____21002 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____21040 =
        let uu____21041 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____21041 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____21075 =
        let uu____21076 = FStar_Syntax_Util.unrefine t  in
        uu____21076.FStar_Syntax_Syntax.n  in
      match uu____21075 with
      | FStar_Syntax_Syntax.Tm_type uu____21080 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____21084) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____21110) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____21115,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____21137 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____21170 =
        let attrs =
          let uu____21176 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____21176  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____21216 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____21216)
               in
            (true, res)
         in
      cache_in_fv_tab env.strict_args_tab fv f
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____21261 = lookup_qname env ftv  in
      match uu____21261 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____21265) ->
          let uu____21310 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____21310 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____21331,t),r) ->
               let uu____21346 =
                 let uu____21347 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____21347 t  in
               FStar_Pervasives_Native.Some uu____21346)
      | uu____21348 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____21360 = try_lookup_effect_lid env ftv  in
      match uu____21360 with
      | FStar_Pervasives_Native.None  ->
          let uu____21363 = name_not_found ftv  in
          let uu____21369 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____21363 uu____21369
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____21393 = lookup_qname env lid0  in
        match uu____21393 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21404);
                FStar_Syntax_Syntax.sigrng = uu____21405;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21407;
                FStar_Syntax_Syntax.sigattrs = uu____21408;
                FStar_Syntax_Syntax.sigopts = uu____21409;_},FStar_Pervasives_Native.None
              ),uu____21410)
            ->
            let lid1 =
              let uu____21466 =
                let uu____21467 = FStar_Ident.range_of_lid lid  in
                let uu____21468 =
                  let uu____21469 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21469  in
                FStar_Range.set_use_range uu____21467 uu____21468  in
              FStar_Ident.set_lid_range lid uu____21466  in
            let uu____21470 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21476  ->
                      match uu___6_21476 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21479 -> false))
               in
            if uu____21470
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21498 =
                      let uu____21500 =
                        let uu____21502 = get_range env  in
                        FStar_Range.string_of_range uu____21502  in
                      let uu____21503 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21505 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21500 uu____21503 uu____21505
                       in
                    failwith uu____21498)
                  in
               match (binders, univs1) with
               | ([],uu____21526) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21552,uu____21553::uu____21554::uu____21555) ->
                   let uu____21576 =
                     let uu____21578 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21580 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21578 uu____21580
                      in
                   failwith uu____21576
               | uu____21591 ->
                   let uu____21606 =
                     let uu____21611 =
                       let uu____21612 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21612)  in
                     inst_tscheme_with uu____21611 insts  in
                   (match uu____21606 with
                    | (uu____21625,t) ->
                        let t1 =
                          let uu____21628 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21628 t  in
                        let uu____21629 =
                          let uu____21630 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21630.FStar_Syntax_Syntax.n  in
                        (match uu____21629 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21665 -> failwith "Impossible")))
        | uu____21673 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____21697 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21697 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21710,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21717 = find1 l2  in
            (match uu____21717 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21724 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____21724 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21728 = find1 l  in
            (match uu____21728 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____21733 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21733
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21754 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____21754 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21760) ->
            FStar_List.length bs
        | uu____21799 ->
            let uu____21800 =
              let uu____21806 =
                let uu____21808 = FStar_Ident.string_of_lid name  in
                let uu____21810 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21808 uu____21810
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21806)
               in
            FStar_Errors.raise_error uu____21800 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21829 = lookup_qname env l1  in
      match uu____21829 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21832;
              FStar_Syntax_Syntax.sigrng = uu____21833;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21835;
              FStar_Syntax_Syntax.sigattrs = uu____21836;
              FStar_Syntax_Syntax.sigopts = uu____21837;_},uu____21838),uu____21839)
          -> q
      | uu____21892 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21916 =
          let uu____21917 =
            let uu____21919 = FStar_Util.string_of_int i  in
            let uu____21921 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21919 uu____21921
             in
          failwith uu____21917  in
        let uu____21924 = lookup_datacon env lid  in
        match uu____21924 with
        | (uu____21929,t) ->
            let uu____21931 =
              let uu____21932 = FStar_Syntax_Subst.compress t  in
              uu____21932.FStar_Syntax_Syntax.n  in
            (match uu____21931 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21936) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21980 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21980
                      FStar_Pervasives_Native.fst)
             | uu____21991 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22005 = lookup_qname env l  in
      match uu____22005 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____22007,uu____22008,uu____22009);
              FStar_Syntax_Syntax.sigrng = uu____22010;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22012;
              FStar_Syntax_Syntax.sigattrs = uu____22013;
              FStar_Syntax_Syntax.sigopts = uu____22014;_},uu____22015),uu____22016)
          ->
          FStar_Util.for_some
            (fun uu___7_22071  ->
               match uu___7_22071 with
               | FStar_Syntax_Syntax.Projector uu____22073 -> true
               | uu____22079 -> false) quals
      | uu____22081 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22095 = lookup_qname env lid  in
      match uu____22095 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____22097,uu____22098,uu____22099,uu____22100,uu____22101,uu____22102);
              FStar_Syntax_Syntax.sigrng = uu____22103;
              FStar_Syntax_Syntax.sigquals = uu____22104;
              FStar_Syntax_Syntax.sigmeta = uu____22105;
              FStar_Syntax_Syntax.sigattrs = uu____22106;
              FStar_Syntax_Syntax.sigopts = uu____22107;_},uu____22108),uu____22109)
          -> true
      | uu____22169 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22183 = lookup_qname env lid  in
      match uu____22183 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22185,uu____22186,uu____22187,uu____22188,uu____22189,uu____22190);
              FStar_Syntax_Syntax.sigrng = uu____22191;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____22193;
              FStar_Syntax_Syntax.sigattrs = uu____22194;
              FStar_Syntax_Syntax.sigopts = uu____22195;_},uu____22196),uu____22197)
          ->
          FStar_Util.for_some
            (fun uu___8_22260  ->
               match uu___8_22260 with
               | FStar_Syntax_Syntax.RecordType uu____22262 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____22272 -> true
               | uu____22282 -> false) quals
      | uu____22284 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____22294,uu____22295);
            FStar_Syntax_Syntax.sigrng = uu____22296;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____22298;
            FStar_Syntax_Syntax.sigattrs = uu____22299;
            FStar_Syntax_Syntax.sigopts = uu____22300;_},uu____22301),uu____22302)
        ->
        FStar_Util.for_some
          (fun uu___9_22361  ->
             match uu___9_22361 with
             | FStar_Syntax_Syntax.Action uu____22363 -> true
             | uu____22365 -> false) quals
    | uu____22367 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22381 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22381
  
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
  fun env  ->
    fun head1  ->
      let uu____22398 =
        let uu____22399 = FStar_Syntax_Util.un_uinst head1  in
        uu____22399.FStar_Syntax_Syntax.n  in
      match uu____22398 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22405 ->
               true
           | uu____22408 -> false)
      | uu____22410 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22424 = lookup_qname env l  in
      match uu____22424 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22427),uu____22428) ->
          FStar_Util.for_some
            (fun uu___10_22476  ->
               match uu___10_22476 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22479 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22481 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22557 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22575) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22593 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22601 ->
                 FStar_Pervasives_Native.Some true
             | uu____22620 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22623 =
        let uu____22627 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22627 mapper  in
      match uu____22623 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____22687 = lookup_qname env lid  in
      match uu____22687 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22691,uu____22692,tps,uu____22694,uu____22695,uu____22696);
              FStar_Syntax_Syntax.sigrng = uu____22697;
              FStar_Syntax_Syntax.sigquals = uu____22698;
              FStar_Syntax_Syntax.sigmeta = uu____22699;
              FStar_Syntax_Syntax.sigattrs = uu____22700;
              FStar_Syntax_Syntax.sigopts = uu____22701;_},uu____22702),uu____22703)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22771 -> FStar_Pervasives_Native.None
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____22817  ->
              match uu____22817 with
              | (d,uu____22826) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____22842 = effect_decl_opt env l  in
      match uu____22842 with
      | FStar_Pervasives_Native.None  ->
          let uu____22857 = name_not_found l  in
          let uu____22863 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22857 uu____22863
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22891 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____22891 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22898  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22912  ->
            fun uu____22913  -> fun e  -> FStar_Util.return_all e))
  } 
let (join_opt :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * mlift * mlift) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22947 = FStar_Ident.lid_equals l1 l2  in
        if uu____22947
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____22966 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22966
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____22985 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____23038  ->
                        match uu____23038 with
                        | (m1,m2,uu____23052,uu____23053,uu____23054) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22985 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____23079,uu____23080,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23128 = join_opt env l1 l2  in
        match uu____23128 with
        | FStar_Pervasives_Native.None  ->
            let uu____23149 =
              let uu____23155 =
                let uu____23157 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____23159 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____23157 uu____23159
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____23155)  in
            FStar_Errors.raise_error uu____23149 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____23202 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____23202
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'Auu____23222 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____23222) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____23251 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____23277  ->
                match uu____23277 with
                | (d,uu____23284) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____23251 with
      | FStar_Pervasives_Native.None  ->
          let uu____23295 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____23295
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____23310 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____23310 with
           | (uu____23321,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____23339)::(wp,uu____23341)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____23397 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____23462 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23475 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23475 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23492 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23492 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23517 =
                     let uu____23523 =
                       let uu____23525 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23533 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23544 =
                         let uu____23546 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23546  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23525 uu____23533 uu____23544
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23523)
                      in
                   FStar_Errors.raise_error uu____23517
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23554 =
                     let uu____23565 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23565 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23602  ->
                        fun uu____23603  ->
                          match (uu____23602, uu____23603) with
                          | ((x,uu____23633),(t,uu____23635)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23554
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23666 =
                     let uu___1606_23667 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1606_23667.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1606_23667.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1606_23667.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1606_23667.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23666
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23679 .
    'Auu____23679 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_res  ->
          let check_partial_application eff_name args =
            let r = get_range env  in
            let uu____23720 =
              let uu____23727 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____23727)  in
            match uu____23720 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23751 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23753 = FStar_Util.string_of_int given  in
                     let uu____23755 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23751 uu____23753 uu____23755
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23760 = effect_decl_opt env effect_name  in
          match uu____23760 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23782) ->
              let uu____23793 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23793 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23811 =
                       let uu____23814 = get_range env  in
                       let uu____23815 =
                         let uu____23822 =
                           let uu____23823 =
                             let uu____23840 =
                               let uu____23851 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23851 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23840)  in
                           FStar_Syntax_Syntax.Tm_app uu____23823  in
                         FStar_Syntax_Syntax.mk uu____23822  in
                       uu____23815 FStar_Pervasives_Native.None uu____23814
                        in
                     FStar_Pervasives_Native.Some uu____23811)))
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_res  -> effect_repr_aux false env c u_res 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_user_reflectable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_All.pipe_right quals
        (FStar_List.existsb
           (fun uu___11_23951  ->
              match uu___11_23951 with
              | FStar_Syntax_Syntax.Reflectable uu____23953 -> true
              | uu____23955 -> false))
  
let (is_total_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.TotalEffect quals
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      (is_user_reifiable_effect env effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
  
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____24015 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____24030 =
        let uu____24031 = FStar_Syntax_Subst.compress t  in
        uu____24031.FStar_Syntax_Syntax.n  in
      match uu____24030 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____24035,c) ->
          is_reifiable_comp env c
      | uu____24057 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____24077 =
           let uu____24079 = is_reifiable_effect env l  in
           Prims.op_Negation uu____24079  in
         if uu____24077
         then
           let uu____24082 =
             let uu____24088 =
               let uu____24090 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____24090
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____24088)  in
           let uu____24094 = get_range env  in
           FStar_Errors.raise_error uu____24082 uu____24094
         else ());
        (let uu____24097 = effect_repr_aux true env c u_c  in
         match uu____24097 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1683_24133 = env  in
        {
          solver = (uu___1683_24133.solver);
          range = (uu___1683_24133.range);
          curmodule = (uu___1683_24133.curmodule);
          gamma = (uu___1683_24133.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1683_24133.gamma_cache);
          modules = (uu___1683_24133.modules);
          expected_typ = (uu___1683_24133.expected_typ);
          sigtab = (uu___1683_24133.sigtab);
          attrtab = (uu___1683_24133.attrtab);
          instantiate_imp = (uu___1683_24133.instantiate_imp);
          effects = (uu___1683_24133.effects);
          generalize = (uu___1683_24133.generalize);
          letrecs = (uu___1683_24133.letrecs);
          top_level = (uu___1683_24133.top_level);
          check_uvars = (uu___1683_24133.check_uvars);
          use_eq = (uu___1683_24133.use_eq);
          is_iface = (uu___1683_24133.is_iface);
          admit = (uu___1683_24133.admit);
          lax = (uu___1683_24133.lax);
          lax_universes = (uu___1683_24133.lax_universes);
          phase1 = (uu___1683_24133.phase1);
          failhard = (uu___1683_24133.failhard);
          nosynth = (uu___1683_24133.nosynth);
          uvar_subtyping = (uu___1683_24133.uvar_subtyping);
          tc_term = (uu___1683_24133.tc_term);
          type_of = (uu___1683_24133.type_of);
          universe_of = (uu___1683_24133.universe_of);
          check_type_of = (uu___1683_24133.check_type_of);
          use_bv_sorts = (uu___1683_24133.use_bv_sorts);
          qtbl_name_and_index = (uu___1683_24133.qtbl_name_and_index);
          normalized_eff_names = (uu___1683_24133.normalized_eff_names);
          fv_delta_depths = (uu___1683_24133.fv_delta_depths);
          proof_ns = (uu___1683_24133.proof_ns);
          synth_hook = (uu___1683_24133.synth_hook);
          try_solve_implicits_hook =
            (uu___1683_24133.try_solve_implicits_hook);
          splice = (uu___1683_24133.splice);
          mpreprocess = (uu___1683_24133.mpreprocess);
          postprocess = (uu___1683_24133.postprocess);
          is_native_tactic = (uu___1683_24133.is_native_tactic);
          identifier_info = (uu___1683_24133.identifier_info);
          tc_hooks = (uu___1683_24133.tc_hooks);
          dsenv = (uu___1683_24133.dsenv);
          nbe = (uu___1683_24133.nbe);
          strict_args_tab = (uu___1683_24133.strict_args_tab);
          erasable_types_tab = (uu___1683_24133.erasable_types_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      env1
  
let (push_new_effect :
  env ->
    (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list)
      -> env)
  =
  fun env  ->
    fun uu____24152  ->
      match uu____24152 with
      | (ed,quals) ->
          let effects =
            let uu___1692_24166 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1692_24166.order);
              joins = (uu___1692_24166.joins);
              polymonadic_binds = (uu___1692_24166.polymonadic_binds)
            }  in
          let uu___1695_24175 = env  in
          {
            solver = (uu___1695_24175.solver);
            range = (uu___1695_24175.range);
            curmodule = (uu___1695_24175.curmodule);
            gamma = (uu___1695_24175.gamma);
            gamma_sig = (uu___1695_24175.gamma_sig);
            gamma_cache = (uu___1695_24175.gamma_cache);
            modules = (uu___1695_24175.modules);
            expected_typ = (uu___1695_24175.expected_typ);
            sigtab = (uu___1695_24175.sigtab);
            attrtab = (uu___1695_24175.attrtab);
            instantiate_imp = (uu___1695_24175.instantiate_imp);
            effects;
            generalize = (uu___1695_24175.generalize);
            letrecs = (uu___1695_24175.letrecs);
            top_level = (uu___1695_24175.top_level);
            check_uvars = (uu___1695_24175.check_uvars);
            use_eq = (uu___1695_24175.use_eq);
            is_iface = (uu___1695_24175.is_iface);
            admit = (uu___1695_24175.admit);
            lax = (uu___1695_24175.lax);
            lax_universes = (uu___1695_24175.lax_universes);
            phase1 = (uu___1695_24175.phase1);
            failhard = (uu___1695_24175.failhard);
            nosynth = (uu___1695_24175.nosynth);
            uvar_subtyping = (uu___1695_24175.uvar_subtyping);
            tc_term = (uu___1695_24175.tc_term);
            type_of = (uu___1695_24175.type_of);
            universe_of = (uu___1695_24175.universe_of);
            check_type_of = (uu___1695_24175.check_type_of);
            use_bv_sorts = (uu___1695_24175.use_bv_sorts);
            qtbl_name_and_index = (uu___1695_24175.qtbl_name_and_index);
            normalized_eff_names = (uu___1695_24175.normalized_eff_names);
            fv_delta_depths = (uu___1695_24175.fv_delta_depths);
            proof_ns = (uu___1695_24175.proof_ns);
            synth_hook = (uu___1695_24175.synth_hook);
            try_solve_implicits_hook =
              (uu___1695_24175.try_solve_implicits_hook);
            splice = (uu___1695_24175.splice);
            mpreprocess = (uu___1695_24175.mpreprocess);
            postprocess = (uu___1695_24175.postprocess);
            is_native_tactic = (uu___1695_24175.is_native_tactic);
            identifier_info = (uu___1695_24175.identifier_info);
            tc_hooks = (uu___1695_24175.tc_hooks);
            dsenv = (uu___1695_24175.dsenv);
            nbe = (uu___1695_24175.nbe);
            strict_args_tab = (uu___1695_24175.strict_args_tab);
            erasable_types_tab = (uu___1695_24175.erasable_types_tab)
          }
  
let (exists_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident * polymonadic_bind_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        let uu____24204 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____24272  ->
                  match uu____24272 with
                  | (m1,n11,uu____24290,uu____24291) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____24204 with
        | FStar_Pervasives_Native.Some (uu____24316,uu____24317,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____24362 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24437 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24437
                  (fun uu____24458  ->
                     match uu____24458 with
                     | (c1,g1) ->
                         let uu____24469 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24469
                           (fun uu____24490  ->
                              match uu____24490 with
                              | (c2,g2) ->
                                  let uu____24501 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24501)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24623 = l1 u t e  in
                              l2 u t uu____24623))
                | uu____24624 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let edge = { msource = src; mtarget = tgt; mlift = st_mlift }  in
          let id_edge l =
            { msource = src; mtarget = tgt; mlift = identity_mlift }  in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____24692  ->
                    match uu____24692 with
                    | (e,uu____24700) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24723 =
            match uu____24723 with
            | (i,j) ->
                let uu____24734 = FStar_Ident.lid_equals i j  in
                if uu____24734
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _24741  -> FStar_Pervasives_Native.Some _24741)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24770 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24780 = FStar_Ident.lid_equals i k  in
                        if uu____24780
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24794 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24794
                                  then []
                                  else
                                    (let uu____24801 =
                                       let uu____24810 =
                                         find_edge order1 (i, k)  in
                                       let uu____24813 =
                                         find_edge order1 (k, j)  in
                                       (uu____24810, uu____24813)  in
                                     match uu____24801 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24828 =
                                           compose_edges e1 e2  in
                                         [uu____24828]
                                     | uu____24829 -> [])))))
                 in
              FStar_List.append order1 uu____24770  in
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
               (fun edge1  ->
                  let uu____24859 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24862 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____24862
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24859
                  then
                    let uu____24869 =
                      let uu____24875 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24875)
                       in
                    let uu____24879 = get_range env  in
                    FStar_Errors.raise_error uu____24869 uu____24879
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____24957 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24957
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____25009 =
                                             let uu____25018 =
                                               find_edge order2 (i, k)  in
                                             let uu____25021 =
                                               find_edge order2 (j, k)  in
                                             (uu____25018, uu____25021)  in
                                           match uu____25009 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____25063,uu____25064)
                                                    ->
                                                    let uu____25071 =
                                                      let uu____25078 =
                                                        let uu____25080 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25080
                                                         in
                                                      let uu____25083 =
                                                        let uu____25085 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____25085
                                                         in
                                                      (uu____25078,
                                                        uu____25083)
                                                       in
                                                    (match uu____25071 with
                                                     | (true ,true ) ->
                                                         let uu____25102 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____25102
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
                                           | uu____25145 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____25197 =
                                   let uu____25199 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____25199
                                     FStar_Util.is_some
                                    in
                                 if uu____25197
                                 then
                                   let uu____25248 =
                                     let uu____25254 =
                                       let uu____25256 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____25258 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____25260 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____25262 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____25256 uu____25258 uu____25260
                                         uu____25262
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____25254)
                                      in
                                   FStar_Errors.raise_error uu____25248
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1816_25301 = env.effects  in
             {
               decls = (uu___1816_25301.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1816_25301.polymonadic_binds)
             }  in
           let uu___1819_25302 = env  in
           {
             solver = (uu___1819_25302.solver);
             range = (uu___1819_25302.range);
             curmodule = (uu___1819_25302.curmodule);
             gamma = (uu___1819_25302.gamma);
             gamma_sig = (uu___1819_25302.gamma_sig);
             gamma_cache = (uu___1819_25302.gamma_cache);
             modules = (uu___1819_25302.modules);
             expected_typ = (uu___1819_25302.expected_typ);
             sigtab = (uu___1819_25302.sigtab);
             attrtab = (uu___1819_25302.attrtab);
             instantiate_imp = (uu___1819_25302.instantiate_imp);
             effects;
             generalize = (uu___1819_25302.generalize);
             letrecs = (uu___1819_25302.letrecs);
             top_level = (uu___1819_25302.top_level);
             check_uvars = (uu___1819_25302.check_uvars);
             use_eq = (uu___1819_25302.use_eq);
             is_iface = (uu___1819_25302.is_iface);
             admit = (uu___1819_25302.admit);
             lax = (uu___1819_25302.lax);
             lax_universes = (uu___1819_25302.lax_universes);
             phase1 = (uu___1819_25302.phase1);
             failhard = (uu___1819_25302.failhard);
             nosynth = (uu___1819_25302.nosynth);
             uvar_subtyping = (uu___1819_25302.uvar_subtyping);
             tc_term = (uu___1819_25302.tc_term);
             type_of = (uu___1819_25302.type_of);
             universe_of = (uu___1819_25302.universe_of);
             check_type_of = (uu___1819_25302.check_type_of);
             use_bv_sorts = (uu___1819_25302.use_bv_sorts);
             qtbl_name_and_index = (uu___1819_25302.qtbl_name_and_index);
             normalized_eff_names = (uu___1819_25302.normalized_eff_names);
             fv_delta_depths = (uu___1819_25302.fv_delta_depths);
             proof_ns = (uu___1819_25302.proof_ns);
             synth_hook = (uu___1819_25302.synth_hook);
             try_solve_implicits_hook =
               (uu___1819_25302.try_solve_implicits_hook);
             splice = (uu___1819_25302.splice);
             mpreprocess = (uu___1819_25302.mpreprocess);
             postprocess = (uu___1819_25302.postprocess);
             is_native_tactic = (uu___1819_25302.is_native_tactic);
             identifier_info = (uu___1819_25302.identifier_info);
             tc_hooks = (uu___1819_25302.tc_hooks);
             dsenv = (uu___1819_25302.dsenv);
             nbe = (uu___1819_25302.nbe);
             strict_args_tab = (uu___1819_25302.strict_args_tab);
             erasable_types_tab = (uu___1819_25302.erasable_types_tab)
           })
  
let (add_polymonadic_bind :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Ident.lident -> polymonadic_bind_t -> env)
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ty  ->
            let err_msg poly =
              let uu____25350 = FStar_Ident.string_of_lid m  in
              let uu____25352 = FStar_Ident.string_of_lid n1  in
              let uu____25354 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____25350 uu____25352 uu____25354
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____25363 =
              let uu____25365 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____25365 FStar_Util.is_some  in
            if uu____25363
            then
              let uu____25402 =
                let uu____25408 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25408)
                 in
              FStar_Errors.raise_error uu____25402 env.range
            else
              (let uu____25414 =
                 let uu____25416 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25416 FStar_Util.is_some  in
               if uu____25414
               then
                 let uu____25441 =
                   let uu____25447 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25447)
                    in
                 FStar_Errors.raise_error uu____25441 env.range
               else
                 (let uu___1834_25453 = env  in
                  {
                    solver = (uu___1834_25453.solver);
                    range = (uu___1834_25453.range);
                    curmodule = (uu___1834_25453.curmodule);
                    gamma = (uu___1834_25453.gamma);
                    gamma_sig = (uu___1834_25453.gamma_sig);
                    gamma_cache = (uu___1834_25453.gamma_cache);
                    modules = (uu___1834_25453.modules);
                    expected_typ = (uu___1834_25453.expected_typ);
                    sigtab = (uu___1834_25453.sigtab);
                    attrtab = (uu___1834_25453.attrtab);
                    instantiate_imp = (uu___1834_25453.instantiate_imp);
                    effects =
                      (let uu___1836_25455 = env.effects  in
                       {
                         decls = (uu___1836_25455.decls);
                         order = (uu___1836_25455.order);
                         joins = (uu___1836_25455.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1834_25453.generalize);
                    letrecs = (uu___1834_25453.letrecs);
                    top_level = (uu___1834_25453.top_level);
                    check_uvars = (uu___1834_25453.check_uvars);
                    use_eq = (uu___1834_25453.use_eq);
                    is_iface = (uu___1834_25453.is_iface);
                    admit = (uu___1834_25453.admit);
                    lax = (uu___1834_25453.lax);
                    lax_universes = (uu___1834_25453.lax_universes);
                    phase1 = (uu___1834_25453.phase1);
                    failhard = (uu___1834_25453.failhard);
                    nosynth = (uu___1834_25453.nosynth);
                    uvar_subtyping = (uu___1834_25453.uvar_subtyping);
                    tc_term = (uu___1834_25453.tc_term);
                    type_of = (uu___1834_25453.type_of);
                    universe_of = (uu___1834_25453.universe_of);
                    check_type_of = (uu___1834_25453.check_type_of);
                    use_bv_sorts = (uu___1834_25453.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1834_25453.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1834_25453.normalized_eff_names);
                    fv_delta_depths = (uu___1834_25453.fv_delta_depths);
                    proof_ns = (uu___1834_25453.proof_ns);
                    synth_hook = (uu___1834_25453.synth_hook);
                    try_solve_implicits_hook =
                      (uu___1834_25453.try_solve_implicits_hook);
                    splice = (uu___1834_25453.splice);
                    mpreprocess = (uu___1834_25453.mpreprocess);
                    postprocess = (uu___1834_25453.postprocess);
                    is_native_tactic = (uu___1834_25453.is_native_tactic);
                    identifier_info = (uu___1834_25453.identifier_info);
                    tc_hooks = (uu___1834_25453.tc_hooks);
                    dsenv = (uu___1834_25453.dsenv);
                    nbe = (uu___1834_25453.nbe);
                    strict_args_tab = (uu___1834_25453.strict_args_tab);
                    erasable_types_tab = (uu___1834_25453.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1840_25527 = env  in
      {
        solver = (uu___1840_25527.solver);
        range = (uu___1840_25527.range);
        curmodule = (uu___1840_25527.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1840_25527.gamma_sig);
        gamma_cache = (uu___1840_25527.gamma_cache);
        modules = (uu___1840_25527.modules);
        expected_typ = (uu___1840_25527.expected_typ);
        sigtab = (uu___1840_25527.sigtab);
        attrtab = (uu___1840_25527.attrtab);
        instantiate_imp = (uu___1840_25527.instantiate_imp);
        effects = (uu___1840_25527.effects);
        generalize = (uu___1840_25527.generalize);
        letrecs = (uu___1840_25527.letrecs);
        top_level = (uu___1840_25527.top_level);
        check_uvars = (uu___1840_25527.check_uvars);
        use_eq = (uu___1840_25527.use_eq);
        is_iface = (uu___1840_25527.is_iface);
        admit = (uu___1840_25527.admit);
        lax = (uu___1840_25527.lax);
        lax_universes = (uu___1840_25527.lax_universes);
        phase1 = (uu___1840_25527.phase1);
        failhard = (uu___1840_25527.failhard);
        nosynth = (uu___1840_25527.nosynth);
        uvar_subtyping = (uu___1840_25527.uvar_subtyping);
        tc_term = (uu___1840_25527.tc_term);
        type_of = (uu___1840_25527.type_of);
        universe_of = (uu___1840_25527.universe_of);
        check_type_of = (uu___1840_25527.check_type_of);
        use_bv_sorts = (uu___1840_25527.use_bv_sorts);
        qtbl_name_and_index = (uu___1840_25527.qtbl_name_and_index);
        normalized_eff_names = (uu___1840_25527.normalized_eff_names);
        fv_delta_depths = (uu___1840_25527.fv_delta_depths);
        proof_ns = (uu___1840_25527.proof_ns);
        synth_hook = (uu___1840_25527.synth_hook);
        try_solve_implicits_hook = (uu___1840_25527.try_solve_implicits_hook);
        splice = (uu___1840_25527.splice);
        mpreprocess = (uu___1840_25527.mpreprocess);
        postprocess = (uu___1840_25527.postprocess);
        is_native_tactic = (uu___1840_25527.is_native_tactic);
        identifier_info = (uu___1840_25527.identifier_info);
        tc_hooks = (uu___1840_25527.tc_hooks);
        dsenv = (uu___1840_25527.dsenv);
        nbe = (uu___1840_25527.nbe);
        strict_args_tab = (uu___1840_25527.strict_args_tab);
        erasable_types_tab = (uu___1840_25527.erasable_types_tab)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env -> (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option) =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___1853_25585 = env  in
             {
               solver = (uu___1853_25585.solver);
               range = (uu___1853_25585.range);
               curmodule = (uu___1853_25585.curmodule);
               gamma = rest;
               gamma_sig = (uu___1853_25585.gamma_sig);
               gamma_cache = (uu___1853_25585.gamma_cache);
               modules = (uu___1853_25585.modules);
               expected_typ = (uu___1853_25585.expected_typ);
               sigtab = (uu___1853_25585.sigtab);
               attrtab = (uu___1853_25585.attrtab);
               instantiate_imp = (uu___1853_25585.instantiate_imp);
               effects = (uu___1853_25585.effects);
               generalize = (uu___1853_25585.generalize);
               letrecs = (uu___1853_25585.letrecs);
               top_level = (uu___1853_25585.top_level);
               check_uvars = (uu___1853_25585.check_uvars);
               use_eq = (uu___1853_25585.use_eq);
               is_iface = (uu___1853_25585.is_iface);
               admit = (uu___1853_25585.admit);
               lax = (uu___1853_25585.lax);
               lax_universes = (uu___1853_25585.lax_universes);
               phase1 = (uu___1853_25585.phase1);
               failhard = (uu___1853_25585.failhard);
               nosynth = (uu___1853_25585.nosynth);
               uvar_subtyping = (uu___1853_25585.uvar_subtyping);
               tc_term = (uu___1853_25585.tc_term);
               type_of = (uu___1853_25585.type_of);
               universe_of = (uu___1853_25585.universe_of);
               check_type_of = (uu___1853_25585.check_type_of);
               use_bv_sorts = (uu___1853_25585.use_bv_sorts);
               qtbl_name_and_index = (uu___1853_25585.qtbl_name_and_index);
               normalized_eff_names = (uu___1853_25585.normalized_eff_names);
               fv_delta_depths = (uu___1853_25585.fv_delta_depths);
               proof_ns = (uu___1853_25585.proof_ns);
               synth_hook = (uu___1853_25585.synth_hook);
               try_solve_implicits_hook =
                 (uu___1853_25585.try_solve_implicits_hook);
               splice = (uu___1853_25585.splice);
               mpreprocess = (uu___1853_25585.mpreprocess);
               postprocess = (uu___1853_25585.postprocess);
               is_native_tactic = (uu___1853_25585.is_native_tactic);
               identifier_info = (uu___1853_25585.identifier_info);
               tc_hooks = (uu___1853_25585.tc_hooks);
               dsenv = (uu___1853_25585.dsenv);
               nbe = (uu___1853_25585.nbe);
               strict_args_tab = (uu___1853_25585.strict_args_tab);
               erasable_types_tab = (uu___1853_25585.erasable_types_tab)
             }))
    | uu____25586 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25615  ->
             match uu____25615 with | (x,uu____25623) -> push_bv env1 x) env
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
            let uu___1867_25658 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1867_25658.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1867_25658.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun x  ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term
          Prims.list))
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____25731 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25731 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____25759 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25759)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1888_25775 = env  in
      {
        solver = (uu___1888_25775.solver);
        range = (uu___1888_25775.range);
        curmodule = (uu___1888_25775.curmodule);
        gamma = (uu___1888_25775.gamma);
        gamma_sig = (uu___1888_25775.gamma_sig);
        gamma_cache = (uu___1888_25775.gamma_cache);
        modules = (uu___1888_25775.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1888_25775.sigtab);
        attrtab = (uu___1888_25775.attrtab);
        instantiate_imp = (uu___1888_25775.instantiate_imp);
        effects = (uu___1888_25775.effects);
        generalize = (uu___1888_25775.generalize);
        letrecs = (uu___1888_25775.letrecs);
        top_level = (uu___1888_25775.top_level);
        check_uvars = (uu___1888_25775.check_uvars);
        use_eq = false;
        is_iface = (uu___1888_25775.is_iface);
        admit = (uu___1888_25775.admit);
        lax = (uu___1888_25775.lax);
        lax_universes = (uu___1888_25775.lax_universes);
        phase1 = (uu___1888_25775.phase1);
        failhard = (uu___1888_25775.failhard);
        nosynth = (uu___1888_25775.nosynth);
        uvar_subtyping = (uu___1888_25775.uvar_subtyping);
        tc_term = (uu___1888_25775.tc_term);
        type_of = (uu___1888_25775.type_of);
        universe_of = (uu___1888_25775.universe_of);
        check_type_of = (uu___1888_25775.check_type_of);
        use_bv_sorts = (uu___1888_25775.use_bv_sorts);
        qtbl_name_and_index = (uu___1888_25775.qtbl_name_and_index);
        normalized_eff_names = (uu___1888_25775.normalized_eff_names);
        fv_delta_depths = (uu___1888_25775.fv_delta_depths);
        proof_ns = (uu___1888_25775.proof_ns);
        synth_hook = (uu___1888_25775.synth_hook);
        try_solve_implicits_hook = (uu___1888_25775.try_solve_implicits_hook);
        splice = (uu___1888_25775.splice);
        mpreprocess = (uu___1888_25775.mpreprocess);
        postprocess = (uu___1888_25775.postprocess);
        is_native_tactic = (uu___1888_25775.is_native_tactic);
        identifier_info = (uu___1888_25775.identifier_info);
        tc_hooks = (uu___1888_25775.tc_hooks);
        dsenv = (uu___1888_25775.dsenv);
        nbe = (uu___1888_25775.nbe);
        strict_args_tab = (uu___1888_25775.strict_args_tab);
        erasable_types_tab = (uu___1888_25775.erasable_types_tab)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env -> (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)) =
  fun env_  ->
    let uu____25806 = expected_typ env_  in
    ((let uu___1895_25812 = env_  in
      {
        solver = (uu___1895_25812.solver);
        range = (uu___1895_25812.range);
        curmodule = (uu___1895_25812.curmodule);
        gamma = (uu___1895_25812.gamma);
        gamma_sig = (uu___1895_25812.gamma_sig);
        gamma_cache = (uu___1895_25812.gamma_cache);
        modules = (uu___1895_25812.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1895_25812.sigtab);
        attrtab = (uu___1895_25812.attrtab);
        instantiate_imp = (uu___1895_25812.instantiate_imp);
        effects = (uu___1895_25812.effects);
        generalize = (uu___1895_25812.generalize);
        letrecs = (uu___1895_25812.letrecs);
        top_level = (uu___1895_25812.top_level);
        check_uvars = (uu___1895_25812.check_uvars);
        use_eq = false;
        is_iface = (uu___1895_25812.is_iface);
        admit = (uu___1895_25812.admit);
        lax = (uu___1895_25812.lax);
        lax_universes = (uu___1895_25812.lax_universes);
        phase1 = (uu___1895_25812.phase1);
        failhard = (uu___1895_25812.failhard);
        nosynth = (uu___1895_25812.nosynth);
        uvar_subtyping = (uu___1895_25812.uvar_subtyping);
        tc_term = (uu___1895_25812.tc_term);
        type_of = (uu___1895_25812.type_of);
        universe_of = (uu___1895_25812.universe_of);
        check_type_of = (uu___1895_25812.check_type_of);
        use_bv_sorts = (uu___1895_25812.use_bv_sorts);
        qtbl_name_and_index = (uu___1895_25812.qtbl_name_and_index);
        normalized_eff_names = (uu___1895_25812.normalized_eff_names);
        fv_delta_depths = (uu___1895_25812.fv_delta_depths);
        proof_ns = (uu___1895_25812.proof_ns);
        synth_hook = (uu___1895_25812.synth_hook);
        try_solve_implicits_hook = (uu___1895_25812.try_solve_implicits_hook);
        splice = (uu___1895_25812.splice);
        mpreprocess = (uu___1895_25812.mpreprocess);
        postprocess = (uu___1895_25812.postprocess);
        is_native_tactic = (uu___1895_25812.is_native_tactic);
        identifier_info = (uu___1895_25812.identifier_info);
        tc_hooks = (uu___1895_25812.tc_hooks);
        dsenv = (uu___1895_25812.dsenv);
        nbe = (uu___1895_25812.nbe);
        strict_args_tab = (uu___1895_25812.strict_args_tab);
        erasable_types_tab = (uu___1895_25812.erasable_types_tab)
      }), uu____25806)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25824 =
      let uu____25827 = FStar_Ident.id_of_text ""  in [uu____25827]  in
    FStar_Ident.lid_of_ids uu____25824  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____25834 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25834
        then
          let uu____25839 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25839 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1903_25867 = env  in
       {
         solver = (uu___1903_25867.solver);
         range = (uu___1903_25867.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1903_25867.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1903_25867.expected_typ);
         sigtab = (uu___1903_25867.sigtab);
         attrtab = (uu___1903_25867.attrtab);
         instantiate_imp = (uu___1903_25867.instantiate_imp);
         effects = (uu___1903_25867.effects);
         generalize = (uu___1903_25867.generalize);
         letrecs = (uu___1903_25867.letrecs);
         top_level = (uu___1903_25867.top_level);
         check_uvars = (uu___1903_25867.check_uvars);
         use_eq = (uu___1903_25867.use_eq);
         is_iface = (uu___1903_25867.is_iface);
         admit = (uu___1903_25867.admit);
         lax = (uu___1903_25867.lax);
         lax_universes = (uu___1903_25867.lax_universes);
         phase1 = (uu___1903_25867.phase1);
         failhard = (uu___1903_25867.failhard);
         nosynth = (uu___1903_25867.nosynth);
         uvar_subtyping = (uu___1903_25867.uvar_subtyping);
         tc_term = (uu___1903_25867.tc_term);
         type_of = (uu___1903_25867.type_of);
         universe_of = (uu___1903_25867.universe_of);
         check_type_of = (uu___1903_25867.check_type_of);
         use_bv_sorts = (uu___1903_25867.use_bv_sorts);
         qtbl_name_and_index = (uu___1903_25867.qtbl_name_and_index);
         normalized_eff_names = (uu___1903_25867.normalized_eff_names);
         fv_delta_depths = (uu___1903_25867.fv_delta_depths);
         proof_ns = (uu___1903_25867.proof_ns);
         synth_hook = (uu___1903_25867.synth_hook);
         try_solve_implicits_hook =
           (uu___1903_25867.try_solve_implicits_hook);
         splice = (uu___1903_25867.splice);
         mpreprocess = (uu___1903_25867.mpreprocess);
         postprocess = (uu___1903_25867.postprocess);
         is_native_tactic = (uu___1903_25867.is_native_tactic);
         identifier_info = (uu___1903_25867.identifier_info);
         tc_hooks = (uu___1903_25867.tc_hooks);
         dsenv = (uu___1903_25867.dsenv);
         nbe = (uu___1903_25867.nbe);
         strict_args_tab = (uu___1903_25867.strict_args_tab);
         erasable_types_tab = (uu___1903_25867.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25919)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25923,(uu____25924,t)))::tl1
          ->
          let uu____25945 =
            let uu____25948 = FStar_Syntax_Free.uvars t  in
            ext out uu____25948  in
          aux uu____25945 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25951;
            FStar_Syntax_Syntax.index = uu____25952;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25960 =
            let uu____25963 = FStar_Syntax_Free.uvars t  in
            ext out uu____25963  in
          aux uu____25960 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____26021)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26025,(uu____26026,t)))::tl1
          ->
          let uu____26047 =
            let uu____26050 = FStar_Syntax_Free.univs t  in
            ext out uu____26050  in
          aux uu____26047 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26053;
            FStar_Syntax_Syntax.index = uu____26054;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26062 =
            let uu____26065 = FStar_Syntax_Free.univs t  in
            ext out uu____26065  in
          aux uu____26062 tl1
       in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____26127 = FStar_Util.set_add uname out  in
          aux uu____26127 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____26130,(uu____26131,t)))::tl1
          ->
          let uu____26152 =
            let uu____26155 = FStar_Syntax_Free.univnames t  in
            ext out uu____26155  in
          aux uu____26152 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____26158;
            FStar_Syntax_Syntax.index = uu____26159;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____26167 =
            let uu____26170 = FStar_Syntax_Free.univnames t  in
            ext out uu____26170  in
          aux uu____26167 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_26191  ->
            match uu___12_26191 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____26195 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____26208 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____26219 =
      let uu____26228 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____26228
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____26219 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____26276 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_26289  ->
              match uu___13_26289 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____26292 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____26292
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____26298) ->
                  let uu____26315 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____26315))
       in
    FStar_All.pipe_right uu____26276 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_26329  ->
    match uu___14_26329 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____26335 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____26335
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____26358  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26413) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26446,uu____26447) -> false  in
      let uu____26461 =
        FStar_List.tryFind
          (fun uu____26483  ->
             match uu____26483 with | (p,uu____26494) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26461 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26513,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26543 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26543
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2046_26565 = e  in
        {
          solver = (uu___2046_26565.solver);
          range = (uu___2046_26565.range);
          curmodule = (uu___2046_26565.curmodule);
          gamma = (uu___2046_26565.gamma);
          gamma_sig = (uu___2046_26565.gamma_sig);
          gamma_cache = (uu___2046_26565.gamma_cache);
          modules = (uu___2046_26565.modules);
          expected_typ = (uu___2046_26565.expected_typ);
          sigtab = (uu___2046_26565.sigtab);
          attrtab = (uu___2046_26565.attrtab);
          instantiate_imp = (uu___2046_26565.instantiate_imp);
          effects = (uu___2046_26565.effects);
          generalize = (uu___2046_26565.generalize);
          letrecs = (uu___2046_26565.letrecs);
          top_level = (uu___2046_26565.top_level);
          check_uvars = (uu___2046_26565.check_uvars);
          use_eq = (uu___2046_26565.use_eq);
          is_iface = (uu___2046_26565.is_iface);
          admit = (uu___2046_26565.admit);
          lax = (uu___2046_26565.lax);
          lax_universes = (uu___2046_26565.lax_universes);
          phase1 = (uu___2046_26565.phase1);
          failhard = (uu___2046_26565.failhard);
          nosynth = (uu___2046_26565.nosynth);
          uvar_subtyping = (uu___2046_26565.uvar_subtyping);
          tc_term = (uu___2046_26565.tc_term);
          type_of = (uu___2046_26565.type_of);
          universe_of = (uu___2046_26565.universe_of);
          check_type_of = (uu___2046_26565.check_type_of);
          use_bv_sorts = (uu___2046_26565.use_bv_sorts);
          qtbl_name_and_index = (uu___2046_26565.qtbl_name_and_index);
          normalized_eff_names = (uu___2046_26565.normalized_eff_names);
          fv_delta_depths = (uu___2046_26565.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2046_26565.synth_hook);
          try_solve_implicits_hook =
            (uu___2046_26565.try_solve_implicits_hook);
          splice = (uu___2046_26565.splice);
          mpreprocess = (uu___2046_26565.mpreprocess);
          postprocess = (uu___2046_26565.postprocess);
          is_native_tactic = (uu___2046_26565.is_native_tactic);
          identifier_info = (uu___2046_26565.identifier_info);
          tc_hooks = (uu___2046_26565.tc_hooks);
          dsenv = (uu___2046_26565.dsenv);
          nbe = (uu___2046_26565.nbe);
          strict_args_tab = (uu___2046_26565.strict_args_tab);
          erasable_types_tab = (uu___2046_26565.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2055_26613 = e  in
      {
        solver = (uu___2055_26613.solver);
        range = (uu___2055_26613.range);
        curmodule = (uu___2055_26613.curmodule);
        gamma = (uu___2055_26613.gamma);
        gamma_sig = (uu___2055_26613.gamma_sig);
        gamma_cache = (uu___2055_26613.gamma_cache);
        modules = (uu___2055_26613.modules);
        expected_typ = (uu___2055_26613.expected_typ);
        sigtab = (uu___2055_26613.sigtab);
        attrtab = (uu___2055_26613.attrtab);
        instantiate_imp = (uu___2055_26613.instantiate_imp);
        effects = (uu___2055_26613.effects);
        generalize = (uu___2055_26613.generalize);
        letrecs = (uu___2055_26613.letrecs);
        top_level = (uu___2055_26613.top_level);
        check_uvars = (uu___2055_26613.check_uvars);
        use_eq = (uu___2055_26613.use_eq);
        is_iface = (uu___2055_26613.is_iface);
        admit = (uu___2055_26613.admit);
        lax = (uu___2055_26613.lax);
        lax_universes = (uu___2055_26613.lax_universes);
        phase1 = (uu___2055_26613.phase1);
        failhard = (uu___2055_26613.failhard);
        nosynth = (uu___2055_26613.nosynth);
        uvar_subtyping = (uu___2055_26613.uvar_subtyping);
        tc_term = (uu___2055_26613.tc_term);
        type_of = (uu___2055_26613.type_of);
        universe_of = (uu___2055_26613.universe_of);
        check_type_of = (uu___2055_26613.check_type_of);
        use_bv_sorts = (uu___2055_26613.use_bv_sorts);
        qtbl_name_and_index = (uu___2055_26613.qtbl_name_and_index);
        normalized_eff_names = (uu___2055_26613.normalized_eff_names);
        fv_delta_depths = (uu___2055_26613.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2055_26613.synth_hook);
        try_solve_implicits_hook = (uu___2055_26613.try_solve_implicits_hook);
        splice = (uu___2055_26613.splice);
        mpreprocess = (uu___2055_26613.mpreprocess);
        postprocess = (uu___2055_26613.postprocess);
        is_native_tactic = (uu___2055_26613.is_native_tactic);
        identifier_info = (uu___2055_26613.identifier_info);
        tc_hooks = (uu___2055_26613.tc_hooks);
        dsenv = (uu___2055_26613.dsenv);
        nbe = (uu___2055_26613.nbe);
        strict_args_tab = (uu___2055_26613.strict_args_tab);
        erasable_types_tab = (uu___2055_26613.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26629 = FStar_Syntax_Free.names t  in
      let uu____26632 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26629 uu____26632
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26655 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26655
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26665 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26665
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____26686 =
      match uu____26686 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26706 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26706)
       in
    let uu____26714 =
      let uu____26718 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____26718 FStar_List.rev  in
    FStar_All.pipe_right uu____26714 (FStar_String.concat " ")
  
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
                  (let uu____26786 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26786 with
                   | FStar_Pervasives_Native.Some uu____26790 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26793 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26803;
        FStar_TypeChecker_Common.univ_ineqs = uu____26804;
        FStar_TypeChecker_Common.implicits = uu____26805;_} -> true
    | uu____26815 -> false
  
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
          let uu___2099_26837 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2099_26837.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2099_26837.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2099_26837.FStar_TypeChecker_Common.implicits)
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
          let uu____26876 = FStar_Options.defensive ()  in
          if uu____26876
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26882 =
              let uu____26884 =
                let uu____26886 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26886  in
              Prims.op_Negation uu____26884  in
            (if uu____26882
             then
               let uu____26893 =
                 let uu____26899 =
                   let uu____26901 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26903 =
                     let uu____26905 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26905
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26901 uu____26903
                    in
                 (FStar_Errors.Warning_Defensive, uu____26899)  in
               FStar_Errors.log_issue rng uu____26893
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
          let uu____26945 =
            let uu____26947 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26947  in
          if uu____26945
          then ()
          else
            (let uu____26952 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26952 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26978 =
            let uu____26980 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26980  in
          if uu____26978
          then ()
          else
            (let uu____26985 = bound_vars e  in
             def_check_closed_in rng msg uu____26985 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.FStar_TypeChecker_Common.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2136_27024 = g  in
          let uu____27025 =
            let uu____27026 =
              let uu____27027 =
                let uu____27034 =
                  let uu____27035 =
                    let uu____27052 =
                      let uu____27063 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____27063]  in
                    (f, uu____27052)  in
                  FStar_Syntax_Syntax.Tm_app uu____27035  in
                FStar_Syntax_Syntax.mk uu____27034  in
              uu____27027 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _27100  -> FStar_TypeChecker_Common.NonTrivial _27100)
              uu____27026
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____27025;
            FStar_TypeChecker_Common.deferred =
              (uu___2136_27024.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2136_27024.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2136_27024.FStar_TypeChecker_Common.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2143_27118 = g  in
          let uu____27119 =
            let uu____27120 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27120  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27119;
            FStar_TypeChecker_Common.deferred =
              (uu___2143_27118.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2143_27118.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2143_27118.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2148_27137 = g  in
          let uu____27138 =
            let uu____27139 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____27139  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27138;
            FStar_TypeChecker_Common.deferred =
              (uu___2148_27137.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2148_27137.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2148_27137.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2152_27141 = g  in
          let uu____27142 =
            let uu____27143 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____27143  in
          {
            FStar_TypeChecker_Common.guard_f = uu____27142;
            FStar_TypeChecker_Common.deferred =
              (uu___2152_27141.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2152_27141.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2152_27141.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____27150 ->
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
                       let uu____27227 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____27227
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2175_27234 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2175_27234.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2175_27234.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2175_27234.FStar_TypeChecker_Common.implicits)
            }
  
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____27268 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____27268
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2190_27295 = g  in
            let uu____27296 =
              let uu____27297 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____27297  in
            {
              FStar_TypeChecker_Common.guard_f = uu____27296;
              FStar_TypeChecker_Common.deferred =
                (uu___2190_27295.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2190_27295.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2190_27295.FStar_TypeChecker_Common.implicits)
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
      fun env  ->
        fun k  ->
          fun should_check  ->
            fun meta  ->
              let uu____27355 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____27355 with
              | FStar_Pervasives_Native.Some
                  (uu____27380::(tm,uu____27382)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27446 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27464 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27464;
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
                    let g =
                      let uu___2212_27496 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2212_27496.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2212_27496.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2212_27496.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (uvars_for_binders :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.subst_t ->
        (FStar_Syntax_Syntax.binder -> Prims.string) ->
          FStar_Range.range ->
            (FStar_Syntax_Syntax.term Prims.list * guard_t))
  =
  fun env  ->
    fun bs  ->
      fun substs  ->
        fun reason  ->
          fun r  ->
            let uu____27550 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27607  ->
                      fun b  ->
                        match uu____27607 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27649 =
                              let uu____27662 = reason b  in
                              new_implicit_var_aux uu____27662 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27649 with
                             | (t,uu____27679,g_t) ->
                                 let uu____27693 =
                                   let uu____27696 =
                                     let uu____27699 =
                                       let uu____27700 =
                                         let uu____27707 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27707, t)  in
                                       FStar_Syntax_Syntax.NT uu____27700  in
                                     [uu____27699]  in
                                   FStar_List.append substs1 uu____27696  in
                                 let uu____27718 = conj_guard g g_t  in
                                 (uu____27693,
                                   (FStar_List.append uvars1 [t]),
                                   uu____27718))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27550
              (fun uu____27747  ->
                 match uu____27747 with
                 | (uu____27764,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____27780  -> ());
    push = (fun uu____27782  -> ());
    pop = (fun uu____27785  -> ());
    snapshot =
      (fun uu____27788  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____27807  -> fun uu____27808  -> ());
    encode_sig = (fun uu____27823  -> fun uu____27824  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____27830 =
             let uu____27837 = FStar_Options.peek ()  in (e, g, uu____27837)
              in
           [uu____27830]);
    solve = (fun uu____27853  -> fun uu____27854  -> fun uu____27855  -> ());
    finish = (fun uu____27862  -> ());
    refresh = (fun uu____27864  -> ())
  } 