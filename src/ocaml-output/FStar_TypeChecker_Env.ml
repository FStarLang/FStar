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
  fun projectee  -> match projectee with | Beta  -> true | uu____103 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____114 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____125 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____137 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____155 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____166 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____177 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____188 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____199 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____210 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____222 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____243 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____270 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____297 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____321 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____332 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____343 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____354 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____365 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____376 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____387 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____398 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____409 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____420 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____431 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____442 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____453 -> false
  
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
      | uu____513 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____539 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____550 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____561 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____573 -> false
  
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
  fun projectee  -> match projectee with | { decls; order; joins;_} -> decls 
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> order 
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> joins 
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> curmodule
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> gamma_cache
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> modules
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> expected_typ
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> sigtab
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> generalize
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> uvar_subtyping
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_term
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> type_of
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> universe_of
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> use_bv_sorts
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> qtbl_name_and_index
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> normalized_eff_names
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> proof_ns
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> try_solve_implicits_hook
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> splice1
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> postprocess
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> is_native_tactic
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> dsenv
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> nbe1
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> strict_args_tab
  
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
        synth_hook; try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> erasable_types_tab
  
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
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicit = FStar_TypeChecker_Common.implicit
type implicits = FStar_TypeChecker_Common.implicits
type guard_t = FStar_TypeChecker_Common.guard_t
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
           (fun uu___0_12950  ->
              match uu___0_12950 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12953 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12953  in
                  let uu____12954 =
                    let uu____12955 = FStar_Syntax_Subst.compress y  in
                    uu____12955.FStar_Syntax_Syntax.n  in
                  (match uu____12954 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12959 =
                         let uu___312_12960 = y1  in
                         let uu____12961 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___312_12960.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___312_12960.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12961
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12959
                   | uu____12964 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___318_12978 = env  in
      let uu____12979 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___318_12978.solver);
        range = (uu___318_12978.range);
        curmodule = (uu___318_12978.curmodule);
        gamma = uu____12979;
        gamma_sig = (uu___318_12978.gamma_sig);
        gamma_cache = (uu___318_12978.gamma_cache);
        modules = (uu___318_12978.modules);
        expected_typ = (uu___318_12978.expected_typ);
        sigtab = (uu___318_12978.sigtab);
        attrtab = (uu___318_12978.attrtab);
        instantiate_imp = (uu___318_12978.instantiate_imp);
        effects = (uu___318_12978.effects);
        generalize = (uu___318_12978.generalize);
        letrecs = (uu___318_12978.letrecs);
        top_level = (uu___318_12978.top_level);
        check_uvars = (uu___318_12978.check_uvars);
        use_eq = (uu___318_12978.use_eq);
        is_iface = (uu___318_12978.is_iface);
        admit = (uu___318_12978.admit);
        lax = (uu___318_12978.lax);
        lax_universes = (uu___318_12978.lax_universes);
        phase1 = (uu___318_12978.phase1);
        failhard = (uu___318_12978.failhard);
        nosynth = (uu___318_12978.nosynth);
        uvar_subtyping = (uu___318_12978.uvar_subtyping);
        tc_term = (uu___318_12978.tc_term);
        type_of = (uu___318_12978.type_of);
        universe_of = (uu___318_12978.universe_of);
        check_type_of = (uu___318_12978.check_type_of);
        use_bv_sorts = (uu___318_12978.use_bv_sorts);
        qtbl_name_and_index = (uu___318_12978.qtbl_name_and_index);
        normalized_eff_names = (uu___318_12978.normalized_eff_names);
        fv_delta_depths = (uu___318_12978.fv_delta_depths);
        proof_ns = (uu___318_12978.proof_ns);
        synth_hook = (uu___318_12978.synth_hook);
        try_solve_implicits_hook = (uu___318_12978.try_solve_implicits_hook);
        splice = (uu___318_12978.splice);
        postprocess = (uu___318_12978.postprocess);
        is_native_tactic = (uu___318_12978.is_native_tactic);
        identifier_info = (uu___318_12978.identifier_info);
        tc_hooks = (uu___318_12978.tc_hooks);
        dsenv = (uu___318_12978.dsenv);
        nbe = (uu___318_12978.nbe);
        strict_args_tab = (uu___318_12978.strict_args_tab);
        erasable_types_tab = (uu___318_12978.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12987  -> fun uu____12988  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___325_13010 = env  in
      {
        solver = (uu___325_13010.solver);
        range = (uu___325_13010.range);
        curmodule = (uu___325_13010.curmodule);
        gamma = (uu___325_13010.gamma);
        gamma_sig = (uu___325_13010.gamma_sig);
        gamma_cache = (uu___325_13010.gamma_cache);
        modules = (uu___325_13010.modules);
        expected_typ = (uu___325_13010.expected_typ);
        sigtab = (uu___325_13010.sigtab);
        attrtab = (uu___325_13010.attrtab);
        instantiate_imp = (uu___325_13010.instantiate_imp);
        effects = (uu___325_13010.effects);
        generalize = (uu___325_13010.generalize);
        letrecs = (uu___325_13010.letrecs);
        top_level = (uu___325_13010.top_level);
        check_uvars = (uu___325_13010.check_uvars);
        use_eq = (uu___325_13010.use_eq);
        is_iface = (uu___325_13010.is_iface);
        admit = (uu___325_13010.admit);
        lax = (uu___325_13010.lax);
        lax_universes = (uu___325_13010.lax_universes);
        phase1 = (uu___325_13010.phase1);
        failhard = (uu___325_13010.failhard);
        nosynth = (uu___325_13010.nosynth);
        uvar_subtyping = (uu___325_13010.uvar_subtyping);
        tc_term = (uu___325_13010.tc_term);
        type_of = (uu___325_13010.type_of);
        universe_of = (uu___325_13010.universe_of);
        check_type_of = (uu___325_13010.check_type_of);
        use_bv_sorts = (uu___325_13010.use_bv_sorts);
        qtbl_name_and_index = (uu___325_13010.qtbl_name_and_index);
        normalized_eff_names = (uu___325_13010.normalized_eff_names);
        fv_delta_depths = (uu___325_13010.fv_delta_depths);
        proof_ns = (uu___325_13010.proof_ns);
        synth_hook = (uu___325_13010.synth_hook);
        try_solve_implicits_hook = (uu___325_13010.try_solve_implicits_hook);
        splice = (uu___325_13010.splice);
        postprocess = (uu___325_13010.postprocess);
        is_native_tactic = (uu___325_13010.is_native_tactic);
        identifier_info = (uu___325_13010.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___325_13010.dsenv);
        nbe = (uu___325_13010.nbe);
        strict_args_tab = (uu___325_13010.strict_args_tab);
        erasable_types_tab = (uu___325_13010.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___329_13022 = e  in
      let uu____13023 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___329_13022.solver);
        range = (uu___329_13022.range);
        curmodule = (uu___329_13022.curmodule);
        gamma = (uu___329_13022.gamma);
        gamma_sig = (uu___329_13022.gamma_sig);
        gamma_cache = (uu___329_13022.gamma_cache);
        modules = (uu___329_13022.modules);
        expected_typ = (uu___329_13022.expected_typ);
        sigtab = (uu___329_13022.sigtab);
        attrtab = (uu___329_13022.attrtab);
        instantiate_imp = (uu___329_13022.instantiate_imp);
        effects = (uu___329_13022.effects);
        generalize = (uu___329_13022.generalize);
        letrecs = (uu___329_13022.letrecs);
        top_level = (uu___329_13022.top_level);
        check_uvars = (uu___329_13022.check_uvars);
        use_eq = (uu___329_13022.use_eq);
        is_iface = (uu___329_13022.is_iface);
        admit = (uu___329_13022.admit);
        lax = (uu___329_13022.lax);
        lax_universes = (uu___329_13022.lax_universes);
        phase1 = (uu___329_13022.phase1);
        failhard = (uu___329_13022.failhard);
        nosynth = (uu___329_13022.nosynth);
        uvar_subtyping = (uu___329_13022.uvar_subtyping);
        tc_term = (uu___329_13022.tc_term);
        type_of = (uu___329_13022.type_of);
        universe_of = (uu___329_13022.universe_of);
        check_type_of = (uu___329_13022.check_type_of);
        use_bv_sorts = (uu___329_13022.use_bv_sorts);
        qtbl_name_and_index = (uu___329_13022.qtbl_name_and_index);
        normalized_eff_names = (uu___329_13022.normalized_eff_names);
        fv_delta_depths = (uu___329_13022.fv_delta_depths);
        proof_ns = (uu___329_13022.proof_ns);
        synth_hook = (uu___329_13022.synth_hook);
        try_solve_implicits_hook = (uu___329_13022.try_solve_implicits_hook);
        splice = (uu___329_13022.splice);
        postprocess = (uu___329_13022.postprocess);
        is_native_tactic = (uu___329_13022.is_native_tactic);
        identifier_info = (uu___329_13022.identifier_info);
        tc_hooks = (uu___329_13022.tc_hooks);
        dsenv = uu____13023;
        nbe = (uu___329_13022.nbe);
        strict_args_tab = (uu___329_13022.strict_args_tab);
        erasable_types_tab = (uu___329_13022.erasable_types_tab)
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
      | (NoDelta ,uu____13052) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13055,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13057,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13060 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13074 . unit -> 'Auu____13074 FStar_Util.smap =
  fun uu____13081  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13087 . unit -> 'Auu____13087 FStar_Util.smap =
  fun uu____13094  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13232 = new_gamma_cache ()  in
                  let uu____13235 = new_sigtab ()  in
                  let uu____13238 = new_sigtab ()  in
                  let uu____13245 =
                    let uu____13260 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13260, FStar_Pervasives_Native.None)  in
                  let uu____13281 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13285 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13289 = FStar_Options.using_facts_from ()  in
                  let uu____13290 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13293 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13294 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13308 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13232;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13235;
                    attrtab = uu____13238;
                    instantiate_imp = true;
                    effects = { decls = []; order = []; joins = [] };
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
                    qtbl_name_and_index = uu____13245;
                    normalized_eff_names = uu____13281;
                    fv_delta_depths = uu____13285;
                    proof_ns = uu____13289;
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
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____13381  -> false);
                    identifier_info = uu____13290;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13293;
                    nbe = nbe1;
                    strict_args_tab = uu____13294;
                    erasable_types_tab = uu____13308
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
  fun uu____13460  ->
    let uu____13461 = FStar_ST.op_Bang query_indices  in
    match uu____13461 with
    | [] -> failwith "Empty query indices!"
    | uu____13516 ->
        let uu____13526 =
          let uu____13536 =
            let uu____13544 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13544  in
          let uu____13598 = FStar_ST.op_Bang query_indices  in uu____13536 ::
            uu____13598
           in
        FStar_ST.op_Colon_Equals query_indices uu____13526
  
let (pop_query_indices : unit -> unit) =
  fun uu____13694  ->
    let uu____13695 = FStar_ST.op_Bang query_indices  in
    match uu____13695 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13822  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13859  ->
    match uu____13859 with
    | (l,n1) ->
        let uu____13869 = FStar_ST.op_Bang query_indices  in
        (match uu____13869 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13991 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14014  ->
    let uu____14015 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14015
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14083 =
       let uu____14086 = FStar_ST.op_Bang stack  in env :: uu____14086  in
     FStar_ST.op_Colon_Equals stack uu____14083);
    (let uu___400_14135 = env  in
     let uu____14136 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14139 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14142 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14149 =
       let uu____14164 =
         let uu____14168 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14168  in
       let uu____14200 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14164, uu____14200)  in
     let uu____14249 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14252 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14255 =
       let uu____14258 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14258  in
     let uu____14278 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14291 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___400_14135.solver);
       range = (uu___400_14135.range);
       curmodule = (uu___400_14135.curmodule);
       gamma = (uu___400_14135.gamma);
       gamma_sig = (uu___400_14135.gamma_sig);
       gamma_cache = uu____14136;
       modules = (uu___400_14135.modules);
       expected_typ = (uu___400_14135.expected_typ);
       sigtab = uu____14139;
       attrtab = uu____14142;
       instantiate_imp = (uu___400_14135.instantiate_imp);
       effects = (uu___400_14135.effects);
       generalize = (uu___400_14135.generalize);
       letrecs = (uu___400_14135.letrecs);
       top_level = (uu___400_14135.top_level);
       check_uvars = (uu___400_14135.check_uvars);
       use_eq = (uu___400_14135.use_eq);
       is_iface = (uu___400_14135.is_iface);
       admit = (uu___400_14135.admit);
       lax = (uu___400_14135.lax);
       lax_universes = (uu___400_14135.lax_universes);
       phase1 = (uu___400_14135.phase1);
       failhard = (uu___400_14135.failhard);
       nosynth = (uu___400_14135.nosynth);
       uvar_subtyping = (uu___400_14135.uvar_subtyping);
       tc_term = (uu___400_14135.tc_term);
       type_of = (uu___400_14135.type_of);
       universe_of = (uu___400_14135.universe_of);
       check_type_of = (uu___400_14135.check_type_of);
       use_bv_sorts = (uu___400_14135.use_bv_sorts);
       qtbl_name_and_index = uu____14149;
       normalized_eff_names = uu____14249;
       fv_delta_depths = uu____14252;
       proof_ns = (uu___400_14135.proof_ns);
       synth_hook = (uu___400_14135.synth_hook);
       try_solve_implicits_hook = (uu___400_14135.try_solve_implicits_hook);
       splice = (uu___400_14135.splice);
       postprocess = (uu___400_14135.postprocess);
       is_native_tactic = (uu___400_14135.is_native_tactic);
       identifier_info = uu____14255;
       tc_hooks = (uu___400_14135.tc_hooks);
       dsenv = (uu___400_14135.dsenv);
       nbe = (uu___400_14135.nbe);
       strict_args_tab = uu____14278;
       erasable_types_tab = uu____14291
     })
  
let (pop_stack : unit -> env) =
  fun uu____14301  ->
    let uu____14302 = FStar_ST.op_Bang stack  in
    match uu____14302 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14356 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14446  ->
           let uu____14447 = snapshot_stack env  in
           match uu____14447 with
           | (stack_depth,env1) ->
               let uu____14481 = snapshot_query_indices ()  in
               (match uu____14481 with
                | (query_indices_depth,()) ->
                    let uu____14514 = (env1.solver).snapshot msg  in
                    (match uu____14514 with
                     | (solver_depth,()) ->
                         let uu____14571 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14571 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___425_14638 = env1  in
                                 {
                                   solver = (uu___425_14638.solver);
                                   range = (uu___425_14638.range);
                                   curmodule = (uu___425_14638.curmodule);
                                   gamma = (uu___425_14638.gamma);
                                   gamma_sig = (uu___425_14638.gamma_sig);
                                   gamma_cache = (uu___425_14638.gamma_cache);
                                   modules = (uu___425_14638.modules);
                                   expected_typ =
                                     (uu___425_14638.expected_typ);
                                   sigtab = (uu___425_14638.sigtab);
                                   attrtab = (uu___425_14638.attrtab);
                                   instantiate_imp =
                                     (uu___425_14638.instantiate_imp);
                                   effects = (uu___425_14638.effects);
                                   generalize = (uu___425_14638.generalize);
                                   letrecs = (uu___425_14638.letrecs);
                                   top_level = (uu___425_14638.top_level);
                                   check_uvars = (uu___425_14638.check_uvars);
                                   use_eq = (uu___425_14638.use_eq);
                                   is_iface = (uu___425_14638.is_iface);
                                   admit = (uu___425_14638.admit);
                                   lax = (uu___425_14638.lax);
                                   lax_universes =
                                     (uu___425_14638.lax_universes);
                                   phase1 = (uu___425_14638.phase1);
                                   failhard = (uu___425_14638.failhard);
                                   nosynth = (uu___425_14638.nosynth);
                                   uvar_subtyping =
                                     (uu___425_14638.uvar_subtyping);
                                   tc_term = (uu___425_14638.tc_term);
                                   type_of = (uu___425_14638.type_of);
                                   universe_of = (uu___425_14638.universe_of);
                                   check_type_of =
                                     (uu___425_14638.check_type_of);
                                   use_bv_sorts =
                                     (uu___425_14638.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___425_14638.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___425_14638.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___425_14638.fv_delta_depths);
                                   proof_ns = (uu___425_14638.proof_ns);
                                   synth_hook = (uu___425_14638.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___425_14638.try_solve_implicits_hook);
                                   splice = (uu___425_14638.splice);
                                   postprocess = (uu___425_14638.postprocess);
                                   is_native_tactic =
                                     (uu___425_14638.is_native_tactic);
                                   identifier_info =
                                     (uu___425_14638.identifier_info);
                                   tc_hooks = (uu___425_14638.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___425_14638.nbe);
                                   strict_args_tab =
                                     (uu___425_14638.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___425_14638.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14672  ->
             let uu____14673 =
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
             match uu____14673 with
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
                             ((let uu____14853 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14853
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14869 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14869
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14901,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14943 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14973  ->
                  match uu____14973 with
                  | (m,uu____14981) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14943 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___470_14996 = env  in
               {
                 solver = (uu___470_14996.solver);
                 range = (uu___470_14996.range);
                 curmodule = (uu___470_14996.curmodule);
                 gamma = (uu___470_14996.gamma);
                 gamma_sig = (uu___470_14996.gamma_sig);
                 gamma_cache = (uu___470_14996.gamma_cache);
                 modules = (uu___470_14996.modules);
                 expected_typ = (uu___470_14996.expected_typ);
                 sigtab = (uu___470_14996.sigtab);
                 attrtab = (uu___470_14996.attrtab);
                 instantiate_imp = (uu___470_14996.instantiate_imp);
                 effects = (uu___470_14996.effects);
                 generalize = (uu___470_14996.generalize);
                 letrecs = (uu___470_14996.letrecs);
                 top_level = (uu___470_14996.top_level);
                 check_uvars = (uu___470_14996.check_uvars);
                 use_eq = (uu___470_14996.use_eq);
                 is_iface = (uu___470_14996.is_iface);
                 admit = (uu___470_14996.admit);
                 lax = (uu___470_14996.lax);
                 lax_universes = (uu___470_14996.lax_universes);
                 phase1 = (uu___470_14996.phase1);
                 failhard = (uu___470_14996.failhard);
                 nosynth = (uu___470_14996.nosynth);
                 uvar_subtyping = (uu___470_14996.uvar_subtyping);
                 tc_term = (uu___470_14996.tc_term);
                 type_of = (uu___470_14996.type_of);
                 universe_of = (uu___470_14996.universe_of);
                 check_type_of = (uu___470_14996.check_type_of);
                 use_bv_sorts = (uu___470_14996.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___470_14996.normalized_eff_names);
                 fv_delta_depths = (uu___470_14996.fv_delta_depths);
                 proof_ns = (uu___470_14996.proof_ns);
                 synth_hook = (uu___470_14996.synth_hook);
                 try_solve_implicits_hook =
                   (uu___470_14996.try_solve_implicits_hook);
                 splice = (uu___470_14996.splice);
                 postprocess = (uu___470_14996.postprocess);
                 is_native_tactic = (uu___470_14996.is_native_tactic);
                 identifier_info = (uu___470_14996.identifier_info);
                 tc_hooks = (uu___470_14996.tc_hooks);
                 dsenv = (uu___470_14996.dsenv);
                 nbe = (uu___470_14996.nbe);
                 strict_args_tab = (uu___470_14996.strict_args_tab);
                 erasable_types_tab = (uu___470_14996.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15013,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___479_15029 = env  in
               {
                 solver = (uu___479_15029.solver);
                 range = (uu___479_15029.range);
                 curmodule = (uu___479_15029.curmodule);
                 gamma = (uu___479_15029.gamma);
                 gamma_sig = (uu___479_15029.gamma_sig);
                 gamma_cache = (uu___479_15029.gamma_cache);
                 modules = (uu___479_15029.modules);
                 expected_typ = (uu___479_15029.expected_typ);
                 sigtab = (uu___479_15029.sigtab);
                 attrtab = (uu___479_15029.attrtab);
                 instantiate_imp = (uu___479_15029.instantiate_imp);
                 effects = (uu___479_15029.effects);
                 generalize = (uu___479_15029.generalize);
                 letrecs = (uu___479_15029.letrecs);
                 top_level = (uu___479_15029.top_level);
                 check_uvars = (uu___479_15029.check_uvars);
                 use_eq = (uu___479_15029.use_eq);
                 is_iface = (uu___479_15029.is_iface);
                 admit = (uu___479_15029.admit);
                 lax = (uu___479_15029.lax);
                 lax_universes = (uu___479_15029.lax_universes);
                 phase1 = (uu___479_15029.phase1);
                 failhard = (uu___479_15029.failhard);
                 nosynth = (uu___479_15029.nosynth);
                 uvar_subtyping = (uu___479_15029.uvar_subtyping);
                 tc_term = (uu___479_15029.tc_term);
                 type_of = (uu___479_15029.type_of);
                 universe_of = (uu___479_15029.universe_of);
                 check_type_of = (uu___479_15029.check_type_of);
                 use_bv_sorts = (uu___479_15029.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___479_15029.normalized_eff_names);
                 fv_delta_depths = (uu___479_15029.fv_delta_depths);
                 proof_ns = (uu___479_15029.proof_ns);
                 synth_hook = (uu___479_15029.synth_hook);
                 try_solve_implicits_hook =
                   (uu___479_15029.try_solve_implicits_hook);
                 splice = (uu___479_15029.splice);
                 postprocess = (uu___479_15029.postprocess);
                 is_native_tactic = (uu___479_15029.is_native_tactic);
                 identifier_info = (uu___479_15029.identifier_info);
                 tc_hooks = (uu___479_15029.tc_hooks);
                 dsenv = (uu___479_15029.dsenv);
                 nbe = (uu___479_15029.nbe);
                 strict_args_tab = (uu___479_15029.strict_args_tab);
                 erasable_types_tab = (uu___479_15029.erasable_types_tab)
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
        (let uu___486_15072 = e  in
         {
           solver = (uu___486_15072.solver);
           range = r;
           curmodule = (uu___486_15072.curmodule);
           gamma = (uu___486_15072.gamma);
           gamma_sig = (uu___486_15072.gamma_sig);
           gamma_cache = (uu___486_15072.gamma_cache);
           modules = (uu___486_15072.modules);
           expected_typ = (uu___486_15072.expected_typ);
           sigtab = (uu___486_15072.sigtab);
           attrtab = (uu___486_15072.attrtab);
           instantiate_imp = (uu___486_15072.instantiate_imp);
           effects = (uu___486_15072.effects);
           generalize = (uu___486_15072.generalize);
           letrecs = (uu___486_15072.letrecs);
           top_level = (uu___486_15072.top_level);
           check_uvars = (uu___486_15072.check_uvars);
           use_eq = (uu___486_15072.use_eq);
           is_iface = (uu___486_15072.is_iface);
           admit = (uu___486_15072.admit);
           lax = (uu___486_15072.lax);
           lax_universes = (uu___486_15072.lax_universes);
           phase1 = (uu___486_15072.phase1);
           failhard = (uu___486_15072.failhard);
           nosynth = (uu___486_15072.nosynth);
           uvar_subtyping = (uu___486_15072.uvar_subtyping);
           tc_term = (uu___486_15072.tc_term);
           type_of = (uu___486_15072.type_of);
           universe_of = (uu___486_15072.universe_of);
           check_type_of = (uu___486_15072.check_type_of);
           use_bv_sorts = (uu___486_15072.use_bv_sorts);
           qtbl_name_and_index = (uu___486_15072.qtbl_name_and_index);
           normalized_eff_names = (uu___486_15072.normalized_eff_names);
           fv_delta_depths = (uu___486_15072.fv_delta_depths);
           proof_ns = (uu___486_15072.proof_ns);
           synth_hook = (uu___486_15072.synth_hook);
           try_solve_implicits_hook =
             (uu___486_15072.try_solve_implicits_hook);
           splice = (uu___486_15072.splice);
           postprocess = (uu___486_15072.postprocess);
           is_native_tactic = (uu___486_15072.is_native_tactic);
           identifier_info = (uu___486_15072.identifier_info);
           tc_hooks = (uu___486_15072.tc_hooks);
           dsenv = (uu___486_15072.dsenv);
           nbe = (uu___486_15072.nbe);
           strict_args_tab = (uu___486_15072.strict_args_tab);
           erasable_types_tab = (uu___486_15072.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15092 =
        let uu____15093 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15093 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15092
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15148 =
          let uu____15149 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15149 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15148
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15204 =
          let uu____15205 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15205 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15204
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15260 =
        let uu____15261 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15261 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15260
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___503_15325 = env  in
      {
        solver = (uu___503_15325.solver);
        range = (uu___503_15325.range);
        curmodule = lid;
        gamma = (uu___503_15325.gamma);
        gamma_sig = (uu___503_15325.gamma_sig);
        gamma_cache = (uu___503_15325.gamma_cache);
        modules = (uu___503_15325.modules);
        expected_typ = (uu___503_15325.expected_typ);
        sigtab = (uu___503_15325.sigtab);
        attrtab = (uu___503_15325.attrtab);
        instantiate_imp = (uu___503_15325.instantiate_imp);
        effects = (uu___503_15325.effects);
        generalize = (uu___503_15325.generalize);
        letrecs = (uu___503_15325.letrecs);
        top_level = (uu___503_15325.top_level);
        check_uvars = (uu___503_15325.check_uvars);
        use_eq = (uu___503_15325.use_eq);
        is_iface = (uu___503_15325.is_iface);
        admit = (uu___503_15325.admit);
        lax = (uu___503_15325.lax);
        lax_universes = (uu___503_15325.lax_universes);
        phase1 = (uu___503_15325.phase1);
        failhard = (uu___503_15325.failhard);
        nosynth = (uu___503_15325.nosynth);
        uvar_subtyping = (uu___503_15325.uvar_subtyping);
        tc_term = (uu___503_15325.tc_term);
        type_of = (uu___503_15325.type_of);
        universe_of = (uu___503_15325.universe_of);
        check_type_of = (uu___503_15325.check_type_of);
        use_bv_sorts = (uu___503_15325.use_bv_sorts);
        qtbl_name_and_index = (uu___503_15325.qtbl_name_and_index);
        normalized_eff_names = (uu___503_15325.normalized_eff_names);
        fv_delta_depths = (uu___503_15325.fv_delta_depths);
        proof_ns = (uu___503_15325.proof_ns);
        synth_hook = (uu___503_15325.synth_hook);
        try_solve_implicits_hook = (uu___503_15325.try_solve_implicits_hook);
        splice = (uu___503_15325.splice);
        postprocess = (uu___503_15325.postprocess);
        is_native_tactic = (uu___503_15325.is_native_tactic);
        identifier_info = (uu___503_15325.identifier_info);
        tc_hooks = (uu___503_15325.tc_hooks);
        dsenv = (uu___503_15325.dsenv);
        nbe = (uu___503_15325.nbe);
        strict_args_tab = (uu___503_15325.strict_args_tab);
        erasable_types_tab = (uu___503_15325.erasable_types_tab)
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
      let uu____15356 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15356
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15369 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15369)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15384 =
      let uu____15386 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15386  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15384)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15395  ->
    let uu____15396 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15396
  
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
      | ((formals,t),uu____15496) ->
          let vs = mk_univ_subst formals us  in
          let uu____15520 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15520)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15537  ->
    match uu___1_15537 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15563  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15583 = inst_tscheme t  in
      match uu____15583 with
      | (us,t1) ->
          let uu____15594 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15594)
  
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
          let uu____15619 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15621 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15619 uu____15621
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
        fun uu____15648  ->
          match uu____15648 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15662 =
                    let uu____15664 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15668 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15672 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15674 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15664 uu____15668 uu____15672 uu____15674
                     in
                  failwith uu____15662)
               else ();
               (let uu____15679 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15679))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15697 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15708 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15719 -> false
  
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
             | ([],uu____15767) -> Maybe
             | (uu____15774,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15794 -> No  in
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
          let uu____15888 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15888 with
          | FStar_Pervasives_Native.None  ->
              let uu____15911 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15955  ->
                     match uu___2_15955 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15994 = FStar_Ident.lid_equals lid l  in
                         if uu____15994
                         then
                           let uu____16017 =
                             let uu____16036 =
                               let uu____16051 = inst_tscheme t  in
                               FStar_Util.Inl uu____16051  in
                             let uu____16066 = FStar_Ident.range_of_lid l  in
                             (uu____16036, uu____16066)  in
                           FStar_Pervasives_Native.Some uu____16017
                         else FStar_Pervasives_Native.None
                     | uu____16119 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15911
                (fun uu____16157  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16167  ->
                        match uu___3_16167 with
                        | (uu____16170,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16172);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16173;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16174;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16175;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16176;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16177;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16199 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16199
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
                                  uu____16251 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16258 -> cache t  in
                            let uu____16259 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16259 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16265 =
                                   let uu____16266 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16266)
                                    in
                                 maybe_cache uu____16265)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16337 = find_in_sigtab env lid  in
         match uu____16337 with
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
      let uu____16418 = lookup_qname env lid  in
      match uu____16418 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16439,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16553 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16553 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16598 =
          let uu____16601 = lookup_attr env1 attr  in se1 :: uu____16601  in
        FStar_Util.smap_add (attrtab env1) attr uu____16598  in
      FStar_List.iter
        (fun attr  ->
           let uu____16611 =
             let uu____16612 = FStar_Syntax_Subst.compress attr  in
             uu____16612.FStar_Syntax_Syntax.n  in
           match uu____16611 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16616 =
                 let uu____16618 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16618.FStar_Ident.str  in
               add_one1 env se uu____16616
           | uu____16619 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16642) ->
          add_sigelts env ses
      | uu____16651 ->
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
        (fun uu___4_16689  ->
           match uu___4_16689 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16707 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16769,lb::[]),uu____16771) ->
            let uu____16780 =
              let uu____16789 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16798 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16789, uu____16798)  in
            FStar_Pervasives_Native.Some uu____16780
        | FStar_Syntax_Syntax.Sig_let ((uu____16811,lbs),uu____16813) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16845 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16858 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16858
                     then
                       let uu____16871 =
                         let uu____16880 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16889 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16880, uu____16889)  in
                       FStar_Pervasives_Native.Some uu____16871
                     else FStar_Pervasives_Native.None)
        | uu____16912 -> FStar_Pervasives_Native.None
  
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
                    let uu____17004 =
                      let uu____17006 =
                        let uu____17008 =
                          let uu____17010 =
                            let uu____17012 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17018 =
                              let uu____17020 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17020  in
                            Prims.op_Hat uu____17012 uu____17018  in
                          Prims.op_Hat ", expected " uu____17010  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17008
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17006
                       in
                    failwith uu____17004
                  else ());
             (let uu____17027 =
                let uu____17036 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17036, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17027))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17056,uu____17057) ->
            let uu____17062 =
              let uu____17071 =
                let uu____17076 =
                  let uu____17077 =
                    let uu____17080 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17080  in
                  (us, uu____17077)  in
                inst_ts us_opt uu____17076  in
              (uu____17071, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17062
        | uu____17099 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17188 =
          match uu____17188 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17284,uvs,t,uu____17287,uu____17288,uu____17289);
                      FStar_Syntax_Syntax.sigrng = uu____17290;
                      FStar_Syntax_Syntax.sigquals = uu____17291;
                      FStar_Syntax_Syntax.sigmeta = uu____17292;
                      FStar_Syntax_Syntax.sigattrs = uu____17293;
                      FStar_Syntax_Syntax.sigopts = uu____17294;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17319 =
                     let uu____17328 = inst_tscheme1 (uvs, t)  in
                     (uu____17328, rng)  in
                   FStar_Pervasives_Native.Some uu____17319
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17352;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17354;
                      FStar_Syntax_Syntax.sigattrs = uu____17355;
                      FStar_Syntax_Syntax.sigopts = uu____17356;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17375 =
                     let uu____17377 = in_cur_mod env l  in uu____17377 = Yes
                      in
                   if uu____17375
                   then
                     let uu____17389 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17389
                      then
                        let uu____17405 =
                          let uu____17414 = inst_tscheme1 (uvs, t)  in
                          (uu____17414, rng)  in
                        FStar_Pervasives_Native.Some uu____17405
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17447 =
                        let uu____17456 = inst_tscheme1 (uvs, t)  in
                        (uu____17456, rng)  in
                      FStar_Pervasives_Native.Some uu____17447)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17481,uu____17482);
                      FStar_Syntax_Syntax.sigrng = uu____17483;
                      FStar_Syntax_Syntax.sigquals = uu____17484;
                      FStar_Syntax_Syntax.sigmeta = uu____17485;
                      FStar_Syntax_Syntax.sigattrs = uu____17486;
                      FStar_Syntax_Syntax.sigopts = uu____17487;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17530 =
                          let uu____17539 = inst_tscheme1 (uvs, k)  in
                          (uu____17539, rng)  in
                        FStar_Pervasives_Native.Some uu____17530
                    | uu____17560 ->
                        let uu____17561 =
                          let uu____17570 =
                            let uu____17575 =
                              let uu____17576 =
                                let uu____17579 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17579
                                 in
                              (uvs, uu____17576)  in
                            inst_tscheme1 uu____17575  in
                          (uu____17570, rng)  in
                        FStar_Pervasives_Native.Some uu____17561)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17602,uu____17603);
                      FStar_Syntax_Syntax.sigrng = uu____17604;
                      FStar_Syntax_Syntax.sigquals = uu____17605;
                      FStar_Syntax_Syntax.sigmeta = uu____17606;
                      FStar_Syntax_Syntax.sigattrs = uu____17607;
                      FStar_Syntax_Syntax.sigopts = uu____17608;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17652 =
                          let uu____17661 = inst_tscheme_with (uvs, k) us  in
                          (uu____17661, rng)  in
                        FStar_Pervasives_Native.Some uu____17652
                    | uu____17682 ->
                        let uu____17683 =
                          let uu____17692 =
                            let uu____17697 =
                              let uu____17698 =
                                let uu____17701 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17701
                                 in
                              (uvs, uu____17698)  in
                            inst_tscheme_with uu____17697 us  in
                          (uu____17692, rng)  in
                        FStar_Pervasives_Native.Some uu____17683)
               | FStar_Util.Inr se ->
                   let uu____17737 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17758;
                          FStar_Syntax_Syntax.sigrng = uu____17759;
                          FStar_Syntax_Syntax.sigquals = uu____17760;
                          FStar_Syntax_Syntax.sigmeta = uu____17761;
                          FStar_Syntax_Syntax.sigattrs = uu____17762;
                          FStar_Syntax_Syntax.sigopts = uu____17763;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17780 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17737
                     (FStar_Util.map_option
                        (fun uu____17828  ->
                           match uu____17828 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17859 =
          let uu____17870 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17870 mapper  in
        match uu____17859 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17944 =
              let uu____17955 =
                let uu____17962 =
                  let uu___840_17965 = t  in
                  let uu____17966 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___840_17965.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17966;
                    FStar_Syntax_Syntax.vars =
                      (uu___840_17965.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17962)  in
              (uu____17955, r)  in
            FStar_Pervasives_Native.Some uu____17944
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18015 = lookup_qname env l  in
      match uu____18015 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18036 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18090 = try_lookup_bv env bv  in
      match uu____18090 with
      | FStar_Pervasives_Native.None  ->
          let uu____18105 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18105 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18121 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18122 =
            let uu____18123 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18123  in
          (uu____18121, uu____18122)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18145 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18145 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18211 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18211  in
          let uu____18212 =
            let uu____18221 =
              let uu____18226 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18226)  in
            (uu____18221, r1)  in
          FStar_Pervasives_Native.Some uu____18212
  
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
        let uu____18261 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18261 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18294,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18319 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18319  in
            let uu____18320 =
              let uu____18325 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18325, r1)  in
            FStar_Pervasives_Native.Some uu____18320
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18349 = try_lookup_lid env l  in
      match uu____18349 with
      | FStar_Pervasives_Native.None  ->
          let uu____18376 = name_not_found l  in
          let uu____18382 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18376 uu____18382
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18425  ->
              match uu___5_18425 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18429 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18450 = lookup_qname env lid  in
      match uu____18450 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18459,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18462;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18464;
              FStar_Syntax_Syntax.sigattrs = uu____18465;
              FStar_Syntax_Syntax.sigopts = uu____18466;_},FStar_Pervasives_Native.None
            ),uu____18467)
          ->
          let uu____18518 =
            let uu____18525 =
              let uu____18526 =
                let uu____18529 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18529 t  in
              (uvs, uu____18526)  in
            (uu____18525, q)  in
          FStar_Pervasives_Native.Some uu____18518
      | uu____18542 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18564 = lookup_qname env lid  in
      match uu____18564 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18569,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18572;
              FStar_Syntax_Syntax.sigquals = uu____18573;
              FStar_Syntax_Syntax.sigmeta = uu____18574;
              FStar_Syntax_Syntax.sigattrs = uu____18575;
              FStar_Syntax_Syntax.sigopts = uu____18576;_},FStar_Pervasives_Native.None
            ),uu____18577)
          ->
          let uu____18628 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18628 (uvs, t)
      | uu____18633 ->
          let uu____18634 = name_not_found lid  in
          let uu____18640 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18634 uu____18640
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18660 = lookup_qname env lid  in
      match uu____18660 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18665,uvs,t,uu____18668,uu____18669,uu____18670);
              FStar_Syntax_Syntax.sigrng = uu____18671;
              FStar_Syntax_Syntax.sigquals = uu____18672;
              FStar_Syntax_Syntax.sigmeta = uu____18673;
              FStar_Syntax_Syntax.sigattrs = uu____18674;
              FStar_Syntax_Syntax.sigopts = uu____18675;_},FStar_Pervasives_Native.None
            ),uu____18676)
          ->
          let uu____18733 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18733 (uvs, t)
      | uu____18738 ->
          let uu____18739 = name_not_found lid  in
          let uu____18745 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18739 uu____18745
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18768 = lookup_qname env lid  in
      match uu____18768 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18776,uu____18777,uu____18778,uu____18779,uu____18780,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18782;
              FStar_Syntax_Syntax.sigquals = uu____18783;
              FStar_Syntax_Syntax.sigmeta = uu____18784;
              FStar_Syntax_Syntax.sigattrs = uu____18785;
              FStar_Syntax_Syntax.sigopts = uu____18786;_},uu____18787),uu____18788)
          -> (true, dcs)
      | uu____18853 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18869 = lookup_qname env lid  in
      match uu____18869 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18870,uu____18871,uu____18872,l,uu____18874,uu____18875);
              FStar_Syntax_Syntax.sigrng = uu____18876;
              FStar_Syntax_Syntax.sigquals = uu____18877;
              FStar_Syntax_Syntax.sigmeta = uu____18878;
              FStar_Syntax_Syntax.sigattrs = uu____18879;
              FStar_Syntax_Syntax.sigopts = uu____18880;_},uu____18881),uu____18882)
          -> l
      | uu____18941 ->
          let uu____18942 =
            let uu____18944 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18944  in
          failwith uu____18942
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19014)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19071) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19095 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19095
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19130 -> FStar_Pervasives_Native.None)
          | uu____19139 -> FStar_Pervasives_Native.None
  
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
        let uu____19201 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19201
  
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
        let uu____19234 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19234
  
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
             (FStar_Util.Inl uu____19286,uu____19287) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19336),uu____19337) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19386 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19404 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19414 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19431 ->
                  let uu____19438 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19438
              | FStar_Syntax_Syntax.Sig_let ((uu____19439,lbs),uu____19441)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19457 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19457
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19464 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19472 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19473 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19480 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19481 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19482 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19483 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19496 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19514 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19514
           (fun d_opt  ->
              let uu____19527 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19527
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19537 =
                   let uu____19540 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19540  in
                 match uu____19537 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19541 =
                       let uu____19543 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19543
                        in
                     failwith uu____19541
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19548 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19548
                       then
                         let uu____19551 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19553 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19555 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19551 uu____19553 uu____19555
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
        (FStar_Util.Inr (se,uu____19580),uu____19581) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19630 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19652),uu____19653) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19702 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19724 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19724
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19757 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19757 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19779 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19788 =
                        let uu____19789 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19789.FStar_Syntax_Syntax.n  in
                      match uu____19788 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19794 -> false))
               in
            (true, uu____19779)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19817 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19817
  
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
          let uu____19889 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19889.FStar_Ident.str  in
        let uu____19890 = FStar_Util.smap_try_find tab s  in
        match uu____19890 with
        | FStar_Pervasives_Native.None  ->
            let uu____19893 = f ()  in
            (match uu____19893 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____19931 =
        let uu____19932 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____19932 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19966 =
        let uu____19967 = FStar_Syntax_Util.unrefine t  in
        uu____19967.FStar_Syntax_Syntax.n  in
      match uu____19966 with
      | FStar_Syntax_Syntax.Tm_type uu____19971 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____19975) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20001) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20006,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20028 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20061 =
        let attrs =
          let uu____20067 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20067  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20107 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20107)
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
      let uu____20152 = lookup_qname env ftv  in
      match uu____20152 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20156) ->
          let uu____20201 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20201 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20222,t),r) ->
               let uu____20237 =
                 let uu____20238 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20238 t  in
               FStar_Pervasives_Native.Some uu____20237)
      | uu____20239 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20251 = try_lookup_effect_lid env ftv  in
      match uu____20251 with
      | FStar_Pervasives_Native.None  ->
          let uu____20254 = name_not_found ftv  in
          let uu____20260 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20254 uu____20260
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
        let uu____20284 = lookup_qname env lid0  in
        match uu____20284 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20295);
                FStar_Syntax_Syntax.sigrng = uu____20296;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20298;
                FStar_Syntax_Syntax.sigattrs = uu____20299;
                FStar_Syntax_Syntax.sigopts = uu____20300;_},FStar_Pervasives_Native.None
              ),uu____20301)
            ->
            let lid1 =
              let uu____20357 =
                let uu____20358 = FStar_Ident.range_of_lid lid  in
                let uu____20359 =
                  let uu____20360 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20360  in
                FStar_Range.set_use_range uu____20358 uu____20359  in
              FStar_Ident.set_lid_range lid uu____20357  in
            let uu____20361 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20367  ->
                      match uu___6_20367 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20370 -> false))
               in
            if uu____20361
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20389 =
                      let uu____20391 =
                        let uu____20393 = get_range env  in
                        FStar_Range.string_of_range uu____20393  in
                      let uu____20394 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20396 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20391 uu____20394 uu____20396
                       in
                    failwith uu____20389)
                  in
               match (binders, univs1) with
               | ([],uu____20417) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20443,uu____20444::uu____20445::uu____20446) ->
                   let uu____20467 =
                     let uu____20469 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20471 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20469 uu____20471
                      in
                   failwith uu____20467
               | uu____20482 ->
                   let uu____20497 =
                     let uu____20502 =
                       let uu____20503 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20503)  in
                     inst_tscheme_with uu____20502 insts  in
                   (match uu____20497 with
                    | (uu____20516,t) ->
                        let t1 =
                          let uu____20519 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20519 t  in
                        let uu____20520 =
                          let uu____20521 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20521.FStar_Syntax_Syntax.n  in
                        (match uu____20520 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20556 -> failwith "Impossible")))
        | uu____20564 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20588 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20588 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20601,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20608 = find1 l2  in
            (match uu____20608 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20615 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20615 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20619 = find1 l  in
            (match uu____20619 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20624 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20624
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____20645 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____20645 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____20651) ->
            FStar_List.length bs
        | uu____20690 ->
            let uu____20691 =
              let uu____20697 =
                let uu____20699 = FStar_Ident.string_of_lid name  in
                let uu____20701 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20699 uu____20701
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20697)
               in
            FStar_Errors.raise_error uu____20691 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20720 = lookup_qname env l1  in
      match uu____20720 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20723;
              FStar_Syntax_Syntax.sigrng = uu____20724;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20726;
              FStar_Syntax_Syntax.sigattrs = uu____20727;
              FStar_Syntax_Syntax.sigopts = uu____20728;_},uu____20729),uu____20730)
          -> q
      | uu____20783 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20807 =
          let uu____20808 =
            let uu____20810 = FStar_Util.string_of_int i  in
            let uu____20812 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20810 uu____20812
             in
          failwith uu____20808  in
        let uu____20815 = lookup_datacon env lid  in
        match uu____20815 with
        | (uu____20820,t) ->
            let uu____20822 =
              let uu____20823 = FStar_Syntax_Subst.compress t  in
              uu____20823.FStar_Syntax_Syntax.n  in
            (match uu____20822 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20827) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20871 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20871
                      FStar_Pervasives_Native.fst)
             | uu____20882 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20896 = lookup_qname env l  in
      match uu____20896 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20898,uu____20899,uu____20900);
              FStar_Syntax_Syntax.sigrng = uu____20901;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20903;
              FStar_Syntax_Syntax.sigattrs = uu____20904;
              FStar_Syntax_Syntax.sigopts = uu____20905;_},uu____20906),uu____20907)
          ->
          FStar_Util.for_some
            (fun uu___7_20962  ->
               match uu___7_20962 with
               | FStar_Syntax_Syntax.Projector uu____20964 -> true
               | uu____20970 -> false) quals
      | uu____20972 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20986 = lookup_qname env lid  in
      match uu____20986 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20988,uu____20989,uu____20990,uu____20991,uu____20992,uu____20993);
              FStar_Syntax_Syntax.sigrng = uu____20994;
              FStar_Syntax_Syntax.sigquals = uu____20995;
              FStar_Syntax_Syntax.sigmeta = uu____20996;
              FStar_Syntax_Syntax.sigattrs = uu____20997;
              FStar_Syntax_Syntax.sigopts = uu____20998;_},uu____20999),uu____21000)
          -> true
      | uu____21060 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21074 = lookup_qname env lid  in
      match uu____21074 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21076,uu____21077,uu____21078,uu____21079,uu____21080,uu____21081);
              FStar_Syntax_Syntax.sigrng = uu____21082;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21084;
              FStar_Syntax_Syntax.sigattrs = uu____21085;
              FStar_Syntax_Syntax.sigopts = uu____21086;_},uu____21087),uu____21088)
          ->
          FStar_Util.for_some
            (fun uu___8_21151  ->
               match uu___8_21151 with
               | FStar_Syntax_Syntax.RecordType uu____21153 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21163 -> true
               | uu____21173 -> false) quals
      | uu____21175 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21185,uu____21186);
            FStar_Syntax_Syntax.sigrng = uu____21187;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21189;
            FStar_Syntax_Syntax.sigattrs = uu____21190;
            FStar_Syntax_Syntax.sigopts = uu____21191;_},uu____21192),uu____21193)
        ->
        FStar_Util.for_some
          (fun uu___9_21252  ->
             match uu___9_21252 with
             | FStar_Syntax_Syntax.Action uu____21254 -> true
             | uu____21256 -> false) quals
    | uu____21258 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21272 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21272
  
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
      let uu____21289 =
        let uu____21290 = FStar_Syntax_Util.un_uinst head1  in
        uu____21290.FStar_Syntax_Syntax.n  in
      match uu____21289 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21296 ->
               true
           | uu____21299 -> false)
      | uu____21301 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21315 = lookup_qname env l  in
      match uu____21315 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21318),uu____21319) ->
          FStar_Util.for_some
            (fun uu___10_21367  ->
               match uu___10_21367 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21370 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21372 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21448 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21466) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21484 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21492 ->
                 FStar_Pervasives_Native.Some true
             | uu____21511 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21514 =
        let uu____21518 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21518 mapper  in
      match uu____21514 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21578 = lookup_qname env lid  in
      match uu____21578 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21582,uu____21583,tps,uu____21585,uu____21586,uu____21587);
              FStar_Syntax_Syntax.sigrng = uu____21588;
              FStar_Syntax_Syntax.sigquals = uu____21589;
              FStar_Syntax_Syntax.sigmeta = uu____21590;
              FStar_Syntax_Syntax.sigattrs = uu____21591;
              FStar_Syntax_Syntax.sigopts = uu____21592;_},uu____21593),uu____21594)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21662 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21708  ->
              match uu____21708 with
              | (d,uu____21717) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21733 = effect_decl_opt env l  in
      match uu____21733 with
      | FStar_Pervasives_Native.None  ->
          let uu____21748 = name_not_found l  in
          let uu____21754 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21748 uu____21754
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21782 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____21782
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____21791  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21805  ->
            fun uu____21806  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21836 = FStar_Ident.lid_equals l1 l2  in
        if uu____21836
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21847 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21847
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21858 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21911  ->
                        match uu____21911 with
                        | (m1,m2,uu____21925,uu____21926,uu____21927) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21858 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21944 =
                    let uu____21950 =
                      let uu____21952 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21954 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21952
                        uu____21954
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21950)
                     in
                  FStar_Errors.raise_error uu____21944 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21964,uu____21965,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21999 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21999
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
  'Auu____22019 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22019) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22048 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22074  ->
                match uu____22074 with
                | (d,uu____22081) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22048 with
      | FStar_Pervasives_Native.None  ->
          let uu____22092 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22092
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22107 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22107 with
           | (uu____22118,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22136)::(wp,uu____22138)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22194 -> failwith "Impossible"))
  
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
        | uu____22259 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22272 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22272 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22289 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22289 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22314 =
                     let uu____22320 =
                       let uu____22322 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22330 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22341 =
                         let uu____22343 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22343  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22322 uu____22330 uu____22341
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22320)
                      in
                   FStar_Errors.raise_error uu____22314
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22351 =
                     let uu____22362 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22362 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22399  ->
                        fun uu____22400  ->
                          match (uu____22399, uu____22400) with
                          | ((x,uu____22430),(t,uu____22432)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22351
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22463 =
                     let uu___1589_22464 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1589_22464.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1589_22464.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1589_22464.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1589_22464.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22463
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22476 .
    'Auu____22476 ->
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
            let uu____22517 =
              let uu____22524 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____22524)  in
            match uu____22517 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____22548 = FStar_Ident.string_of_lid eff_name  in
                     let uu____22550 = FStar_Util.string_of_int given  in
                     let uu____22552 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____22548 uu____22550 uu____22552
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____22557 = effect_decl_opt env effect_name  in
          match uu____22557 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____22579) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22600 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr =
                     inst_effect_fun_with [u_res] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____22607 =
                       let uu____22610 = get_range env  in
                       let uu____22611 =
                         let uu____22618 =
                           let uu____22619 =
                             let uu____22636 =
                               let uu____22647 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____22647 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____22636)  in
                           FStar_Syntax_Syntax.Tm_app uu____22619  in
                         FStar_Syntax_Syntax.mk uu____22618  in
                       uu____22611 FStar_Pervasives_Native.None uu____22610
                        in
                     FStar_Pervasives_Native.Some uu____22607)))
  
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
           (fun uu___11_22747  ->
              match uu___11_22747 with
              | FStar_Syntax_Syntax.Reflectable uu____22749 -> true
              | uu____22751 -> false))
  
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
      | uu____22811 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22826 =
        let uu____22827 = FStar_Syntax_Subst.compress t  in
        uu____22827.FStar_Syntax_Syntax.n  in
      match uu____22826 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22831,c) ->
          is_reifiable_comp env c
      | uu____22853 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22873 =
           let uu____22875 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22875  in
         if uu____22873
         then
           let uu____22878 =
             let uu____22884 =
               let uu____22886 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22886
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22884)  in
           let uu____22890 = get_range env  in
           FStar_Errors.raise_error uu____22878 uu____22890
         else ());
        (let uu____22893 = effect_repr_aux true env c u_c  in
         match uu____22893 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1665_22929 = env  in
        {
          solver = (uu___1665_22929.solver);
          range = (uu___1665_22929.range);
          curmodule = (uu___1665_22929.curmodule);
          gamma = (uu___1665_22929.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1665_22929.gamma_cache);
          modules = (uu___1665_22929.modules);
          expected_typ = (uu___1665_22929.expected_typ);
          sigtab = (uu___1665_22929.sigtab);
          attrtab = (uu___1665_22929.attrtab);
          instantiate_imp = (uu___1665_22929.instantiate_imp);
          effects = (uu___1665_22929.effects);
          generalize = (uu___1665_22929.generalize);
          letrecs = (uu___1665_22929.letrecs);
          top_level = (uu___1665_22929.top_level);
          check_uvars = (uu___1665_22929.check_uvars);
          use_eq = (uu___1665_22929.use_eq);
          is_iface = (uu___1665_22929.is_iface);
          admit = (uu___1665_22929.admit);
          lax = (uu___1665_22929.lax);
          lax_universes = (uu___1665_22929.lax_universes);
          phase1 = (uu___1665_22929.phase1);
          failhard = (uu___1665_22929.failhard);
          nosynth = (uu___1665_22929.nosynth);
          uvar_subtyping = (uu___1665_22929.uvar_subtyping);
          tc_term = (uu___1665_22929.tc_term);
          type_of = (uu___1665_22929.type_of);
          universe_of = (uu___1665_22929.universe_of);
          check_type_of = (uu___1665_22929.check_type_of);
          use_bv_sorts = (uu___1665_22929.use_bv_sorts);
          qtbl_name_and_index = (uu___1665_22929.qtbl_name_and_index);
          normalized_eff_names = (uu___1665_22929.normalized_eff_names);
          fv_delta_depths = (uu___1665_22929.fv_delta_depths);
          proof_ns = (uu___1665_22929.proof_ns);
          synth_hook = (uu___1665_22929.synth_hook);
          try_solve_implicits_hook =
            (uu___1665_22929.try_solve_implicits_hook);
          splice = (uu___1665_22929.splice);
          postprocess = (uu___1665_22929.postprocess);
          is_native_tactic = (uu___1665_22929.is_native_tactic);
          identifier_info = (uu___1665_22929.identifier_info);
          tc_hooks = (uu___1665_22929.tc_hooks);
          dsenv = (uu___1665_22929.dsenv);
          nbe = (uu___1665_22929.nbe);
          strict_args_tab = (uu___1665_22929.strict_args_tab);
          erasable_types_tab = (uu___1665_22929.erasable_types_tab)
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
    fun uu____22948  ->
      match uu____22948 with
      | (ed,quals) ->
          let effects =
            let uu___1674_22962 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1674_22962.order);
              joins = (uu___1674_22962.joins)
            }  in
          let uu___1677_22971 = env  in
          {
            solver = (uu___1677_22971.solver);
            range = (uu___1677_22971.range);
            curmodule = (uu___1677_22971.curmodule);
            gamma = (uu___1677_22971.gamma);
            gamma_sig = (uu___1677_22971.gamma_sig);
            gamma_cache = (uu___1677_22971.gamma_cache);
            modules = (uu___1677_22971.modules);
            expected_typ = (uu___1677_22971.expected_typ);
            sigtab = (uu___1677_22971.sigtab);
            attrtab = (uu___1677_22971.attrtab);
            instantiate_imp = (uu___1677_22971.instantiate_imp);
            effects;
            generalize = (uu___1677_22971.generalize);
            letrecs = (uu___1677_22971.letrecs);
            top_level = (uu___1677_22971.top_level);
            check_uvars = (uu___1677_22971.check_uvars);
            use_eq = (uu___1677_22971.use_eq);
            is_iface = (uu___1677_22971.is_iface);
            admit = (uu___1677_22971.admit);
            lax = (uu___1677_22971.lax);
            lax_universes = (uu___1677_22971.lax_universes);
            phase1 = (uu___1677_22971.phase1);
            failhard = (uu___1677_22971.failhard);
            nosynth = (uu___1677_22971.nosynth);
            uvar_subtyping = (uu___1677_22971.uvar_subtyping);
            tc_term = (uu___1677_22971.tc_term);
            type_of = (uu___1677_22971.type_of);
            universe_of = (uu___1677_22971.universe_of);
            check_type_of = (uu___1677_22971.check_type_of);
            use_bv_sorts = (uu___1677_22971.use_bv_sorts);
            qtbl_name_and_index = (uu___1677_22971.qtbl_name_and_index);
            normalized_eff_names = (uu___1677_22971.normalized_eff_names);
            fv_delta_depths = (uu___1677_22971.fv_delta_depths);
            proof_ns = (uu___1677_22971.proof_ns);
            synth_hook = (uu___1677_22971.synth_hook);
            try_solve_implicits_hook =
              (uu___1677_22971.try_solve_implicits_hook);
            splice = (uu___1677_22971.splice);
            postprocess = (uu___1677_22971.postprocess);
            is_native_tactic = (uu___1677_22971.is_native_tactic);
            identifier_info = (uu___1677_22971.identifier_info);
            tc_hooks = (uu___1677_22971.tc_hooks);
            dsenv = (uu___1677_22971.dsenv);
            nbe = (uu___1677_22971.nbe);
            strict_args_tab = (uu___1677_22971.strict_args_tab);
            erasable_types_tab = (uu___1677_22971.erasable_types_tab)
          }
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____23020 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____23020
                  (fun uu____23041  ->
                     match uu____23041 with
                     | (c1,g1) ->
                         let uu____23052 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____23052
                           (fun uu____23073  ->
                              match uu____23073 with
                              | (c2,g2) ->
                                  let uu____23084 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____23084)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____23206 = l1 u t e  in
                              l2 u t uu____23206))
                | uu____23207 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____23275  ->
                    match uu____23275 with
                    | (e,uu____23283) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____23306 =
            match uu____23306 with
            | (i,j) ->
                let uu____23317 = FStar_Ident.lid_equals i j  in
                if uu____23317
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _23324  -> FStar_Pervasives_Native.Some _23324)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____23353 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____23363 = FStar_Ident.lid_equals i k  in
                        if uu____23363
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____23377 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____23377
                                  then []
                                  else
                                    (let uu____23384 =
                                       let uu____23393 =
                                         find_edge order1 (i, k)  in
                                       let uu____23396 =
                                         find_edge order1 (k, j)  in
                                       (uu____23393, uu____23396)  in
                                     match uu____23384 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____23411 =
                                           compose_edges e1 e2  in
                                         [uu____23411]
                                     | uu____23412 -> [])))))
                 in
              FStar_List.append order1 uu____23353  in
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
                  let uu____23442 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____23445 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____23445
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____23442
                  then
                    let uu____23452 =
                      let uu____23458 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____23458)
                       in
                    let uu____23462 = get_range env  in
                    FStar_Errors.raise_error uu____23452 uu____23462
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt =
                               let uu____23540 = FStar_Ident.lid_equals i j
                                  in
                               if uu____23540
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____23592 =
                                             let uu____23601 =
                                               find_edge order2 (i, k)  in
                                             let uu____23604 =
                                               find_edge order2 (j, k)  in
                                             (uu____23601, uu____23604)  in
                                           match uu____23592 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____23646,uu____23647)
                                                    ->
                                                    let uu____23654 =
                                                      let uu____23661 =
                                                        let uu____23663 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23663
                                                         in
                                                      let uu____23666 =
                                                        let uu____23668 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23668
                                                         in
                                                      (uu____23661,
                                                        uu____23666)
                                                       in
                                                    (match uu____23654 with
                                                     | (true ,true ) ->
                                                         let uu____23685 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____23685
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
                                           | uu____23728 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1782_23801 = env.effects  in
             { decls = (uu___1782_23801.decls); order = order2; joins }  in
           let uu___1785_23802 = env  in
           {
             solver = (uu___1785_23802.solver);
             range = (uu___1785_23802.range);
             curmodule = (uu___1785_23802.curmodule);
             gamma = (uu___1785_23802.gamma);
             gamma_sig = (uu___1785_23802.gamma_sig);
             gamma_cache = (uu___1785_23802.gamma_cache);
             modules = (uu___1785_23802.modules);
             expected_typ = (uu___1785_23802.expected_typ);
             sigtab = (uu___1785_23802.sigtab);
             attrtab = (uu___1785_23802.attrtab);
             instantiate_imp = (uu___1785_23802.instantiate_imp);
             effects;
             generalize = (uu___1785_23802.generalize);
             letrecs = (uu___1785_23802.letrecs);
             top_level = (uu___1785_23802.top_level);
             check_uvars = (uu___1785_23802.check_uvars);
             use_eq = (uu___1785_23802.use_eq);
             is_iface = (uu___1785_23802.is_iface);
             admit = (uu___1785_23802.admit);
             lax = (uu___1785_23802.lax);
             lax_universes = (uu___1785_23802.lax_universes);
             phase1 = (uu___1785_23802.phase1);
             failhard = (uu___1785_23802.failhard);
             nosynth = (uu___1785_23802.nosynth);
             uvar_subtyping = (uu___1785_23802.uvar_subtyping);
             tc_term = (uu___1785_23802.tc_term);
             type_of = (uu___1785_23802.type_of);
             universe_of = (uu___1785_23802.universe_of);
             check_type_of = (uu___1785_23802.check_type_of);
             use_bv_sorts = (uu___1785_23802.use_bv_sorts);
             qtbl_name_and_index = (uu___1785_23802.qtbl_name_and_index);
             normalized_eff_names = (uu___1785_23802.normalized_eff_names);
             fv_delta_depths = (uu___1785_23802.fv_delta_depths);
             proof_ns = (uu___1785_23802.proof_ns);
             synth_hook = (uu___1785_23802.synth_hook);
             try_solve_implicits_hook =
               (uu___1785_23802.try_solve_implicits_hook);
             splice = (uu___1785_23802.splice);
             postprocess = (uu___1785_23802.postprocess);
             is_native_tactic = (uu___1785_23802.is_native_tactic);
             identifier_info = (uu___1785_23802.identifier_info);
             tc_hooks = (uu___1785_23802.tc_hooks);
             dsenv = (uu___1785_23802.dsenv);
             nbe = (uu___1785_23802.nbe);
             strict_args_tab = (uu___1785_23802.strict_args_tab);
             erasable_types_tab = (uu___1785_23802.erasable_types_tab)
           })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1789_23814 = env  in
      {
        solver = (uu___1789_23814.solver);
        range = (uu___1789_23814.range);
        curmodule = (uu___1789_23814.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1789_23814.gamma_sig);
        gamma_cache = (uu___1789_23814.gamma_cache);
        modules = (uu___1789_23814.modules);
        expected_typ = (uu___1789_23814.expected_typ);
        sigtab = (uu___1789_23814.sigtab);
        attrtab = (uu___1789_23814.attrtab);
        instantiate_imp = (uu___1789_23814.instantiate_imp);
        effects = (uu___1789_23814.effects);
        generalize = (uu___1789_23814.generalize);
        letrecs = (uu___1789_23814.letrecs);
        top_level = (uu___1789_23814.top_level);
        check_uvars = (uu___1789_23814.check_uvars);
        use_eq = (uu___1789_23814.use_eq);
        is_iface = (uu___1789_23814.is_iface);
        admit = (uu___1789_23814.admit);
        lax = (uu___1789_23814.lax);
        lax_universes = (uu___1789_23814.lax_universes);
        phase1 = (uu___1789_23814.phase1);
        failhard = (uu___1789_23814.failhard);
        nosynth = (uu___1789_23814.nosynth);
        uvar_subtyping = (uu___1789_23814.uvar_subtyping);
        tc_term = (uu___1789_23814.tc_term);
        type_of = (uu___1789_23814.type_of);
        universe_of = (uu___1789_23814.universe_of);
        check_type_of = (uu___1789_23814.check_type_of);
        use_bv_sorts = (uu___1789_23814.use_bv_sorts);
        qtbl_name_and_index = (uu___1789_23814.qtbl_name_and_index);
        normalized_eff_names = (uu___1789_23814.normalized_eff_names);
        fv_delta_depths = (uu___1789_23814.fv_delta_depths);
        proof_ns = (uu___1789_23814.proof_ns);
        synth_hook = (uu___1789_23814.synth_hook);
        try_solve_implicits_hook = (uu___1789_23814.try_solve_implicits_hook);
        splice = (uu___1789_23814.splice);
        postprocess = (uu___1789_23814.postprocess);
        is_native_tactic = (uu___1789_23814.is_native_tactic);
        identifier_info = (uu___1789_23814.identifier_info);
        tc_hooks = (uu___1789_23814.tc_hooks);
        dsenv = (uu___1789_23814.dsenv);
        nbe = (uu___1789_23814.nbe);
        strict_args_tab = (uu___1789_23814.strict_args_tab);
        erasable_types_tab = (uu___1789_23814.erasable_types_tab)
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
            (let uu___1802_23872 = env  in
             {
               solver = (uu___1802_23872.solver);
               range = (uu___1802_23872.range);
               curmodule = (uu___1802_23872.curmodule);
               gamma = rest;
               gamma_sig = (uu___1802_23872.gamma_sig);
               gamma_cache = (uu___1802_23872.gamma_cache);
               modules = (uu___1802_23872.modules);
               expected_typ = (uu___1802_23872.expected_typ);
               sigtab = (uu___1802_23872.sigtab);
               attrtab = (uu___1802_23872.attrtab);
               instantiate_imp = (uu___1802_23872.instantiate_imp);
               effects = (uu___1802_23872.effects);
               generalize = (uu___1802_23872.generalize);
               letrecs = (uu___1802_23872.letrecs);
               top_level = (uu___1802_23872.top_level);
               check_uvars = (uu___1802_23872.check_uvars);
               use_eq = (uu___1802_23872.use_eq);
               is_iface = (uu___1802_23872.is_iface);
               admit = (uu___1802_23872.admit);
               lax = (uu___1802_23872.lax);
               lax_universes = (uu___1802_23872.lax_universes);
               phase1 = (uu___1802_23872.phase1);
               failhard = (uu___1802_23872.failhard);
               nosynth = (uu___1802_23872.nosynth);
               uvar_subtyping = (uu___1802_23872.uvar_subtyping);
               tc_term = (uu___1802_23872.tc_term);
               type_of = (uu___1802_23872.type_of);
               universe_of = (uu___1802_23872.universe_of);
               check_type_of = (uu___1802_23872.check_type_of);
               use_bv_sorts = (uu___1802_23872.use_bv_sorts);
               qtbl_name_and_index = (uu___1802_23872.qtbl_name_and_index);
               normalized_eff_names = (uu___1802_23872.normalized_eff_names);
               fv_delta_depths = (uu___1802_23872.fv_delta_depths);
               proof_ns = (uu___1802_23872.proof_ns);
               synth_hook = (uu___1802_23872.synth_hook);
               try_solve_implicits_hook =
                 (uu___1802_23872.try_solve_implicits_hook);
               splice = (uu___1802_23872.splice);
               postprocess = (uu___1802_23872.postprocess);
               is_native_tactic = (uu___1802_23872.is_native_tactic);
               identifier_info = (uu___1802_23872.identifier_info);
               tc_hooks = (uu___1802_23872.tc_hooks);
               dsenv = (uu___1802_23872.dsenv);
               nbe = (uu___1802_23872.nbe);
               strict_args_tab = (uu___1802_23872.strict_args_tab);
               erasable_types_tab = (uu___1802_23872.erasable_types_tab)
             }))
    | uu____23873 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23902  ->
             match uu____23902 with | (x,uu____23910) -> push_bv env1 x) env
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
            let uu___1816_23945 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1816_23945.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1816_23945.FStar_Syntax_Syntax.index);
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
        let uu____24018 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24018 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24046 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24046)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1837_24062 = env  in
      {
        solver = (uu___1837_24062.solver);
        range = (uu___1837_24062.range);
        curmodule = (uu___1837_24062.curmodule);
        gamma = (uu___1837_24062.gamma);
        gamma_sig = (uu___1837_24062.gamma_sig);
        gamma_cache = (uu___1837_24062.gamma_cache);
        modules = (uu___1837_24062.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1837_24062.sigtab);
        attrtab = (uu___1837_24062.attrtab);
        instantiate_imp = (uu___1837_24062.instantiate_imp);
        effects = (uu___1837_24062.effects);
        generalize = (uu___1837_24062.generalize);
        letrecs = (uu___1837_24062.letrecs);
        top_level = (uu___1837_24062.top_level);
        check_uvars = (uu___1837_24062.check_uvars);
        use_eq = false;
        is_iface = (uu___1837_24062.is_iface);
        admit = (uu___1837_24062.admit);
        lax = (uu___1837_24062.lax);
        lax_universes = (uu___1837_24062.lax_universes);
        phase1 = (uu___1837_24062.phase1);
        failhard = (uu___1837_24062.failhard);
        nosynth = (uu___1837_24062.nosynth);
        uvar_subtyping = (uu___1837_24062.uvar_subtyping);
        tc_term = (uu___1837_24062.tc_term);
        type_of = (uu___1837_24062.type_of);
        universe_of = (uu___1837_24062.universe_of);
        check_type_of = (uu___1837_24062.check_type_of);
        use_bv_sorts = (uu___1837_24062.use_bv_sorts);
        qtbl_name_and_index = (uu___1837_24062.qtbl_name_and_index);
        normalized_eff_names = (uu___1837_24062.normalized_eff_names);
        fv_delta_depths = (uu___1837_24062.fv_delta_depths);
        proof_ns = (uu___1837_24062.proof_ns);
        synth_hook = (uu___1837_24062.synth_hook);
        try_solve_implicits_hook = (uu___1837_24062.try_solve_implicits_hook);
        splice = (uu___1837_24062.splice);
        postprocess = (uu___1837_24062.postprocess);
        is_native_tactic = (uu___1837_24062.is_native_tactic);
        identifier_info = (uu___1837_24062.identifier_info);
        tc_hooks = (uu___1837_24062.tc_hooks);
        dsenv = (uu___1837_24062.dsenv);
        nbe = (uu___1837_24062.nbe);
        strict_args_tab = (uu___1837_24062.strict_args_tab);
        erasable_types_tab = (uu___1837_24062.erasable_types_tab)
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
    let uu____24093 = expected_typ env_  in
    ((let uu___1844_24099 = env_  in
      {
        solver = (uu___1844_24099.solver);
        range = (uu___1844_24099.range);
        curmodule = (uu___1844_24099.curmodule);
        gamma = (uu___1844_24099.gamma);
        gamma_sig = (uu___1844_24099.gamma_sig);
        gamma_cache = (uu___1844_24099.gamma_cache);
        modules = (uu___1844_24099.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1844_24099.sigtab);
        attrtab = (uu___1844_24099.attrtab);
        instantiate_imp = (uu___1844_24099.instantiate_imp);
        effects = (uu___1844_24099.effects);
        generalize = (uu___1844_24099.generalize);
        letrecs = (uu___1844_24099.letrecs);
        top_level = (uu___1844_24099.top_level);
        check_uvars = (uu___1844_24099.check_uvars);
        use_eq = false;
        is_iface = (uu___1844_24099.is_iface);
        admit = (uu___1844_24099.admit);
        lax = (uu___1844_24099.lax);
        lax_universes = (uu___1844_24099.lax_universes);
        phase1 = (uu___1844_24099.phase1);
        failhard = (uu___1844_24099.failhard);
        nosynth = (uu___1844_24099.nosynth);
        uvar_subtyping = (uu___1844_24099.uvar_subtyping);
        tc_term = (uu___1844_24099.tc_term);
        type_of = (uu___1844_24099.type_of);
        universe_of = (uu___1844_24099.universe_of);
        check_type_of = (uu___1844_24099.check_type_of);
        use_bv_sorts = (uu___1844_24099.use_bv_sorts);
        qtbl_name_and_index = (uu___1844_24099.qtbl_name_and_index);
        normalized_eff_names = (uu___1844_24099.normalized_eff_names);
        fv_delta_depths = (uu___1844_24099.fv_delta_depths);
        proof_ns = (uu___1844_24099.proof_ns);
        synth_hook = (uu___1844_24099.synth_hook);
        try_solve_implicits_hook = (uu___1844_24099.try_solve_implicits_hook);
        splice = (uu___1844_24099.splice);
        postprocess = (uu___1844_24099.postprocess);
        is_native_tactic = (uu___1844_24099.is_native_tactic);
        identifier_info = (uu___1844_24099.identifier_info);
        tc_hooks = (uu___1844_24099.tc_hooks);
        dsenv = (uu___1844_24099.dsenv);
        nbe = (uu___1844_24099.nbe);
        strict_args_tab = (uu___1844_24099.strict_args_tab);
        erasable_types_tab = (uu___1844_24099.erasable_types_tab)
      }), uu____24093)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24111 =
      let uu____24114 = FStar_Ident.id_of_text ""  in [uu____24114]  in
    FStar_Ident.lid_of_ids uu____24111  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24121 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24121
        then
          let uu____24126 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24126 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1852_24154 = env  in
       {
         solver = (uu___1852_24154.solver);
         range = (uu___1852_24154.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1852_24154.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1852_24154.expected_typ);
         sigtab = (uu___1852_24154.sigtab);
         attrtab = (uu___1852_24154.attrtab);
         instantiate_imp = (uu___1852_24154.instantiate_imp);
         effects = (uu___1852_24154.effects);
         generalize = (uu___1852_24154.generalize);
         letrecs = (uu___1852_24154.letrecs);
         top_level = (uu___1852_24154.top_level);
         check_uvars = (uu___1852_24154.check_uvars);
         use_eq = (uu___1852_24154.use_eq);
         is_iface = (uu___1852_24154.is_iface);
         admit = (uu___1852_24154.admit);
         lax = (uu___1852_24154.lax);
         lax_universes = (uu___1852_24154.lax_universes);
         phase1 = (uu___1852_24154.phase1);
         failhard = (uu___1852_24154.failhard);
         nosynth = (uu___1852_24154.nosynth);
         uvar_subtyping = (uu___1852_24154.uvar_subtyping);
         tc_term = (uu___1852_24154.tc_term);
         type_of = (uu___1852_24154.type_of);
         universe_of = (uu___1852_24154.universe_of);
         check_type_of = (uu___1852_24154.check_type_of);
         use_bv_sorts = (uu___1852_24154.use_bv_sorts);
         qtbl_name_and_index = (uu___1852_24154.qtbl_name_and_index);
         normalized_eff_names = (uu___1852_24154.normalized_eff_names);
         fv_delta_depths = (uu___1852_24154.fv_delta_depths);
         proof_ns = (uu___1852_24154.proof_ns);
         synth_hook = (uu___1852_24154.synth_hook);
         try_solve_implicits_hook =
           (uu___1852_24154.try_solve_implicits_hook);
         splice = (uu___1852_24154.splice);
         postprocess = (uu___1852_24154.postprocess);
         is_native_tactic = (uu___1852_24154.is_native_tactic);
         identifier_info = (uu___1852_24154.identifier_info);
         tc_hooks = (uu___1852_24154.tc_hooks);
         dsenv = (uu___1852_24154.dsenv);
         nbe = (uu___1852_24154.nbe);
         strict_args_tab = (uu___1852_24154.strict_args_tab);
         erasable_types_tab = (uu___1852_24154.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24206)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24210,(uu____24211,t)))::tl1
          ->
          let uu____24232 =
            let uu____24235 = FStar_Syntax_Free.uvars t  in
            ext out uu____24235  in
          aux uu____24232 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24238;
            FStar_Syntax_Syntax.index = uu____24239;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24247 =
            let uu____24250 = FStar_Syntax_Free.uvars t  in
            ext out uu____24250  in
          aux uu____24247 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24308)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24312,(uu____24313,t)))::tl1
          ->
          let uu____24334 =
            let uu____24337 = FStar_Syntax_Free.univs t  in
            ext out uu____24337  in
          aux uu____24334 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24340;
            FStar_Syntax_Syntax.index = uu____24341;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24349 =
            let uu____24352 = FStar_Syntax_Free.univs t  in
            ext out uu____24352  in
          aux uu____24349 tl1
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
          let uu____24414 = FStar_Util.set_add uname out  in
          aux uu____24414 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24417,(uu____24418,t)))::tl1
          ->
          let uu____24439 =
            let uu____24442 = FStar_Syntax_Free.univnames t  in
            ext out uu____24442  in
          aux uu____24439 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24445;
            FStar_Syntax_Syntax.index = uu____24446;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24454 =
            let uu____24457 = FStar_Syntax_Free.univnames t  in
            ext out uu____24457  in
          aux uu____24454 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24478  ->
            match uu___12_24478 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24482 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24495 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24506 =
      let uu____24515 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24515
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24506 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24563 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24576  ->
              match uu___13_24576 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24579 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24579
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24585) ->
                  let uu____24602 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24602))
       in
    FStar_All.pipe_right uu____24563 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24616  ->
    match uu___14_24616 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24622 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24622
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24645  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24700) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24733,uu____24734) -> false  in
      let uu____24748 =
        FStar_List.tryFind
          (fun uu____24770  ->
             match uu____24770 with | (p,uu____24781) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24748 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24800,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24830 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24830
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1995_24852 = e  in
        {
          solver = (uu___1995_24852.solver);
          range = (uu___1995_24852.range);
          curmodule = (uu___1995_24852.curmodule);
          gamma = (uu___1995_24852.gamma);
          gamma_sig = (uu___1995_24852.gamma_sig);
          gamma_cache = (uu___1995_24852.gamma_cache);
          modules = (uu___1995_24852.modules);
          expected_typ = (uu___1995_24852.expected_typ);
          sigtab = (uu___1995_24852.sigtab);
          attrtab = (uu___1995_24852.attrtab);
          instantiate_imp = (uu___1995_24852.instantiate_imp);
          effects = (uu___1995_24852.effects);
          generalize = (uu___1995_24852.generalize);
          letrecs = (uu___1995_24852.letrecs);
          top_level = (uu___1995_24852.top_level);
          check_uvars = (uu___1995_24852.check_uvars);
          use_eq = (uu___1995_24852.use_eq);
          is_iface = (uu___1995_24852.is_iface);
          admit = (uu___1995_24852.admit);
          lax = (uu___1995_24852.lax);
          lax_universes = (uu___1995_24852.lax_universes);
          phase1 = (uu___1995_24852.phase1);
          failhard = (uu___1995_24852.failhard);
          nosynth = (uu___1995_24852.nosynth);
          uvar_subtyping = (uu___1995_24852.uvar_subtyping);
          tc_term = (uu___1995_24852.tc_term);
          type_of = (uu___1995_24852.type_of);
          universe_of = (uu___1995_24852.universe_of);
          check_type_of = (uu___1995_24852.check_type_of);
          use_bv_sorts = (uu___1995_24852.use_bv_sorts);
          qtbl_name_and_index = (uu___1995_24852.qtbl_name_and_index);
          normalized_eff_names = (uu___1995_24852.normalized_eff_names);
          fv_delta_depths = (uu___1995_24852.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1995_24852.synth_hook);
          try_solve_implicits_hook =
            (uu___1995_24852.try_solve_implicits_hook);
          splice = (uu___1995_24852.splice);
          postprocess = (uu___1995_24852.postprocess);
          is_native_tactic = (uu___1995_24852.is_native_tactic);
          identifier_info = (uu___1995_24852.identifier_info);
          tc_hooks = (uu___1995_24852.tc_hooks);
          dsenv = (uu___1995_24852.dsenv);
          nbe = (uu___1995_24852.nbe);
          strict_args_tab = (uu___1995_24852.strict_args_tab);
          erasable_types_tab = (uu___1995_24852.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2004_24900 = e  in
      {
        solver = (uu___2004_24900.solver);
        range = (uu___2004_24900.range);
        curmodule = (uu___2004_24900.curmodule);
        gamma = (uu___2004_24900.gamma);
        gamma_sig = (uu___2004_24900.gamma_sig);
        gamma_cache = (uu___2004_24900.gamma_cache);
        modules = (uu___2004_24900.modules);
        expected_typ = (uu___2004_24900.expected_typ);
        sigtab = (uu___2004_24900.sigtab);
        attrtab = (uu___2004_24900.attrtab);
        instantiate_imp = (uu___2004_24900.instantiate_imp);
        effects = (uu___2004_24900.effects);
        generalize = (uu___2004_24900.generalize);
        letrecs = (uu___2004_24900.letrecs);
        top_level = (uu___2004_24900.top_level);
        check_uvars = (uu___2004_24900.check_uvars);
        use_eq = (uu___2004_24900.use_eq);
        is_iface = (uu___2004_24900.is_iface);
        admit = (uu___2004_24900.admit);
        lax = (uu___2004_24900.lax);
        lax_universes = (uu___2004_24900.lax_universes);
        phase1 = (uu___2004_24900.phase1);
        failhard = (uu___2004_24900.failhard);
        nosynth = (uu___2004_24900.nosynth);
        uvar_subtyping = (uu___2004_24900.uvar_subtyping);
        tc_term = (uu___2004_24900.tc_term);
        type_of = (uu___2004_24900.type_of);
        universe_of = (uu___2004_24900.universe_of);
        check_type_of = (uu___2004_24900.check_type_of);
        use_bv_sorts = (uu___2004_24900.use_bv_sorts);
        qtbl_name_and_index = (uu___2004_24900.qtbl_name_and_index);
        normalized_eff_names = (uu___2004_24900.normalized_eff_names);
        fv_delta_depths = (uu___2004_24900.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2004_24900.synth_hook);
        try_solve_implicits_hook = (uu___2004_24900.try_solve_implicits_hook);
        splice = (uu___2004_24900.splice);
        postprocess = (uu___2004_24900.postprocess);
        is_native_tactic = (uu___2004_24900.is_native_tactic);
        identifier_info = (uu___2004_24900.identifier_info);
        tc_hooks = (uu___2004_24900.tc_hooks);
        dsenv = (uu___2004_24900.dsenv);
        nbe = (uu___2004_24900.nbe);
        strict_args_tab = (uu___2004_24900.strict_args_tab);
        erasable_types_tab = (uu___2004_24900.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24916 = FStar_Syntax_Free.names t  in
      let uu____24919 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24916 uu____24919
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24942 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24942
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24952 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24952
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24973 =
      match uu____24973 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24993 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24993)
       in
    let uu____25001 =
      let uu____25005 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25005 FStar_List.rev  in
    FStar_All.pipe_right uu____25001 (FStar_String.concat " ")
  
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
                  (let uu____25073 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25073 with
                   | FStar_Pervasives_Native.Some uu____25077 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25080 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25090;
        FStar_TypeChecker_Common.univ_ineqs = uu____25091;
        FStar_TypeChecker_Common.implicits = uu____25092;_} -> true
    | uu____25102 -> false
  
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
          let uu___2048_25124 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2048_25124.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2048_25124.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2048_25124.FStar_TypeChecker_Common.implicits)
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
          let uu____25163 = FStar_Options.defensive ()  in
          if uu____25163
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25169 =
              let uu____25171 =
                let uu____25173 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25173  in
              Prims.op_Negation uu____25171  in
            (if uu____25169
             then
               let uu____25180 =
                 let uu____25186 =
                   let uu____25188 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25190 =
                     let uu____25192 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25192
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25188 uu____25190
                    in
                 (FStar_Errors.Warning_Defensive, uu____25186)  in
               FStar_Errors.log_issue rng uu____25180
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
          let uu____25232 =
            let uu____25234 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25234  in
          if uu____25232
          then ()
          else
            (let uu____25239 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25239 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25265 =
            let uu____25267 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25267  in
          if uu____25265
          then ()
          else
            (let uu____25272 = bound_vars e  in
             def_check_closed_in rng msg uu____25272 t)
  
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
          let uu___2085_25311 = g  in
          let uu____25312 =
            let uu____25313 =
              let uu____25314 =
                let uu____25321 =
                  let uu____25322 =
                    let uu____25339 =
                      let uu____25350 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25350]  in
                    (f, uu____25339)  in
                  FStar_Syntax_Syntax.Tm_app uu____25322  in
                FStar_Syntax_Syntax.mk uu____25321  in
              uu____25314 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25387  -> FStar_TypeChecker_Common.NonTrivial _25387)
              uu____25313
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____25312;
            FStar_TypeChecker_Common.deferred =
              (uu___2085_25311.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2085_25311.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2085_25311.FStar_TypeChecker_Common.implicits)
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
          let uu___2092_25405 = g  in
          let uu____25406 =
            let uu____25407 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25407  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25406;
            FStar_TypeChecker_Common.deferred =
              (uu___2092_25405.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2092_25405.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2092_25405.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2097_25424 = g  in
          let uu____25425 =
            let uu____25426 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25426  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25425;
            FStar_TypeChecker_Common.deferred =
              (uu___2097_25424.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2097_25424.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2097_25424.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2101_25428 = g  in
          let uu____25429 =
            let uu____25430 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25430  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25429;
            FStar_TypeChecker_Common.deferred =
              (uu___2101_25428.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2101_25428.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2101_25428.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25437 ->
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
                       let uu____25514 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25514
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2124_25521 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2124_25521.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2124_25521.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2124_25521.FStar_TypeChecker_Common.implicits)
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
               let uu____25555 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25555
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
            let uu___2139_25582 = g  in
            let uu____25583 =
              let uu____25584 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25584  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25583;
              FStar_TypeChecker_Common.deferred =
                (uu___2139_25582.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2139_25582.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2139_25582.FStar_TypeChecker_Common.implicits)
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
              let uu____25642 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25642 with
              | FStar_Pervasives_Native.Some
                  (uu____25667::(tm,uu____25669)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25733 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25751 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25751;
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
                      let uu___2161_25783 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2161_25783.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2161_25783.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2161_25783.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____25837 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____25894  ->
                      fun b  ->
                        match uu____25894 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____25936 =
                              let uu____25949 = reason b  in
                              new_implicit_var_aux uu____25949 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____25936 with
                             | (t,uu____25966,g_t) ->
                                 let uu____25980 =
                                   let uu____25983 =
                                     let uu____25986 =
                                       let uu____25987 =
                                         let uu____25994 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____25994, t)  in
                                       FStar_Syntax_Syntax.NT uu____25987  in
                                     [uu____25986]  in
                                   FStar_List.append substs1 uu____25983  in
                                 let uu____26005 = conj_guard g g_t  in
                                 (uu____25980,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26005))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____25837
              (fun uu____26034  ->
                 match uu____26034 with
                 | (uu____26051,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26067  -> ());
    push = (fun uu____26069  -> ());
    pop = (fun uu____26072  -> ());
    snapshot =
      (fun uu____26075  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26094  -> fun uu____26095  -> ());
    encode_sig = (fun uu____26110  -> fun uu____26111  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26117 =
             let uu____26124 = FStar_Options.peek ()  in (e, g, uu____26124)
              in
           [uu____26117]);
    solve = (fun uu____26140  -> fun uu____26141  -> fun uu____26142  -> ());
    finish = (fun uu____26149  -> ());
    refresh = (fun uu____26151  -> ())
  } 