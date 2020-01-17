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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> synth_hook
  
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> splice1
  
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab; erasable_types_tab;_} -> mpreprocess
  
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
        synth_hook; splice = splice1; mpreprocess; postprocess;
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
           (fun uu___0_12966  ->
              match uu___0_12966 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12969 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12969  in
                  let uu____12970 =
                    let uu____12971 = FStar_Syntax_Subst.compress y  in
                    uu____12971.FStar_Syntax_Syntax.n  in
                  (match uu____12970 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12975 =
                         let uu___315_12976 = y1  in
                         let uu____12977 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___315_12976.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___315_12976.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12977
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12975
                   | uu____12980 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___321_12994 = env  in
      let uu____12995 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___321_12994.solver);
        range = (uu___321_12994.range);
        curmodule = (uu___321_12994.curmodule);
        gamma = uu____12995;
        gamma_sig = (uu___321_12994.gamma_sig);
        gamma_cache = (uu___321_12994.gamma_cache);
        modules = (uu___321_12994.modules);
        expected_typ = (uu___321_12994.expected_typ);
        sigtab = (uu___321_12994.sigtab);
        attrtab = (uu___321_12994.attrtab);
        instantiate_imp = (uu___321_12994.instantiate_imp);
        effects = (uu___321_12994.effects);
        generalize = (uu___321_12994.generalize);
        letrecs = (uu___321_12994.letrecs);
        top_level = (uu___321_12994.top_level);
        check_uvars = (uu___321_12994.check_uvars);
        use_eq = (uu___321_12994.use_eq);
        is_iface = (uu___321_12994.is_iface);
        admit = (uu___321_12994.admit);
        lax = (uu___321_12994.lax);
        lax_universes = (uu___321_12994.lax_universes);
        phase1 = (uu___321_12994.phase1);
        failhard = (uu___321_12994.failhard);
        nosynth = (uu___321_12994.nosynth);
        uvar_subtyping = (uu___321_12994.uvar_subtyping);
        tc_term = (uu___321_12994.tc_term);
        type_of = (uu___321_12994.type_of);
        universe_of = (uu___321_12994.universe_of);
        check_type_of = (uu___321_12994.check_type_of);
        use_bv_sorts = (uu___321_12994.use_bv_sorts);
        qtbl_name_and_index = (uu___321_12994.qtbl_name_and_index);
        normalized_eff_names = (uu___321_12994.normalized_eff_names);
        fv_delta_depths = (uu___321_12994.fv_delta_depths);
        proof_ns = (uu___321_12994.proof_ns);
        synth_hook = (uu___321_12994.synth_hook);
        splice = (uu___321_12994.splice);
        mpreprocess = (uu___321_12994.mpreprocess);
        postprocess = (uu___321_12994.postprocess);
        is_native_tactic = (uu___321_12994.is_native_tactic);
        identifier_info = (uu___321_12994.identifier_info);
        tc_hooks = (uu___321_12994.tc_hooks);
        dsenv = (uu___321_12994.dsenv);
        nbe = (uu___321_12994.nbe);
        strict_args_tab = (uu___321_12994.strict_args_tab);
        erasable_types_tab = (uu___321_12994.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13003  -> fun uu____13004  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___328_13026 = env  in
      {
        solver = (uu___328_13026.solver);
        range = (uu___328_13026.range);
        curmodule = (uu___328_13026.curmodule);
        gamma = (uu___328_13026.gamma);
        gamma_sig = (uu___328_13026.gamma_sig);
        gamma_cache = (uu___328_13026.gamma_cache);
        modules = (uu___328_13026.modules);
        expected_typ = (uu___328_13026.expected_typ);
        sigtab = (uu___328_13026.sigtab);
        attrtab = (uu___328_13026.attrtab);
        instantiate_imp = (uu___328_13026.instantiate_imp);
        effects = (uu___328_13026.effects);
        generalize = (uu___328_13026.generalize);
        letrecs = (uu___328_13026.letrecs);
        top_level = (uu___328_13026.top_level);
        check_uvars = (uu___328_13026.check_uvars);
        use_eq = (uu___328_13026.use_eq);
        is_iface = (uu___328_13026.is_iface);
        admit = (uu___328_13026.admit);
        lax = (uu___328_13026.lax);
        lax_universes = (uu___328_13026.lax_universes);
        phase1 = (uu___328_13026.phase1);
        failhard = (uu___328_13026.failhard);
        nosynth = (uu___328_13026.nosynth);
        uvar_subtyping = (uu___328_13026.uvar_subtyping);
        tc_term = (uu___328_13026.tc_term);
        type_of = (uu___328_13026.type_of);
        universe_of = (uu___328_13026.universe_of);
        check_type_of = (uu___328_13026.check_type_of);
        use_bv_sorts = (uu___328_13026.use_bv_sorts);
        qtbl_name_and_index = (uu___328_13026.qtbl_name_and_index);
        normalized_eff_names = (uu___328_13026.normalized_eff_names);
        fv_delta_depths = (uu___328_13026.fv_delta_depths);
        proof_ns = (uu___328_13026.proof_ns);
        synth_hook = (uu___328_13026.synth_hook);
        splice = (uu___328_13026.splice);
        mpreprocess = (uu___328_13026.mpreprocess);
        postprocess = (uu___328_13026.postprocess);
        is_native_tactic = (uu___328_13026.is_native_tactic);
        identifier_info = (uu___328_13026.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___328_13026.dsenv);
        nbe = (uu___328_13026.nbe);
        strict_args_tab = (uu___328_13026.strict_args_tab);
        erasable_types_tab = (uu___328_13026.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___332_13038 = e  in
      let uu____13039 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___332_13038.solver);
        range = (uu___332_13038.range);
        curmodule = (uu___332_13038.curmodule);
        gamma = (uu___332_13038.gamma);
        gamma_sig = (uu___332_13038.gamma_sig);
        gamma_cache = (uu___332_13038.gamma_cache);
        modules = (uu___332_13038.modules);
        expected_typ = (uu___332_13038.expected_typ);
        sigtab = (uu___332_13038.sigtab);
        attrtab = (uu___332_13038.attrtab);
        instantiate_imp = (uu___332_13038.instantiate_imp);
        effects = (uu___332_13038.effects);
        generalize = (uu___332_13038.generalize);
        letrecs = (uu___332_13038.letrecs);
        top_level = (uu___332_13038.top_level);
        check_uvars = (uu___332_13038.check_uvars);
        use_eq = (uu___332_13038.use_eq);
        is_iface = (uu___332_13038.is_iface);
        admit = (uu___332_13038.admit);
        lax = (uu___332_13038.lax);
        lax_universes = (uu___332_13038.lax_universes);
        phase1 = (uu___332_13038.phase1);
        failhard = (uu___332_13038.failhard);
        nosynth = (uu___332_13038.nosynth);
        uvar_subtyping = (uu___332_13038.uvar_subtyping);
        tc_term = (uu___332_13038.tc_term);
        type_of = (uu___332_13038.type_of);
        universe_of = (uu___332_13038.universe_of);
        check_type_of = (uu___332_13038.check_type_of);
        use_bv_sorts = (uu___332_13038.use_bv_sorts);
        qtbl_name_and_index = (uu___332_13038.qtbl_name_and_index);
        normalized_eff_names = (uu___332_13038.normalized_eff_names);
        fv_delta_depths = (uu___332_13038.fv_delta_depths);
        proof_ns = (uu___332_13038.proof_ns);
        synth_hook = (uu___332_13038.synth_hook);
        splice = (uu___332_13038.splice);
        mpreprocess = (uu___332_13038.mpreprocess);
        postprocess = (uu___332_13038.postprocess);
        is_native_tactic = (uu___332_13038.is_native_tactic);
        identifier_info = (uu___332_13038.identifier_info);
        tc_hooks = (uu___332_13038.tc_hooks);
        dsenv = uu____13039;
        nbe = (uu___332_13038.nbe);
        strict_args_tab = (uu___332_13038.strict_args_tab);
        erasable_types_tab = (uu___332_13038.erasable_types_tab)
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
      | (NoDelta ,uu____13068) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13071,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13073,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13076 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13090 . unit -> 'Auu____13090 FStar_Util.smap =
  fun uu____13097  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13103 . unit -> 'Auu____13103 FStar_Util.smap =
  fun uu____13110  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13248 = new_gamma_cache ()  in
                  let uu____13251 = new_sigtab ()  in
                  let uu____13254 = new_sigtab ()  in
                  let uu____13261 =
                    let uu____13276 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13276, FStar_Pervasives_Native.None)  in
                  let uu____13297 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13301 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13305 = FStar_Options.using_facts_from ()  in
                  let uu____13306 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13309 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13310 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13324 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13248;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13251;
                    attrtab = uu____13254;
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
                    qtbl_name_and_index = uu____13261;
                    normalized_eff_names = uu____13297;
                    fv_delta_depths = uu____13301;
                    proof_ns = uu____13305;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
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
                    is_native_tactic = (fun uu____13397  -> false);
                    identifier_info = uu____13306;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13309;
                    nbe = nbe1;
                    strict_args_tab = uu____13310;
                    erasable_types_tab = uu____13324
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
  fun uu____13476  ->
    let uu____13477 = FStar_ST.op_Bang query_indices  in
    match uu____13477 with
    | [] -> failwith "Empty query indices!"
    | uu____13532 ->
        let uu____13542 =
          let uu____13552 =
            let uu____13560 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13560  in
          let uu____13614 = FStar_ST.op_Bang query_indices  in uu____13552 ::
            uu____13614
           in
        FStar_ST.op_Colon_Equals query_indices uu____13542
  
let (pop_query_indices : unit -> unit) =
  fun uu____13710  ->
    let uu____13711 = FStar_ST.op_Bang query_indices  in
    match uu____13711 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13838  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13875  ->
    match uu____13875 with
    | (l,n1) ->
        let uu____13885 = FStar_ST.op_Bang query_indices  in
        (match uu____13885 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14007 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14030  ->
    let uu____14031 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14031
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14099 =
       let uu____14102 = FStar_ST.op_Bang stack  in env :: uu____14102  in
     FStar_ST.op_Colon_Equals stack uu____14099);
    (let uu___403_14151 = env  in
     let uu____14152 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14155 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14158 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14165 =
       let uu____14180 =
         let uu____14184 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14184  in
       let uu____14216 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14180, uu____14216)  in
     let uu____14265 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14268 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14271 =
       let uu____14274 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14274  in
     let uu____14294 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14307 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___403_14151.solver);
       range = (uu___403_14151.range);
       curmodule = (uu___403_14151.curmodule);
       gamma = (uu___403_14151.gamma);
       gamma_sig = (uu___403_14151.gamma_sig);
       gamma_cache = uu____14152;
       modules = (uu___403_14151.modules);
       expected_typ = (uu___403_14151.expected_typ);
       sigtab = uu____14155;
       attrtab = uu____14158;
       instantiate_imp = (uu___403_14151.instantiate_imp);
       effects = (uu___403_14151.effects);
       generalize = (uu___403_14151.generalize);
       letrecs = (uu___403_14151.letrecs);
       top_level = (uu___403_14151.top_level);
       check_uvars = (uu___403_14151.check_uvars);
       use_eq = (uu___403_14151.use_eq);
       is_iface = (uu___403_14151.is_iface);
       admit = (uu___403_14151.admit);
       lax = (uu___403_14151.lax);
       lax_universes = (uu___403_14151.lax_universes);
       phase1 = (uu___403_14151.phase1);
       failhard = (uu___403_14151.failhard);
       nosynth = (uu___403_14151.nosynth);
       uvar_subtyping = (uu___403_14151.uvar_subtyping);
       tc_term = (uu___403_14151.tc_term);
       type_of = (uu___403_14151.type_of);
       universe_of = (uu___403_14151.universe_of);
       check_type_of = (uu___403_14151.check_type_of);
       use_bv_sorts = (uu___403_14151.use_bv_sorts);
       qtbl_name_and_index = uu____14165;
       normalized_eff_names = uu____14265;
       fv_delta_depths = uu____14268;
       proof_ns = (uu___403_14151.proof_ns);
       synth_hook = (uu___403_14151.synth_hook);
       splice = (uu___403_14151.splice);
       mpreprocess = (uu___403_14151.mpreprocess);
       postprocess = (uu___403_14151.postprocess);
       is_native_tactic = (uu___403_14151.is_native_tactic);
       identifier_info = uu____14271;
       tc_hooks = (uu___403_14151.tc_hooks);
       dsenv = (uu___403_14151.dsenv);
       nbe = (uu___403_14151.nbe);
       strict_args_tab = uu____14294;
       erasable_types_tab = uu____14307
     })
  
let (pop_stack : unit -> env) =
  fun uu____14317  ->
    let uu____14318 = FStar_ST.op_Bang stack  in
    match uu____14318 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14372 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14462  ->
           let uu____14463 = snapshot_stack env  in
           match uu____14463 with
           | (stack_depth,env1) ->
               let uu____14497 = snapshot_query_indices ()  in
               (match uu____14497 with
                | (query_indices_depth,()) ->
                    let uu____14530 = (env1.solver).snapshot msg  in
                    (match uu____14530 with
                     | (solver_depth,()) ->
                         let uu____14587 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14587 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___428_14654 = env1  in
                                 {
                                   solver = (uu___428_14654.solver);
                                   range = (uu___428_14654.range);
                                   curmodule = (uu___428_14654.curmodule);
                                   gamma = (uu___428_14654.gamma);
                                   gamma_sig = (uu___428_14654.gamma_sig);
                                   gamma_cache = (uu___428_14654.gamma_cache);
                                   modules = (uu___428_14654.modules);
                                   expected_typ =
                                     (uu___428_14654.expected_typ);
                                   sigtab = (uu___428_14654.sigtab);
                                   attrtab = (uu___428_14654.attrtab);
                                   instantiate_imp =
                                     (uu___428_14654.instantiate_imp);
                                   effects = (uu___428_14654.effects);
                                   generalize = (uu___428_14654.generalize);
                                   letrecs = (uu___428_14654.letrecs);
                                   top_level = (uu___428_14654.top_level);
                                   check_uvars = (uu___428_14654.check_uvars);
                                   use_eq = (uu___428_14654.use_eq);
                                   is_iface = (uu___428_14654.is_iface);
                                   admit = (uu___428_14654.admit);
                                   lax = (uu___428_14654.lax);
                                   lax_universes =
                                     (uu___428_14654.lax_universes);
                                   phase1 = (uu___428_14654.phase1);
                                   failhard = (uu___428_14654.failhard);
                                   nosynth = (uu___428_14654.nosynth);
                                   uvar_subtyping =
                                     (uu___428_14654.uvar_subtyping);
                                   tc_term = (uu___428_14654.tc_term);
                                   type_of = (uu___428_14654.type_of);
                                   universe_of = (uu___428_14654.universe_of);
                                   check_type_of =
                                     (uu___428_14654.check_type_of);
                                   use_bv_sorts =
                                     (uu___428_14654.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___428_14654.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___428_14654.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___428_14654.fv_delta_depths);
                                   proof_ns = (uu___428_14654.proof_ns);
                                   synth_hook = (uu___428_14654.synth_hook);
                                   splice = (uu___428_14654.splice);
                                   mpreprocess = (uu___428_14654.mpreprocess);
                                   postprocess = (uu___428_14654.postprocess);
                                   is_native_tactic =
                                     (uu___428_14654.is_native_tactic);
                                   identifier_info =
                                     (uu___428_14654.identifier_info);
                                   tc_hooks = (uu___428_14654.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___428_14654.nbe);
                                   strict_args_tab =
                                     (uu___428_14654.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___428_14654.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14688  ->
             let uu____14689 =
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
             match uu____14689 with
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
                             ((let uu____14869 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14869
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14885 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14885
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14917,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14959 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14989  ->
                  match uu____14989 with
                  | (m,uu____14997) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14959 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___473_15012 = env  in
               {
                 solver = (uu___473_15012.solver);
                 range = (uu___473_15012.range);
                 curmodule = (uu___473_15012.curmodule);
                 gamma = (uu___473_15012.gamma);
                 gamma_sig = (uu___473_15012.gamma_sig);
                 gamma_cache = (uu___473_15012.gamma_cache);
                 modules = (uu___473_15012.modules);
                 expected_typ = (uu___473_15012.expected_typ);
                 sigtab = (uu___473_15012.sigtab);
                 attrtab = (uu___473_15012.attrtab);
                 instantiate_imp = (uu___473_15012.instantiate_imp);
                 effects = (uu___473_15012.effects);
                 generalize = (uu___473_15012.generalize);
                 letrecs = (uu___473_15012.letrecs);
                 top_level = (uu___473_15012.top_level);
                 check_uvars = (uu___473_15012.check_uvars);
                 use_eq = (uu___473_15012.use_eq);
                 is_iface = (uu___473_15012.is_iface);
                 admit = (uu___473_15012.admit);
                 lax = (uu___473_15012.lax);
                 lax_universes = (uu___473_15012.lax_universes);
                 phase1 = (uu___473_15012.phase1);
                 failhard = (uu___473_15012.failhard);
                 nosynth = (uu___473_15012.nosynth);
                 uvar_subtyping = (uu___473_15012.uvar_subtyping);
                 tc_term = (uu___473_15012.tc_term);
                 type_of = (uu___473_15012.type_of);
                 universe_of = (uu___473_15012.universe_of);
                 check_type_of = (uu___473_15012.check_type_of);
                 use_bv_sorts = (uu___473_15012.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___473_15012.normalized_eff_names);
                 fv_delta_depths = (uu___473_15012.fv_delta_depths);
                 proof_ns = (uu___473_15012.proof_ns);
                 synth_hook = (uu___473_15012.synth_hook);
                 splice = (uu___473_15012.splice);
                 mpreprocess = (uu___473_15012.mpreprocess);
                 postprocess = (uu___473_15012.postprocess);
                 is_native_tactic = (uu___473_15012.is_native_tactic);
                 identifier_info = (uu___473_15012.identifier_info);
                 tc_hooks = (uu___473_15012.tc_hooks);
                 dsenv = (uu___473_15012.dsenv);
                 nbe = (uu___473_15012.nbe);
                 strict_args_tab = (uu___473_15012.strict_args_tab);
                 erasable_types_tab = (uu___473_15012.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15029,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___482_15045 = env  in
               {
                 solver = (uu___482_15045.solver);
                 range = (uu___482_15045.range);
                 curmodule = (uu___482_15045.curmodule);
                 gamma = (uu___482_15045.gamma);
                 gamma_sig = (uu___482_15045.gamma_sig);
                 gamma_cache = (uu___482_15045.gamma_cache);
                 modules = (uu___482_15045.modules);
                 expected_typ = (uu___482_15045.expected_typ);
                 sigtab = (uu___482_15045.sigtab);
                 attrtab = (uu___482_15045.attrtab);
                 instantiate_imp = (uu___482_15045.instantiate_imp);
                 effects = (uu___482_15045.effects);
                 generalize = (uu___482_15045.generalize);
                 letrecs = (uu___482_15045.letrecs);
                 top_level = (uu___482_15045.top_level);
                 check_uvars = (uu___482_15045.check_uvars);
                 use_eq = (uu___482_15045.use_eq);
                 is_iface = (uu___482_15045.is_iface);
                 admit = (uu___482_15045.admit);
                 lax = (uu___482_15045.lax);
                 lax_universes = (uu___482_15045.lax_universes);
                 phase1 = (uu___482_15045.phase1);
                 failhard = (uu___482_15045.failhard);
                 nosynth = (uu___482_15045.nosynth);
                 uvar_subtyping = (uu___482_15045.uvar_subtyping);
                 tc_term = (uu___482_15045.tc_term);
                 type_of = (uu___482_15045.type_of);
                 universe_of = (uu___482_15045.universe_of);
                 check_type_of = (uu___482_15045.check_type_of);
                 use_bv_sorts = (uu___482_15045.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___482_15045.normalized_eff_names);
                 fv_delta_depths = (uu___482_15045.fv_delta_depths);
                 proof_ns = (uu___482_15045.proof_ns);
                 synth_hook = (uu___482_15045.synth_hook);
                 splice = (uu___482_15045.splice);
                 mpreprocess = (uu___482_15045.mpreprocess);
                 postprocess = (uu___482_15045.postprocess);
                 is_native_tactic = (uu___482_15045.is_native_tactic);
                 identifier_info = (uu___482_15045.identifier_info);
                 tc_hooks = (uu___482_15045.tc_hooks);
                 dsenv = (uu___482_15045.dsenv);
                 nbe = (uu___482_15045.nbe);
                 strict_args_tab = (uu___482_15045.strict_args_tab);
                 erasable_types_tab = (uu___482_15045.erasable_types_tab)
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
        (let uu___489_15088 = e  in
         {
           solver = (uu___489_15088.solver);
           range = r;
           curmodule = (uu___489_15088.curmodule);
           gamma = (uu___489_15088.gamma);
           gamma_sig = (uu___489_15088.gamma_sig);
           gamma_cache = (uu___489_15088.gamma_cache);
           modules = (uu___489_15088.modules);
           expected_typ = (uu___489_15088.expected_typ);
           sigtab = (uu___489_15088.sigtab);
           attrtab = (uu___489_15088.attrtab);
           instantiate_imp = (uu___489_15088.instantiate_imp);
           effects = (uu___489_15088.effects);
           generalize = (uu___489_15088.generalize);
           letrecs = (uu___489_15088.letrecs);
           top_level = (uu___489_15088.top_level);
           check_uvars = (uu___489_15088.check_uvars);
           use_eq = (uu___489_15088.use_eq);
           is_iface = (uu___489_15088.is_iface);
           admit = (uu___489_15088.admit);
           lax = (uu___489_15088.lax);
           lax_universes = (uu___489_15088.lax_universes);
           phase1 = (uu___489_15088.phase1);
           failhard = (uu___489_15088.failhard);
           nosynth = (uu___489_15088.nosynth);
           uvar_subtyping = (uu___489_15088.uvar_subtyping);
           tc_term = (uu___489_15088.tc_term);
           type_of = (uu___489_15088.type_of);
           universe_of = (uu___489_15088.universe_of);
           check_type_of = (uu___489_15088.check_type_of);
           use_bv_sorts = (uu___489_15088.use_bv_sorts);
           qtbl_name_and_index = (uu___489_15088.qtbl_name_and_index);
           normalized_eff_names = (uu___489_15088.normalized_eff_names);
           fv_delta_depths = (uu___489_15088.fv_delta_depths);
           proof_ns = (uu___489_15088.proof_ns);
           synth_hook = (uu___489_15088.synth_hook);
           splice = (uu___489_15088.splice);
           mpreprocess = (uu___489_15088.mpreprocess);
           postprocess = (uu___489_15088.postprocess);
           is_native_tactic = (uu___489_15088.is_native_tactic);
           identifier_info = (uu___489_15088.identifier_info);
           tc_hooks = (uu___489_15088.tc_hooks);
           dsenv = (uu___489_15088.dsenv);
           nbe = (uu___489_15088.nbe);
           strict_args_tab = (uu___489_15088.strict_args_tab);
           erasable_types_tab = (uu___489_15088.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15108 =
        let uu____15109 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15109 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15108
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15164 =
          let uu____15165 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15165 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15164
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15220 =
          let uu____15221 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15221 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15220
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15276 =
        let uu____15277 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15277 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15276
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___506_15341 = env  in
      {
        solver = (uu___506_15341.solver);
        range = (uu___506_15341.range);
        curmodule = lid;
        gamma = (uu___506_15341.gamma);
        gamma_sig = (uu___506_15341.gamma_sig);
        gamma_cache = (uu___506_15341.gamma_cache);
        modules = (uu___506_15341.modules);
        expected_typ = (uu___506_15341.expected_typ);
        sigtab = (uu___506_15341.sigtab);
        attrtab = (uu___506_15341.attrtab);
        instantiate_imp = (uu___506_15341.instantiate_imp);
        effects = (uu___506_15341.effects);
        generalize = (uu___506_15341.generalize);
        letrecs = (uu___506_15341.letrecs);
        top_level = (uu___506_15341.top_level);
        check_uvars = (uu___506_15341.check_uvars);
        use_eq = (uu___506_15341.use_eq);
        is_iface = (uu___506_15341.is_iface);
        admit = (uu___506_15341.admit);
        lax = (uu___506_15341.lax);
        lax_universes = (uu___506_15341.lax_universes);
        phase1 = (uu___506_15341.phase1);
        failhard = (uu___506_15341.failhard);
        nosynth = (uu___506_15341.nosynth);
        uvar_subtyping = (uu___506_15341.uvar_subtyping);
        tc_term = (uu___506_15341.tc_term);
        type_of = (uu___506_15341.type_of);
        universe_of = (uu___506_15341.universe_of);
        check_type_of = (uu___506_15341.check_type_of);
        use_bv_sorts = (uu___506_15341.use_bv_sorts);
        qtbl_name_and_index = (uu___506_15341.qtbl_name_and_index);
        normalized_eff_names = (uu___506_15341.normalized_eff_names);
        fv_delta_depths = (uu___506_15341.fv_delta_depths);
        proof_ns = (uu___506_15341.proof_ns);
        synth_hook = (uu___506_15341.synth_hook);
        splice = (uu___506_15341.splice);
        mpreprocess = (uu___506_15341.mpreprocess);
        postprocess = (uu___506_15341.postprocess);
        is_native_tactic = (uu___506_15341.is_native_tactic);
        identifier_info = (uu___506_15341.identifier_info);
        tc_hooks = (uu___506_15341.tc_hooks);
        dsenv = (uu___506_15341.dsenv);
        nbe = (uu___506_15341.nbe);
        strict_args_tab = (uu___506_15341.strict_args_tab);
        erasable_types_tab = (uu___506_15341.erasable_types_tab)
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
      let uu____15372 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15372
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15385 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15385)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15400 =
      let uu____15402 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15402  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15400)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15411  ->
    let uu____15412 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15412
  
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
      | ((formals,t),uu____15512) ->
          let vs = mk_univ_subst formals us  in
          let uu____15536 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15536)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15553  ->
    match uu___1_15553 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15579  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15599 = inst_tscheme t  in
      match uu____15599 with
      | (us,t1) ->
          let uu____15610 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15610)
  
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
          let uu____15635 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15637 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15635 uu____15637
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
        fun uu____15664  ->
          match uu____15664 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15678 =
                    let uu____15680 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15684 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15688 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15690 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15680 uu____15684 uu____15688 uu____15690
                     in
                  failwith uu____15678)
               else ();
               (let uu____15695 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15695))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15713 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15724 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15735 -> false
  
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
             | ([],uu____15783) -> Maybe
             | (uu____15790,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15810 -> No  in
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
          let uu____15904 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15904 with
          | FStar_Pervasives_Native.None  ->
              let uu____15927 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15971  ->
                     match uu___2_15971 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16010 = FStar_Ident.lid_equals lid l  in
                         if uu____16010
                         then
                           let uu____16033 =
                             let uu____16052 =
                               let uu____16067 = inst_tscheme t  in
                               FStar_Util.Inl uu____16067  in
                             let uu____16082 = FStar_Ident.range_of_lid l  in
                             (uu____16052, uu____16082)  in
                           FStar_Pervasives_Native.Some uu____16033
                         else FStar_Pervasives_Native.None
                     | uu____16135 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15927
                (fun uu____16173  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16183  ->
                        match uu___3_16183 with
                        | (uu____16186,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16188);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16189;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16190;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16191;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16192;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16193;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16215 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16215
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
                                  uu____16267 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16274 -> cache t  in
                            let uu____16275 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16275 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16281 =
                                   let uu____16282 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16282)
                                    in
                                 maybe_cache uu____16281)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16353 = find_in_sigtab env lid  in
         match uu____16353 with
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
      let uu____16434 = lookup_qname env lid  in
      match uu____16434 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16455,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16569 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16569 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16614 =
          let uu____16617 = lookup_attr env1 attr  in se1 :: uu____16617  in
        FStar_Util.smap_add (attrtab env1) attr uu____16614  in
      FStar_List.iter
        (fun attr  ->
           let uu____16627 =
             let uu____16628 = FStar_Syntax_Subst.compress attr  in
             uu____16628.FStar_Syntax_Syntax.n  in
           match uu____16627 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16632 =
                 let uu____16634 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16634.FStar_Ident.str  in
               add_one1 env se uu____16632
           | uu____16635 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16658) ->
          add_sigelts env ses
      | uu____16667 ->
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
        (fun uu___4_16705  ->
           match uu___4_16705 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16723 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16785,lb::[]),uu____16787) ->
            let uu____16796 =
              let uu____16805 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16814 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16805, uu____16814)  in
            FStar_Pervasives_Native.Some uu____16796
        | FStar_Syntax_Syntax.Sig_let ((uu____16827,lbs),uu____16829) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16861 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16874 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16874
                     then
                       let uu____16887 =
                         let uu____16896 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16905 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16896, uu____16905)  in
                       FStar_Pervasives_Native.Some uu____16887
                     else FStar_Pervasives_Native.None)
        | uu____16928 -> FStar_Pervasives_Native.None
  
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
                    let uu____17020 =
                      let uu____17022 =
                        let uu____17024 =
                          let uu____17026 =
                            let uu____17028 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17034 =
                              let uu____17036 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17036  in
                            Prims.op_Hat uu____17028 uu____17034  in
                          Prims.op_Hat ", expected " uu____17026  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17024
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17022
                       in
                    failwith uu____17020
                  else ());
             (let uu____17043 =
                let uu____17052 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17052, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17043))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17072,uu____17073) ->
            let uu____17078 =
              let uu____17087 =
                let uu____17092 =
                  let uu____17093 =
                    let uu____17096 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17096  in
                  (us, uu____17093)  in
                inst_ts us_opt uu____17092  in
              (uu____17087, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17078
        | uu____17115 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17204 =
          match uu____17204 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17300,uvs,t,uu____17303,uu____17304,uu____17305);
                      FStar_Syntax_Syntax.sigrng = uu____17306;
                      FStar_Syntax_Syntax.sigquals = uu____17307;
                      FStar_Syntax_Syntax.sigmeta = uu____17308;
                      FStar_Syntax_Syntax.sigattrs = uu____17309;
                      FStar_Syntax_Syntax.sigopts = uu____17310;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17335 =
                     let uu____17344 = inst_tscheme1 (uvs, t)  in
                     (uu____17344, rng)  in
                   FStar_Pervasives_Native.Some uu____17335
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17368;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17370;
                      FStar_Syntax_Syntax.sigattrs = uu____17371;
                      FStar_Syntax_Syntax.sigopts = uu____17372;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17391 =
                     let uu____17393 = in_cur_mod env l  in uu____17393 = Yes
                      in
                   if uu____17391
                   then
                     let uu____17405 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17405
                      then
                        let uu____17421 =
                          let uu____17430 = inst_tscheme1 (uvs, t)  in
                          (uu____17430, rng)  in
                        FStar_Pervasives_Native.Some uu____17421
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17463 =
                        let uu____17472 = inst_tscheme1 (uvs, t)  in
                        (uu____17472, rng)  in
                      FStar_Pervasives_Native.Some uu____17463)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17497,uu____17498);
                      FStar_Syntax_Syntax.sigrng = uu____17499;
                      FStar_Syntax_Syntax.sigquals = uu____17500;
                      FStar_Syntax_Syntax.sigmeta = uu____17501;
                      FStar_Syntax_Syntax.sigattrs = uu____17502;
                      FStar_Syntax_Syntax.sigopts = uu____17503;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17546 =
                          let uu____17555 = inst_tscheme1 (uvs, k)  in
                          (uu____17555, rng)  in
                        FStar_Pervasives_Native.Some uu____17546
                    | uu____17576 ->
                        let uu____17577 =
                          let uu____17586 =
                            let uu____17591 =
                              let uu____17592 =
                                let uu____17595 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17595
                                 in
                              (uvs, uu____17592)  in
                            inst_tscheme1 uu____17591  in
                          (uu____17586, rng)  in
                        FStar_Pervasives_Native.Some uu____17577)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17618,uu____17619);
                      FStar_Syntax_Syntax.sigrng = uu____17620;
                      FStar_Syntax_Syntax.sigquals = uu____17621;
                      FStar_Syntax_Syntax.sigmeta = uu____17622;
                      FStar_Syntax_Syntax.sigattrs = uu____17623;
                      FStar_Syntax_Syntax.sigopts = uu____17624;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17668 =
                          let uu____17677 = inst_tscheme_with (uvs, k) us  in
                          (uu____17677, rng)  in
                        FStar_Pervasives_Native.Some uu____17668
                    | uu____17698 ->
                        let uu____17699 =
                          let uu____17708 =
                            let uu____17713 =
                              let uu____17714 =
                                let uu____17717 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17717
                                 in
                              (uvs, uu____17714)  in
                            inst_tscheme_with uu____17713 us  in
                          (uu____17708, rng)  in
                        FStar_Pervasives_Native.Some uu____17699)
               | FStar_Util.Inr se ->
                   let uu____17753 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17774;
                          FStar_Syntax_Syntax.sigrng = uu____17775;
                          FStar_Syntax_Syntax.sigquals = uu____17776;
                          FStar_Syntax_Syntax.sigmeta = uu____17777;
                          FStar_Syntax_Syntax.sigattrs = uu____17778;
                          FStar_Syntax_Syntax.sigopts = uu____17779;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17796 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17753
                     (FStar_Util.map_option
                        (fun uu____17844  ->
                           match uu____17844 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17875 =
          let uu____17886 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17886 mapper  in
        match uu____17875 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17960 =
              let uu____17971 =
                let uu____17978 =
                  let uu___843_17981 = t  in
                  let uu____17982 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___843_17981.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17982;
                    FStar_Syntax_Syntax.vars =
                      (uu___843_17981.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17978)  in
              (uu____17971, r)  in
            FStar_Pervasives_Native.Some uu____17960
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18031 = lookup_qname env l  in
      match uu____18031 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18052 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18106 = try_lookup_bv env bv  in
      match uu____18106 with
      | FStar_Pervasives_Native.None  ->
          let uu____18121 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18121 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18137 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18138 =
            let uu____18139 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18139  in
          (uu____18137, uu____18138)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18161 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18161 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18227 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18227  in
          let uu____18228 =
            let uu____18237 =
              let uu____18242 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18242)  in
            (uu____18237, r1)  in
          FStar_Pervasives_Native.Some uu____18228
  
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
        let uu____18277 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18277 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18310,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18335 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18335  in
            let uu____18336 =
              let uu____18341 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18341, r1)  in
            FStar_Pervasives_Native.Some uu____18336
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18365 = try_lookup_lid env l  in
      match uu____18365 with
      | FStar_Pervasives_Native.None  ->
          let uu____18392 = name_not_found l  in
          let uu____18398 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18392 uu____18398
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18441  ->
              match uu___5_18441 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18445 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18466 = lookup_qname env lid  in
      match uu____18466 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18475,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18478;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18480;
              FStar_Syntax_Syntax.sigattrs = uu____18481;
              FStar_Syntax_Syntax.sigopts = uu____18482;_},FStar_Pervasives_Native.None
            ),uu____18483)
          ->
          let uu____18534 =
            let uu____18541 =
              let uu____18542 =
                let uu____18545 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18545 t  in
              (uvs, uu____18542)  in
            (uu____18541, q)  in
          FStar_Pervasives_Native.Some uu____18534
      | uu____18558 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18580 = lookup_qname env lid  in
      match uu____18580 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18585,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18588;
              FStar_Syntax_Syntax.sigquals = uu____18589;
              FStar_Syntax_Syntax.sigmeta = uu____18590;
              FStar_Syntax_Syntax.sigattrs = uu____18591;
              FStar_Syntax_Syntax.sigopts = uu____18592;_},FStar_Pervasives_Native.None
            ),uu____18593)
          ->
          let uu____18644 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18644 (uvs, t)
      | uu____18649 ->
          let uu____18650 = name_not_found lid  in
          let uu____18656 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18650 uu____18656
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18676 = lookup_qname env lid  in
      match uu____18676 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18681,uvs,t,uu____18684,uu____18685,uu____18686);
              FStar_Syntax_Syntax.sigrng = uu____18687;
              FStar_Syntax_Syntax.sigquals = uu____18688;
              FStar_Syntax_Syntax.sigmeta = uu____18689;
              FStar_Syntax_Syntax.sigattrs = uu____18690;
              FStar_Syntax_Syntax.sigopts = uu____18691;_},FStar_Pervasives_Native.None
            ),uu____18692)
          ->
          let uu____18749 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18749 (uvs, t)
      | uu____18754 ->
          let uu____18755 = name_not_found lid  in
          let uu____18761 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18755 uu____18761
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18784 = lookup_qname env lid  in
      match uu____18784 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18792,uu____18793,uu____18794,uu____18795,uu____18796,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18798;
              FStar_Syntax_Syntax.sigquals = uu____18799;
              FStar_Syntax_Syntax.sigmeta = uu____18800;
              FStar_Syntax_Syntax.sigattrs = uu____18801;
              FStar_Syntax_Syntax.sigopts = uu____18802;_},uu____18803),uu____18804)
          -> (true, dcs)
      | uu____18869 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18885 = lookup_qname env lid  in
      match uu____18885 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18886,uu____18887,uu____18888,l,uu____18890,uu____18891);
              FStar_Syntax_Syntax.sigrng = uu____18892;
              FStar_Syntax_Syntax.sigquals = uu____18893;
              FStar_Syntax_Syntax.sigmeta = uu____18894;
              FStar_Syntax_Syntax.sigattrs = uu____18895;
              FStar_Syntax_Syntax.sigopts = uu____18896;_},uu____18897),uu____18898)
          -> l
      | uu____18957 ->
          let uu____18958 =
            let uu____18960 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18960  in
          failwith uu____18958
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19030)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19087) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19111 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19111
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19146 -> FStar_Pervasives_Native.None)
          | uu____19155 -> FStar_Pervasives_Native.None
  
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
        let uu____19217 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19217
  
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
        let uu____19250 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19250
  
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
             (FStar_Util.Inl uu____19302,uu____19303) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19352),uu____19353) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19402 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19420 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19430 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19447 ->
                  let uu____19454 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19454
              | FStar_Syntax_Syntax.Sig_let ((uu____19455,lbs),uu____19457)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19473 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19473
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19480 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19488 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19489 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19496 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19497 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19498 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19511 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____19512 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19540 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19540
           (fun d_opt  ->
              let uu____19553 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19553
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19563 =
                   let uu____19566 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19566  in
                 match uu____19563 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19567 =
                       let uu____19569 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19569
                        in
                     failwith uu____19567
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19574 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19574
                       then
                         let uu____19577 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19579 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19581 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19577 uu____19579 uu____19581
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
        (FStar_Util.Inr (se,uu____19606),uu____19607) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19656 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19678),uu____19679) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19728 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19750 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19750
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19783 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19783 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19805 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19814 =
                        let uu____19815 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19815.FStar_Syntax_Syntax.n  in
                      match uu____19814 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19820 -> false))
               in
            (true, uu____19805)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19843 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19843
  
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
          let uu____19915 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19915.FStar_Ident.str  in
        let uu____19916 = FStar_Util.smap_try_find tab s  in
        match uu____19916 with
        | FStar_Pervasives_Native.None  ->
            let uu____19919 = f ()  in
            (match uu____19919 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____19957 =
        let uu____19958 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____19958 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19992 =
        let uu____19993 = FStar_Syntax_Util.unrefine t  in
        uu____19993.FStar_Syntax_Syntax.n  in
      match uu____19992 with
      | FStar_Syntax_Syntax.Tm_type uu____19997 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20001) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20027) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20032,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20054 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20087 =
        let attrs =
          let uu____20093 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20093  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20133 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20133)
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
      let uu____20178 = lookup_qname env ftv  in
      match uu____20178 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20182) ->
          let uu____20227 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20227 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20248,t),r) ->
               let uu____20263 =
                 let uu____20264 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20264 t  in
               FStar_Pervasives_Native.Some uu____20263)
      | uu____20265 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20277 = try_lookup_effect_lid env ftv  in
      match uu____20277 with
      | FStar_Pervasives_Native.None  ->
          let uu____20280 = name_not_found ftv  in
          let uu____20286 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20280 uu____20286
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
        let uu____20310 = lookup_qname env lid0  in
        match uu____20310 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20321);
                FStar_Syntax_Syntax.sigrng = uu____20322;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20324;
                FStar_Syntax_Syntax.sigattrs = uu____20325;
                FStar_Syntax_Syntax.sigopts = uu____20326;_},FStar_Pervasives_Native.None
              ),uu____20327)
            ->
            let lid1 =
              let uu____20383 =
                let uu____20384 = FStar_Ident.range_of_lid lid  in
                let uu____20385 =
                  let uu____20386 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20386  in
                FStar_Range.set_use_range uu____20384 uu____20385  in
              FStar_Ident.set_lid_range lid uu____20383  in
            let uu____20387 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20393  ->
                      match uu___6_20393 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20396 -> false))
               in
            if uu____20387
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20415 =
                      let uu____20417 =
                        let uu____20419 = get_range env  in
                        FStar_Range.string_of_range uu____20419  in
                      let uu____20420 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20422 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20417 uu____20420 uu____20422
                       in
                    failwith uu____20415)
                  in
               match (binders, univs1) with
               | ([],uu____20443) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20469,uu____20470::uu____20471::uu____20472) ->
                   let uu____20493 =
                     let uu____20495 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20497 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20495 uu____20497
                      in
                   failwith uu____20493
               | uu____20508 ->
                   let uu____20523 =
                     let uu____20528 =
                       let uu____20529 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20529)  in
                     inst_tscheme_with uu____20528 insts  in
                   (match uu____20523 with
                    | (uu____20542,t) ->
                        let t1 =
                          let uu____20545 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20545 t  in
                        let uu____20546 =
                          let uu____20547 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20547.FStar_Syntax_Syntax.n  in
                        (match uu____20546 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20582 -> failwith "Impossible")))
        | uu____20590 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20614 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20614 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20627,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20634 = find1 l2  in
            (match uu____20634 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20641 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20641 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20645 = find1 l  in
            (match uu____20645 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20650 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20650
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____20671 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____20671 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____20677) ->
            FStar_List.length bs
        | uu____20716 ->
            let uu____20717 =
              let uu____20723 =
                let uu____20725 = FStar_Ident.string_of_lid name  in
                let uu____20727 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20725 uu____20727
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20723)
               in
            FStar_Errors.raise_error uu____20717 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20746 = lookup_qname env l1  in
      match uu____20746 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20749;
              FStar_Syntax_Syntax.sigrng = uu____20750;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20752;
              FStar_Syntax_Syntax.sigattrs = uu____20753;
              FStar_Syntax_Syntax.sigopts = uu____20754;_},uu____20755),uu____20756)
          -> q
      | uu____20809 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20833 =
          let uu____20834 =
            let uu____20836 = FStar_Util.string_of_int i  in
            let uu____20838 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20836 uu____20838
             in
          failwith uu____20834  in
        let uu____20841 = lookup_datacon env lid  in
        match uu____20841 with
        | (uu____20846,t) ->
            let uu____20848 =
              let uu____20849 = FStar_Syntax_Subst.compress t  in
              uu____20849.FStar_Syntax_Syntax.n  in
            (match uu____20848 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20853) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20897 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20897
                      FStar_Pervasives_Native.fst)
             | uu____20908 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20922 = lookup_qname env l  in
      match uu____20922 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20924,uu____20925,uu____20926);
              FStar_Syntax_Syntax.sigrng = uu____20927;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20929;
              FStar_Syntax_Syntax.sigattrs = uu____20930;
              FStar_Syntax_Syntax.sigopts = uu____20931;_},uu____20932),uu____20933)
          ->
          FStar_Util.for_some
            (fun uu___7_20988  ->
               match uu___7_20988 with
               | FStar_Syntax_Syntax.Projector uu____20990 -> true
               | uu____20996 -> false) quals
      | uu____20998 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21012 = lookup_qname env lid  in
      match uu____21012 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21014,uu____21015,uu____21016,uu____21017,uu____21018,uu____21019);
              FStar_Syntax_Syntax.sigrng = uu____21020;
              FStar_Syntax_Syntax.sigquals = uu____21021;
              FStar_Syntax_Syntax.sigmeta = uu____21022;
              FStar_Syntax_Syntax.sigattrs = uu____21023;
              FStar_Syntax_Syntax.sigopts = uu____21024;_},uu____21025),uu____21026)
          -> true
      | uu____21086 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21100 = lookup_qname env lid  in
      match uu____21100 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21102,uu____21103,uu____21104,uu____21105,uu____21106,uu____21107);
              FStar_Syntax_Syntax.sigrng = uu____21108;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21110;
              FStar_Syntax_Syntax.sigattrs = uu____21111;
              FStar_Syntax_Syntax.sigopts = uu____21112;_},uu____21113),uu____21114)
          ->
          FStar_Util.for_some
            (fun uu___8_21177  ->
               match uu___8_21177 with
               | FStar_Syntax_Syntax.RecordType uu____21179 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21189 -> true
               | uu____21199 -> false) quals
      | uu____21201 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21211,uu____21212);
            FStar_Syntax_Syntax.sigrng = uu____21213;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21215;
            FStar_Syntax_Syntax.sigattrs = uu____21216;
            FStar_Syntax_Syntax.sigopts = uu____21217;_},uu____21218),uu____21219)
        ->
        FStar_Util.for_some
          (fun uu___9_21278  ->
             match uu___9_21278 with
             | FStar_Syntax_Syntax.Action uu____21280 -> true
             | uu____21282 -> false) quals
    | uu____21284 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21298 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21298
  
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
      let uu____21315 =
        let uu____21316 = FStar_Syntax_Util.un_uinst head1  in
        uu____21316.FStar_Syntax_Syntax.n  in
      match uu____21315 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21322 ->
               true
           | uu____21325 -> false)
      | uu____21327 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21341 = lookup_qname env l  in
      match uu____21341 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21344),uu____21345) ->
          FStar_Util.for_some
            (fun uu___10_21393  ->
               match uu___10_21393 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21396 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21398 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21474 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21492) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21510 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21518 ->
                 FStar_Pervasives_Native.Some true
             | uu____21537 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21540 =
        let uu____21544 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21544 mapper  in
      match uu____21540 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21604 = lookup_qname env lid  in
      match uu____21604 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21608,uu____21609,tps,uu____21611,uu____21612,uu____21613);
              FStar_Syntax_Syntax.sigrng = uu____21614;
              FStar_Syntax_Syntax.sigquals = uu____21615;
              FStar_Syntax_Syntax.sigmeta = uu____21616;
              FStar_Syntax_Syntax.sigattrs = uu____21617;
              FStar_Syntax_Syntax.sigopts = uu____21618;_},uu____21619),uu____21620)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21688 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21734  ->
              match uu____21734 with
              | (d,uu____21743) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21759 = effect_decl_opt env l  in
      match uu____21759 with
      | FStar_Pervasives_Native.None  ->
          let uu____21774 = name_not_found l  in
          let uu____21780 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21774 uu____21780
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21808 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____21808 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____21815  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21829  ->
            fun uu____21830  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21860 = FStar_Ident.lid_equals l1 l2  in
        if uu____21860
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21871 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21871
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21882 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21935  ->
                        match uu____21935 with
                        | (m1,m2,uu____21949,uu____21950,uu____21951) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21882 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21968 =
                    let uu____21974 =
                      let uu____21976 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21978 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21976
                        uu____21978
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21974)
                     in
                  FStar_Errors.raise_error uu____21968 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21988,uu____21989,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22023 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22023
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
  'Auu____22043 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22043) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22072 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22098  ->
                match uu____22098 with
                | (d,uu____22105) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22072 with
      | FStar_Pervasives_Native.None  ->
          let uu____22116 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22116
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22131 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22131 with
           | (uu____22142,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22160)::(wp,uu____22162)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22218 -> failwith "Impossible"))
  
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
        | uu____22283 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22296 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22296 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22313 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22313 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22338 =
                     let uu____22344 =
                       let uu____22346 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22354 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22365 =
                         let uu____22367 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22367  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22346 uu____22354 uu____22365
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22344)
                      in
                   FStar_Errors.raise_error uu____22338
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22375 =
                     let uu____22386 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22386 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22423  ->
                        fun uu____22424  ->
                          match (uu____22423, uu____22424) with
                          | ((x,uu____22454),(t,uu____22456)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22375
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22487 =
                     let uu___1591_22488 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1591_22488.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1591_22488.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1591_22488.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1591_22488.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22487
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22500 .
    'Auu____22500 ->
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
            let uu____22541 =
              let uu____22548 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____22548)  in
            match uu____22541 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____22572 = FStar_Ident.string_of_lid eff_name  in
                     let uu____22574 = FStar_Util.string_of_int given  in
                     let uu____22576 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____22572 uu____22574 uu____22576
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____22581 = effect_decl_opt env effect_name  in
          match uu____22581 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____22603) ->
              let uu____22614 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____22614 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____22632 =
                       let uu____22635 = get_range env  in
                       let uu____22636 =
                         let uu____22643 =
                           let uu____22644 =
                             let uu____22661 =
                               let uu____22672 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____22672 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____22661)  in
                           FStar_Syntax_Syntax.Tm_app uu____22644  in
                         FStar_Syntax_Syntax.mk uu____22643  in
                       uu____22636 FStar_Pervasives_Native.None uu____22635
                        in
                     FStar_Pervasives_Native.Some uu____22632)))
  
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
           (fun uu___11_22772  ->
              match uu___11_22772 with
              | FStar_Syntax_Syntax.Reflectable uu____22774 -> true
              | uu____22776 -> false))
  
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
      | uu____22836 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22851 =
        let uu____22852 = FStar_Syntax_Subst.compress t  in
        uu____22852.FStar_Syntax_Syntax.n  in
      match uu____22851 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22856,c) ->
          is_reifiable_comp env c
      | uu____22878 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22898 =
           let uu____22900 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22900  in
         if uu____22898
         then
           let uu____22903 =
             let uu____22909 =
               let uu____22911 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22911
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22909)  in
           let uu____22915 = get_range env  in
           FStar_Errors.raise_error uu____22903 uu____22915
         else ());
        (let uu____22918 = effect_repr_aux true env c u_c  in
         match uu____22918 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1668_22954 = env  in
        {
          solver = (uu___1668_22954.solver);
          range = (uu___1668_22954.range);
          curmodule = (uu___1668_22954.curmodule);
          gamma = (uu___1668_22954.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1668_22954.gamma_cache);
          modules = (uu___1668_22954.modules);
          expected_typ = (uu___1668_22954.expected_typ);
          sigtab = (uu___1668_22954.sigtab);
          attrtab = (uu___1668_22954.attrtab);
          instantiate_imp = (uu___1668_22954.instantiate_imp);
          effects = (uu___1668_22954.effects);
          generalize = (uu___1668_22954.generalize);
          letrecs = (uu___1668_22954.letrecs);
          top_level = (uu___1668_22954.top_level);
          check_uvars = (uu___1668_22954.check_uvars);
          use_eq = (uu___1668_22954.use_eq);
          is_iface = (uu___1668_22954.is_iface);
          admit = (uu___1668_22954.admit);
          lax = (uu___1668_22954.lax);
          lax_universes = (uu___1668_22954.lax_universes);
          phase1 = (uu___1668_22954.phase1);
          failhard = (uu___1668_22954.failhard);
          nosynth = (uu___1668_22954.nosynth);
          uvar_subtyping = (uu___1668_22954.uvar_subtyping);
          tc_term = (uu___1668_22954.tc_term);
          type_of = (uu___1668_22954.type_of);
          universe_of = (uu___1668_22954.universe_of);
          check_type_of = (uu___1668_22954.check_type_of);
          use_bv_sorts = (uu___1668_22954.use_bv_sorts);
          qtbl_name_and_index = (uu___1668_22954.qtbl_name_and_index);
          normalized_eff_names = (uu___1668_22954.normalized_eff_names);
          fv_delta_depths = (uu___1668_22954.fv_delta_depths);
          proof_ns = (uu___1668_22954.proof_ns);
          synth_hook = (uu___1668_22954.synth_hook);
          splice = (uu___1668_22954.splice);
          mpreprocess = (uu___1668_22954.mpreprocess);
          postprocess = (uu___1668_22954.postprocess);
          is_native_tactic = (uu___1668_22954.is_native_tactic);
          identifier_info = (uu___1668_22954.identifier_info);
          tc_hooks = (uu___1668_22954.tc_hooks);
          dsenv = (uu___1668_22954.dsenv);
          nbe = (uu___1668_22954.nbe);
          strict_args_tab = (uu___1668_22954.strict_args_tab);
          erasable_types_tab = (uu___1668_22954.erasable_types_tab)
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
    fun uu____22973  ->
      match uu____22973 with
      | (ed,quals) ->
          let effects =
            let uu___1677_22987 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1677_22987.order);
              joins = (uu___1677_22987.joins)
            }  in
          let uu___1680_22996 = env  in
          {
            solver = (uu___1680_22996.solver);
            range = (uu___1680_22996.range);
            curmodule = (uu___1680_22996.curmodule);
            gamma = (uu___1680_22996.gamma);
            gamma_sig = (uu___1680_22996.gamma_sig);
            gamma_cache = (uu___1680_22996.gamma_cache);
            modules = (uu___1680_22996.modules);
            expected_typ = (uu___1680_22996.expected_typ);
            sigtab = (uu___1680_22996.sigtab);
            attrtab = (uu___1680_22996.attrtab);
            instantiate_imp = (uu___1680_22996.instantiate_imp);
            effects;
            generalize = (uu___1680_22996.generalize);
            letrecs = (uu___1680_22996.letrecs);
            top_level = (uu___1680_22996.top_level);
            check_uvars = (uu___1680_22996.check_uvars);
            use_eq = (uu___1680_22996.use_eq);
            is_iface = (uu___1680_22996.is_iface);
            admit = (uu___1680_22996.admit);
            lax = (uu___1680_22996.lax);
            lax_universes = (uu___1680_22996.lax_universes);
            phase1 = (uu___1680_22996.phase1);
            failhard = (uu___1680_22996.failhard);
            nosynth = (uu___1680_22996.nosynth);
            uvar_subtyping = (uu___1680_22996.uvar_subtyping);
            tc_term = (uu___1680_22996.tc_term);
            type_of = (uu___1680_22996.type_of);
            universe_of = (uu___1680_22996.universe_of);
            check_type_of = (uu___1680_22996.check_type_of);
            use_bv_sorts = (uu___1680_22996.use_bv_sorts);
            qtbl_name_and_index = (uu___1680_22996.qtbl_name_and_index);
            normalized_eff_names = (uu___1680_22996.normalized_eff_names);
            fv_delta_depths = (uu___1680_22996.fv_delta_depths);
            proof_ns = (uu___1680_22996.proof_ns);
            synth_hook = (uu___1680_22996.synth_hook);
            splice = (uu___1680_22996.splice);
            mpreprocess = (uu___1680_22996.mpreprocess);
            postprocess = (uu___1680_22996.postprocess);
            is_native_tactic = (uu___1680_22996.is_native_tactic);
            identifier_info = (uu___1680_22996.identifier_info);
            tc_hooks = (uu___1680_22996.tc_hooks);
            dsenv = (uu___1680_22996.dsenv);
            nbe = (uu___1680_22996.nbe);
            strict_args_tab = (uu___1680_22996.strict_args_tab);
            erasable_types_tab = (uu___1680_22996.erasable_types_tab)
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
                let uu____23045 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____23045
                  (fun uu____23066  ->
                     match uu____23066 with
                     | (c1,g1) ->
                         let uu____23077 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____23077
                           (fun uu____23098  ->
                              match uu____23098 with
                              | (c2,g2) ->
                                  let uu____23109 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____23109)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____23231 = l1 u t e  in
                              l2 u t uu____23231))
                | uu____23232 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____23300  ->
                    match uu____23300 with
                    | (e,uu____23308) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____23331 =
            match uu____23331 with
            | (i,j) ->
                let uu____23342 = FStar_Ident.lid_equals i j  in
                if uu____23342
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _23349  -> FStar_Pervasives_Native.Some _23349)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____23378 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____23388 = FStar_Ident.lid_equals i k  in
                        if uu____23388
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____23402 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____23402
                                  then []
                                  else
                                    (let uu____23409 =
                                       let uu____23418 =
                                         find_edge order1 (i, k)  in
                                       let uu____23421 =
                                         find_edge order1 (k, j)  in
                                       (uu____23418, uu____23421)  in
                                     match uu____23409 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____23436 =
                                           compose_edges e1 e2  in
                                         [uu____23436]
                                     | uu____23437 -> [])))))
                 in
              FStar_List.append order1 uu____23378  in
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
                  let uu____23467 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____23470 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____23470
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____23467
                  then
                    let uu____23477 =
                      let uu____23483 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____23483)
                       in
                    let uu____23487 = get_range env  in
                    FStar_Errors.raise_error uu____23477 uu____23487
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt =
                               let uu____23565 = FStar_Ident.lid_equals i j
                                  in
                               if uu____23565
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____23617 =
                                             let uu____23626 =
                                               find_edge order2 (i, k)  in
                                             let uu____23629 =
                                               find_edge order2 (j, k)  in
                                             (uu____23626, uu____23629)  in
                                           match uu____23617 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____23671,uu____23672)
                                                    ->
                                                    let uu____23679 =
                                                      let uu____23686 =
                                                        let uu____23688 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23688
                                                         in
                                                      let uu____23691 =
                                                        let uu____23693 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____23693
                                                         in
                                                      (uu____23686,
                                                        uu____23691)
                                                       in
                                                    (match uu____23679 with
                                                     | (true ,true ) ->
                                                         let uu____23710 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____23710
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
                                           | uu____23753 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1785_23826 = env.effects  in
             { decls = (uu___1785_23826.decls); order = order2; joins }  in
           let uu___1788_23827 = env  in
           {
             solver = (uu___1788_23827.solver);
             range = (uu___1788_23827.range);
             curmodule = (uu___1788_23827.curmodule);
             gamma = (uu___1788_23827.gamma);
             gamma_sig = (uu___1788_23827.gamma_sig);
             gamma_cache = (uu___1788_23827.gamma_cache);
             modules = (uu___1788_23827.modules);
             expected_typ = (uu___1788_23827.expected_typ);
             sigtab = (uu___1788_23827.sigtab);
             attrtab = (uu___1788_23827.attrtab);
             instantiate_imp = (uu___1788_23827.instantiate_imp);
             effects;
             generalize = (uu___1788_23827.generalize);
             letrecs = (uu___1788_23827.letrecs);
             top_level = (uu___1788_23827.top_level);
             check_uvars = (uu___1788_23827.check_uvars);
             use_eq = (uu___1788_23827.use_eq);
             is_iface = (uu___1788_23827.is_iface);
             admit = (uu___1788_23827.admit);
             lax = (uu___1788_23827.lax);
             lax_universes = (uu___1788_23827.lax_universes);
             phase1 = (uu___1788_23827.phase1);
             failhard = (uu___1788_23827.failhard);
             nosynth = (uu___1788_23827.nosynth);
             uvar_subtyping = (uu___1788_23827.uvar_subtyping);
             tc_term = (uu___1788_23827.tc_term);
             type_of = (uu___1788_23827.type_of);
             universe_of = (uu___1788_23827.universe_of);
             check_type_of = (uu___1788_23827.check_type_of);
             use_bv_sorts = (uu___1788_23827.use_bv_sorts);
             qtbl_name_and_index = (uu___1788_23827.qtbl_name_and_index);
             normalized_eff_names = (uu___1788_23827.normalized_eff_names);
             fv_delta_depths = (uu___1788_23827.fv_delta_depths);
             proof_ns = (uu___1788_23827.proof_ns);
             synth_hook = (uu___1788_23827.synth_hook);
             splice = (uu___1788_23827.splice);
             mpreprocess = (uu___1788_23827.mpreprocess);
             postprocess = (uu___1788_23827.postprocess);
             is_native_tactic = (uu___1788_23827.is_native_tactic);
             identifier_info = (uu___1788_23827.identifier_info);
             tc_hooks = (uu___1788_23827.tc_hooks);
             dsenv = (uu___1788_23827.dsenv);
             nbe = (uu___1788_23827.nbe);
             strict_args_tab = (uu___1788_23827.strict_args_tab);
             erasable_types_tab = (uu___1788_23827.erasable_types_tab)
           })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1792_23839 = env  in
      {
        solver = (uu___1792_23839.solver);
        range = (uu___1792_23839.range);
        curmodule = (uu___1792_23839.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1792_23839.gamma_sig);
        gamma_cache = (uu___1792_23839.gamma_cache);
        modules = (uu___1792_23839.modules);
        expected_typ = (uu___1792_23839.expected_typ);
        sigtab = (uu___1792_23839.sigtab);
        attrtab = (uu___1792_23839.attrtab);
        instantiate_imp = (uu___1792_23839.instantiate_imp);
        effects = (uu___1792_23839.effects);
        generalize = (uu___1792_23839.generalize);
        letrecs = (uu___1792_23839.letrecs);
        top_level = (uu___1792_23839.top_level);
        check_uvars = (uu___1792_23839.check_uvars);
        use_eq = (uu___1792_23839.use_eq);
        is_iface = (uu___1792_23839.is_iface);
        admit = (uu___1792_23839.admit);
        lax = (uu___1792_23839.lax);
        lax_universes = (uu___1792_23839.lax_universes);
        phase1 = (uu___1792_23839.phase1);
        failhard = (uu___1792_23839.failhard);
        nosynth = (uu___1792_23839.nosynth);
        uvar_subtyping = (uu___1792_23839.uvar_subtyping);
        tc_term = (uu___1792_23839.tc_term);
        type_of = (uu___1792_23839.type_of);
        universe_of = (uu___1792_23839.universe_of);
        check_type_of = (uu___1792_23839.check_type_of);
        use_bv_sorts = (uu___1792_23839.use_bv_sorts);
        qtbl_name_and_index = (uu___1792_23839.qtbl_name_and_index);
        normalized_eff_names = (uu___1792_23839.normalized_eff_names);
        fv_delta_depths = (uu___1792_23839.fv_delta_depths);
        proof_ns = (uu___1792_23839.proof_ns);
        synth_hook = (uu___1792_23839.synth_hook);
        splice = (uu___1792_23839.splice);
        mpreprocess = (uu___1792_23839.mpreprocess);
        postprocess = (uu___1792_23839.postprocess);
        is_native_tactic = (uu___1792_23839.is_native_tactic);
        identifier_info = (uu___1792_23839.identifier_info);
        tc_hooks = (uu___1792_23839.tc_hooks);
        dsenv = (uu___1792_23839.dsenv);
        nbe = (uu___1792_23839.nbe);
        strict_args_tab = (uu___1792_23839.strict_args_tab);
        erasable_types_tab = (uu___1792_23839.erasable_types_tab)
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
            (let uu___1805_23897 = env  in
             {
               solver = (uu___1805_23897.solver);
               range = (uu___1805_23897.range);
               curmodule = (uu___1805_23897.curmodule);
               gamma = rest;
               gamma_sig = (uu___1805_23897.gamma_sig);
               gamma_cache = (uu___1805_23897.gamma_cache);
               modules = (uu___1805_23897.modules);
               expected_typ = (uu___1805_23897.expected_typ);
               sigtab = (uu___1805_23897.sigtab);
               attrtab = (uu___1805_23897.attrtab);
               instantiate_imp = (uu___1805_23897.instantiate_imp);
               effects = (uu___1805_23897.effects);
               generalize = (uu___1805_23897.generalize);
               letrecs = (uu___1805_23897.letrecs);
               top_level = (uu___1805_23897.top_level);
               check_uvars = (uu___1805_23897.check_uvars);
               use_eq = (uu___1805_23897.use_eq);
               is_iface = (uu___1805_23897.is_iface);
               admit = (uu___1805_23897.admit);
               lax = (uu___1805_23897.lax);
               lax_universes = (uu___1805_23897.lax_universes);
               phase1 = (uu___1805_23897.phase1);
               failhard = (uu___1805_23897.failhard);
               nosynth = (uu___1805_23897.nosynth);
               uvar_subtyping = (uu___1805_23897.uvar_subtyping);
               tc_term = (uu___1805_23897.tc_term);
               type_of = (uu___1805_23897.type_of);
               universe_of = (uu___1805_23897.universe_of);
               check_type_of = (uu___1805_23897.check_type_of);
               use_bv_sorts = (uu___1805_23897.use_bv_sorts);
               qtbl_name_and_index = (uu___1805_23897.qtbl_name_and_index);
               normalized_eff_names = (uu___1805_23897.normalized_eff_names);
               fv_delta_depths = (uu___1805_23897.fv_delta_depths);
               proof_ns = (uu___1805_23897.proof_ns);
               synth_hook = (uu___1805_23897.synth_hook);
               splice = (uu___1805_23897.splice);
               mpreprocess = (uu___1805_23897.mpreprocess);
               postprocess = (uu___1805_23897.postprocess);
               is_native_tactic = (uu___1805_23897.is_native_tactic);
               identifier_info = (uu___1805_23897.identifier_info);
               tc_hooks = (uu___1805_23897.tc_hooks);
               dsenv = (uu___1805_23897.dsenv);
               nbe = (uu___1805_23897.nbe);
               strict_args_tab = (uu___1805_23897.strict_args_tab);
               erasable_types_tab = (uu___1805_23897.erasable_types_tab)
             }))
    | uu____23898 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23927  ->
             match uu____23927 with | (x,uu____23935) -> push_bv env1 x) env
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
            let uu___1819_23970 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1819_23970.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1819_23970.FStar_Syntax_Syntax.index);
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
        let uu____24043 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24043 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24071 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24071)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1840_24087 = env  in
      {
        solver = (uu___1840_24087.solver);
        range = (uu___1840_24087.range);
        curmodule = (uu___1840_24087.curmodule);
        gamma = (uu___1840_24087.gamma);
        gamma_sig = (uu___1840_24087.gamma_sig);
        gamma_cache = (uu___1840_24087.gamma_cache);
        modules = (uu___1840_24087.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1840_24087.sigtab);
        attrtab = (uu___1840_24087.attrtab);
        instantiate_imp = (uu___1840_24087.instantiate_imp);
        effects = (uu___1840_24087.effects);
        generalize = (uu___1840_24087.generalize);
        letrecs = (uu___1840_24087.letrecs);
        top_level = (uu___1840_24087.top_level);
        check_uvars = (uu___1840_24087.check_uvars);
        use_eq = false;
        is_iface = (uu___1840_24087.is_iface);
        admit = (uu___1840_24087.admit);
        lax = (uu___1840_24087.lax);
        lax_universes = (uu___1840_24087.lax_universes);
        phase1 = (uu___1840_24087.phase1);
        failhard = (uu___1840_24087.failhard);
        nosynth = (uu___1840_24087.nosynth);
        uvar_subtyping = (uu___1840_24087.uvar_subtyping);
        tc_term = (uu___1840_24087.tc_term);
        type_of = (uu___1840_24087.type_of);
        universe_of = (uu___1840_24087.universe_of);
        check_type_of = (uu___1840_24087.check_type_of);
        use_bv_sorts = (uu___1840_24087.use_bv_sorts);
        qtbl_name_and_index = (uu___1840_24087.qtbl_name_and_index);
        normalized_eff_names = (uu___1840_24087.normalized_eff_names);
        fv_delta_depths = (uu___1840_24087.fv_delta_depths);
        proof_ns = (uu___1840_24087.proof_ns);
        synth_hook = (uu___1840_24087.synth_hook);
        splice = (uu___1840_24087.splice);
        mpreprocess = (uu___1840_24087.mpreprocess);
        postprocess = (uu___1840_24087.postprocess);
        is_native_tactic = (uu___1840_24087.is_native_tactic);
        identifier_info = (uu___1840_24087.identifier_info);
        tc_hooks = (uu___1840_24087.tc_hooks);
        dsenv = (uu___1840_24087.dsenv);
        nbe = (uu___1840_24087.nbe);
        strict_args_tab = (uu___1840_24087.strict_args_tab);
        erasable_types_tab = (uu___1840_24087.erasable_types_tab)
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
    let uu____24118 = expected_typ env_  in
    ((let uu___1847_24124 = env_  in
      {
        solver = (uu___1847_24124.solver);
        range = (uu___1847_24124.range);
        curmodule = (uu___1847_24124.curmodule);
        gamma = (uu___1847_24124.gamma);
        gamma_sig = (uu___1847_24124.gamma_sig);
        gamma_cache = (uu___1847_24124.gamma_cache);
        modules = (uu___1847_24124.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1847_24124.sigtab);
        attrtab = (uu___1847_24124.attrtab);
        instantiate_imp = (uu___1847_24124.instantiate_imp);
        effects = (uu___1847_24124.effects);
        generalize = (uu___1847_24124.generalize);
        letrecs = (uu___1847_24124.letrecs);
        top_level = (uu___1847_24124.top_level);
        check_uvars = (uu___1847_24124.check_uvars);
        use_eq = false;
        is_iface = (uu___1847_24124.is_iface);
        admit = (uu___1847_24124.admit);
        lax = (uu___1847_24124.lax);
        lax_universes = (uu___1847_24124.lax_universes);
        phase1 = (uu___1847_24124.phase1);
        failhard = (uu___1847_24124.failhard);
        nosynth = (uu___1847_24124.nosynth);
        uvar_subtyping = (uu___1847_24124.uvar_subtyping);
        tc_term = (uu___1847_24124.tc_term);
        type_of = (uu___1847_24124.type_of);
        universe_of = (uu___1847_24124.universe_of);
        check_type_of = (uu___1847_24124.check_type_of);
        use_bv_sorts = (uu___1847_24124.use_bv_sorts);
        qtbl_name_and_index = (uu___1847_24124.qtbl_name_and_index);
        normalized_eff_names = (uu___1847_24124.normalized_eff_names);
        fv_delta_depths = (uu___1847_24124.fv_delta_depths);
        proof_ns = (uu___1847_24124.proof_ns);
        synth_hook = (uu___1847_24124.synth_hook);
        splice = (uu___1847_24124.splice);
        mpreprocess = (uu___1847_24124.mpreprocess);
        postprocess = (uu___1847_24124.postprocess);
        is_native_tactic = (uu___1847_24124.is_native_tactic);
        identifier_info = (uu___1847_24124.identifier_info);
        tc_hooks = (uu___1847_24124.tc_hooks);
        dsenv = (uu___1847_24124.dsenv);
        nbe = (uu___1847_24124.nbe);
        strict_args_tab = (uu___1847_24124.strict_args_tab);
        erasable_types_tab = (uu___1847_24124.erasable_types_tab)
      }), uu____24118)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24136 =
      let uu____24139 = FStar_Ident.id_of_text ""  in [uu____24139]  in
    FStar_Ident.lid_of_ids uu____24136  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24146 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24146
        then
          let uu____24151 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24151 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1855_24179 = env  in
       {
         solver = (uu___1855_24179.solver);
         range = (uu___1855_24179.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1855_24179.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1855_24179.expected_typ);
         sigtab = (uu___1855_24179.sigtab);
         attrtab = (uu___1855_24179.attrtab);
         instantiate_imp = (uu___1855_24179.instantiate_imp);
         effects = (uu___1855_24179.effects);
         generalize = (uu___1855_24179.generalize);
         letrecs = (uu___1855_24179.letrecs);
         top_level = (uu___1855_24179.top_level);
         check_uvars = (uu___1855_24179.check_uvars);
         use_eq = (uu___1855_24179.use_eq);
         is_iface = (uu___1855_24179.is_iface);
         admit = (uu___1855_24179.admit);
         lax = (uu___1855_24179.lax);
         lax_universes = (uu___1855_24179.lax_universes);
         phase1 = (uu___1855_24179.phase1);
         failhard = (uu___1855_24179.failhard);
         nosynth = (uu___1855_24179.nosynth);
         uvar_subtyping = (uu___1855_24179.uvar_subtyping);
         tc_term = (uu___1855_24179.tc_term);
         type_of = (uu___1855_24179.type_of);
         universe_of = (uu___1855_24179.universe_of);
         check_type_of = (uu___1855_24179.check_type_of);
         use_bv_sorts = (uu___1855_24179.use_bv_sorts);
         qtbl_name_and_index = (uu___1855_24179.qtbl_name_and_index);
         normalized_eff_names = (uu___1855_24179.normalized_eff_names);
         fv_delta_depths = (uu___1855_24179.fv_delta_depths);
         proof_ns = (uu___1855_24179.proof_ns);
         synth_hook = (uu___1855_24179.synth_hook);
         splice = (uu___1855_24179.splice);
         mpreprocess = (uu___1855_24179.mpreprocess);
         postprocess = (uu___1855_24179.postprocess);
         is_native_tactic = (uu___1855_24179.is_native_tactic);
         identifier_info = (uu___1855_24179.identifier_info);
         tc_hooks = (uu___1855_24179.tc_hooks);
         dsenv = (uu___1855_24179.dsenv);
         nbe = (uu___1855_24179.nbe);
         strict_args_tab = (uu___1855_24179.strict_args_tab);
         erasable_types_tab = (uu___1855_24179.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24231)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24235,(uu____24236,t)))::tl1
          ->
          let uu____24257 =
            let uu____24260 = FStar_Syntax_Free.uvars t  in
            ext out uu____24260  in
          aux uu____24257 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24263;
            FStar_Syntax_Syntax.index = uu____24264;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24272 =
            let uu____24275 = FStar_Syntax_Free.uvars t  in
            ext out uu____24275  in
          aux uu____24272 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24333)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24337,(uu____24338,t)))::tl1
          ->
          let uu____24359 =
            let uu____24362 = FStar_Syntax_Free.univs t  in
            ext out uu____24362  in
          aux uu____24359 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24365;
            FStar_Syntax_Syntax.index = uu____24366;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24374 =
            let uu____24377 = FStar_Syntax_Free.univs t  in
            ext out uu____24377  in
          aux uu____24374 tl1
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
          let uu____24439 = FStar_Util.set_add uname out  in
          aux uu____24439 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24442,(uu____24443,t)))::tl1
          ->
          let uu____24464 =
            let uu____24467 = FStar_Syntax_Free.univnames t  in
            ext out uu____24467  in
          aux uu____24464 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24470;
            FStar_Syntax_Syntax.index = uu____24471;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24479 =
            let uu____24482 = FStar_Syntax_Free.univnames t  in
            ext out uu____24482  in
          aux uu____24479 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24503  ->
            match uu___12_24503 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24507 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24520 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24531 =
      let uu____24540 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24540
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24531 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24588 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24601  ->
              match uu___13_24601 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24604 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24604
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24610) ->
                  let uu____24627 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24627))
       in
    FStar_All.pipe_right uu____24588 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24641  ->
    match uu___14_24641 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24647 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24647
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24670  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24725) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24758,uu____24759) -> false  in
      let uu____24773 =
        FStar_List.tryFind
          (fun uu____24795  ->
             match uu____24795 with | (p,uu____24806) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24773 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24825,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24855 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24855
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1998_24877 = e  in
        {
          solver = (uu___1998_24877.solver);
          range = (uu___1998_24877.range);
          curmodule = (uu___1998_24877.curmodule);
          gamma = (uu___1998_24877.gamma);
          gamma_sig = (uu___1998_24877.gamma_sig);
          gamma_cache = (uu___1998_24877.gamma_cache);
          modules = (uu___1998_24877.modules);
          expected_typ = (uu___1998_24877.expected_typ);
          sigtab = (uu___1998_24877.sigtab);
          attrtab = (uu___1998_24877.attrtab);
          instantiate_imp = (uu___1998_24877.instantiate_imp);
          effects = (uu___1998_24877.effects);
          generalize = (uu___1998_24877.generalize);
          letrecs = (uu___1998_24877.letrecs);
          top_level = (uu___1998_24877.top_level);
          check_uvars = (uu___1998_24877.check_uvars);
          use_eq = (uu___1998_24877.use_eq);
          is_iface = (uu___1998_24877.is_iface);
          admit = (uu___1998_24877.admit);
          lax = (uu___1998_24877.lax);
          lax_universes = (uu___1998_24877.lax_universes);
          phase1 = (uu___1998_24877.phase1);
          failhard = (uu___1998_24877.failhard);
          nosynth = (uu___1998_24877.nosynth);
          uvar_subtyping = (uu___1998_24877.uvar_subtyping);
          tc_term = (uu___1998_24877.tc_term);
          type_of = (uu___1998_24877.type_of);
          universe_of = (uu___1998_24877.universe_of);
          check_type_of = (uu___1998_24877.check_type_of);
          use_bv_sorts = (uu___1998_24877.use_bv_sorts);
          qtbl_name_and_index = (uu___1998_24877.qtbl_name_and_index);
          normalized_eff_names = (uu___1998_24877.normalized_eff_names);
          fv_delta_depths = (uu___1998_24877.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1998_24877.synth_hook);
          splice = (uu___1998_24877.splice);
          mpreprocess = (uu___1998_24877.mpreprocess);
          postprocess = (uu___1998_24877.postprocess);
          is_native_tactic = (uu___1998_24877.is_native_tactic);
          identifier_info = (uu___1998_24877.identifier_info);
          tc_hooks = (uu___1998_24877.tc_hooks);
          dsenv = (uu___1998_24877.dsenv);
          nbe = (uu___1998_24877.nbe);
          strict_args_tab = (uu___1998_24877.strict_args_tab);
          erasable_types_tab = (uu___1998_24877.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2007_24925 = e  in
      {
        solver = (uu___2007_24925.solver);
        range = (uu___2007_24925.range);
        curmodule = (uu___2007_24925.curmodule);
        gamma = (uu___2007_24925.gamma);
        gamma_sig = (uu___2007_24925.gamma_sig);
        gamma_cache = (uu___2007_24925.gamma_cache);
        modules = (uu___2007_24925.modules);
        expected_typ = (uu___2007_24925.expected_typ);
        sigtab = (uu___2007_24925.sigtab);
        attrtab = (uu___2007_24925.attrtab);
        instantiate_imp = (uu___2007_24925.instantiate_imp);
        effects = (uu___2007_24925.effects);
        generalize = (uu___2007_24925.generalize);
        letrecs = (uu___2007_24925.letrecs);
        top_level = (uu___2007_24925.top_level);
        check_uvars = (uu___2007_24925.check_uvars);
        use_eq = (uu___2007_24925.use_eq);
        is_iface = (uu___2007_24925.is_iface);
        admit = (uu___2007_24925.admit);
        lax = (uu___2007_24925.lax);
        lax_universes = (uu___2007_24925.lax_universes);
        phase1 = (uu___2007_24925.phase1);
        failhard = (uu___2007_24925.failhard);
        nosynth = (uu___2007_24925.nosynth);
        uvar_subtyping = (uu___2007_24925.uvar_subtyping);
        tc_term = (uu___2007_24925.tc_term);
        type_of = (uu___2007_24925.type_of);
        universe_of = (uu___2007_24925.universe_of);
        check_type_of = (uu___2007_24925.check_type_of);
        use_bv_sorts = (uu___2007_24925.use_bv_sorts);
        qtbl_name_and_index = (uu___2007_24925.qtbl_name_and_index);
        normalized_eff_names = (uu___2007_24925.normalized_eff_names);
        fv_delta_depths = (uu___2007_24925.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2007_24925.synth_hook);
        splice = (uu___2007_24925.splice);
        mpreprocess = (uu___2007_24925.mpreprocess);
        postprocess = (uu___2007_24925.postprocess);
        is_native_tactic = (uu___2007_24925.is_native_tactic);
        identifier_info = (uu___2007_24925.identifier_info);
        tc_hooks = (uu___2007_24925.tc_hooks);
        dsenv = (uu___2007_24925.dsenv);
        nbe = (uu___2007_24925.nbe);
        strict_args_tab = (uu___2007_24925.strict_args_tab);
        erasable_types_tab = (uu___2007_24925.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24941 = FStar_Syntax_Free.names t  in
      let uu____24944 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24941 uu____24944
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24967 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24967
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24977 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24977
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24998 =
      match uu____24998 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25018 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25018)
       in
    let uu____25026 =
      let uu____25030 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25030 FStar_List.rev  in
    FStar_All.pipe_right uu____25026 (FStar_String.concat " ")
  
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
                  (let uu____25098 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25098 with
                   | FStar_Pervasives_Native.Some uu____25102 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25105 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25115;
        FStar_TypeChecker_Common.univ_ineqs = uu____25116;
        FStar_TypeChecker_Common.implicits = uu____25117;_} -> true
    | uu____25127 -> false
  
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
          let uu___2051_25149 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2051_25149.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2051_25149.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2051_25149.FStar_TypeChecker_Common.implicits)
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
          let uu____25188 = FStar_Options.defensive ()  in
          if uu____25188
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25194 =
              let uu____25196 =
                let uu____25198 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25198  in
              Prims.op_Negation uu____25196  in
            (if uu____25194
             then
               let uu____25205 =
                 let uu____25211 =
                   let uu____25213 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25215 =
                     let uu____25217 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25217
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25213 uu____25215
                    in
                 (FStar_Errors.Warning_Defensive, uu____25211)  in
               FStar_Errors.log_issue rng uu____25205
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
          let uu____25257 =
            let uu____25259 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25259  in
          if uu____25257
          then ()
          else
            (let uu____25264 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25264 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25290 =
            let uu____25292 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25292  in
          if uu____25290
          then ()
          else
            (let uu____25297 = bound_vars e  in
             def_check_closed_in rng msg uu____25297 t)
  
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
          let uu___2088_25336 = g  in
          let uu____25337 =
            let uu____25338 =
              let uu____25339 =
                let uu____25346 =
                  let uu____25347 =
                    let uu____25364 =
                      let uu____25375 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25375]  in
                    (f, uu____25364)  in
                  FStar_Syntax_Syntax.Tm_app uu____25347  in
                FStar_Syntax_Syntax.mk uu____25346  in
              uu____25339 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25412  -> FStar_TypeChecker_Common.NonTrivial _25412)
              uu____25338
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____25337;
            FStar_TypeChecker_Common.deferred =
              (uu___2088_25336.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2088_25336.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2088_25336.FStar_TypeChecker_Common.implicits)
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
          let uu___2095_25430 = g  in
          let uu____25431 =
            let uu____25432 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25432  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25431;
            FStar_TypeChecker_Common.deferred =
              (uu___2095_25430.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2095_25430.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2095_25430.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2100_25449 = g  in
          let uu____25450 =
            let uu____25451 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25451  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25450;
            FStar_TypeChecker_Common.deferred =
              (uu___2100_25449.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2100_25449.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2100_25449.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2104_25453 = g  in
          let uu____25454 =
            let uu____25455 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25455  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25454;
            FStar_TypeChecker_Common.deferred =
              (uu___2104_25453.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2104_25453.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2104_25453.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25462 ->
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
                       let uu____25539 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25539
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2127_25546 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2127_25546.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2127_25546.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2127_25546.FStar_TypeChecker_Common.implicits)
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
               let uu____25580 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25580
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
            let uu___2142_25607 = g  in
            let uu____25608 =
              let uu____25609 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25609  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25608;
              FStar_TypeChecker_Common.deferred =
                (uu___2142_25607.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2142_25607.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2142_25607.FStar_TypeChecker_Common.implicits)
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
              let uu____25667 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25667 with
              | FStar_Pervasives_Native.Some
                  (uu____25692::(tm,uu____25694)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25758 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25776 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25776;
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
                      let uu___2164_25808 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2164_25808.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2164_25808.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2164_25808.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____25862 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____25919  ->
                      fun b  ->
                        match uu____25919 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____25961 =
                              let uu____25974 = reason b  in
                              new_implicit_var_aux uu____25974 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____25961 with
                             | (t,uu____25991,g_t) ->
                                 let uu____26005 =
                                   let uu____26008 =
                                     let uu____26011 =
                                       let uu____26012 =
                                         let uu____26019 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26019, t)  in
                                       FStar_Syntax_Syntax.NT uu____26012  in
                                     [uu____26011]  in
                                   FStar_List.append substs1 uu____26008  in
                                 let uu____26030 = conj_guard g g_t  in
                                 (uu____26005,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26030))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____25862
              (fun uu____26059  ->
                 match uu____26059 with
                 | (uu____26076,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26092  -> ());
    push = (fun uu____26094  -> ());
    pop = (fun uu____26097  -> ());
    snapshot =
      (fun uu____26100  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26119  -> fun uu____26120  -> ());
    encode_sig = (fun uu____26135  -> fun uu____26136  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26142 =
             let uu____26149 = FStar_Options.peek ()  in (e, g, uu____26149)
              in
           [uu____26142]);
    solve = (fun uu____26165  -> fun uu____26166  -> fun uu____26167  -> ());
    finish = (fun uu____26174  -> ());
    refresh = (fun uu____26176  -> ())
  } 