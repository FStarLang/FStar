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
  fun projectee  -> match projectee with | Beta  -> true | uu____104 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____115 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____126 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____138 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____156 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____167 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____178 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____189 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____200 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____211 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____223 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____244 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____271 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____298 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____322 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____333 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____344 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____355 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____366 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____377 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____388 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____399 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____410 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____421 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____432 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____443 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____454 -> false
  
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
      | uu____514 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____540 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____551 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____562 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____574 -> false
  
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
           (fun uu___0_13683  ->
              match uu___0_13683 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13686 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13686  in
                  let uu____13687 =
                    let uu____13688 = FStar_Syntax_Subst.compress y  in
                    uu____13688.FStar_Syntax_Syntax.n  in
                  (match uu____13687 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13692 =
                         let uu___318_13693 = y1  in
                         let uu____13694 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___318_13693.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___318_13693.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13694
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13692
                   | uu____13697 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___324_13711 = env  in
      let uu____13712 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___324_13711.solver);
        range = (uu___324_13711.range);
        curmodule = (uu___324_13711.curmodule);
        gamma = uu____13712;
        gamma_sig = (uu___324_13711.gamma_sig);
        gamma_cache = (uu___324_13711.gamma_cache);
        modules = (uu___324_13711.modules);
        expected_typ = (uu___324_13711.expected_typ);
        sigtab = (uu___324_13711.sigtab);
        attrtab = (uu___324_13711.attrtab);
        instantiate_imp = (uu___324_13711.instantiate_imp);
        effects = (uu___324_13711.effects);
        generalize = (uu___324_13711.generalize);
        letrecs = (uu___324_13711.letrecs);
        top_level = (uu___324_13711.top_level);
        check_uvars = (uu___324_13711.check_uvars);
        use_eq = (uu___324_13711.use_eq);
        is_iface = (uu___324_13711.is_iface);
        admit = (uu___324_13711.admit);
        lax = (uu___324_13711.lax);
        lax_universes = (uu___324_13711.lax_universes);
        phase1 = (uu___324_13711.phase1);
        failhard = (uu___324_13711.failhard);
        nosynth = (uu___324_13711.nosynth);
        uvar_subtyping = (uu___324_13711.uvar_subtyping);
        tc_term = (uu___324_13711.tc_term);
        type_of = (uu___324_13711.type_of);
        universe_of = (uu___324_13711.universe_of);
        check_type_of = (uu___324_13711.check_type_of);
        use_bv_sorts = (uu___324_13711.use_bv_sorts);
        qtbl_name_and_index = (uu___324_13711.qtbl_name_and_index);
        normalized_eff_names = (uu___324_13711.normalized_eff_names);
        fv_delta_depths = (uu___324_13711.fv_delta_depths);
        proof_ns = (uu___324_13711.proof_ns);
        synth_hook = (uu___324_13711.synth_hook);
        try_solve_implicits_hook = (uu___324_13711.try_solve_implicits_hook);
        splice = (uu___324_13711.splice);
        mpreprocess = (uu___324_13711.mpreprocess);
        postprocess = (uu___324_13711.postprocess);
        is_native_tactic = (uu___324_13711.is_native_tactic);
        identifier_info = (uu___324_13711.identifier_info);
        tc_hooks = (uu___324_13711.tc_hooks);
        dsenv = (uu___324_13711.dsenv);
        nbe = (uu___324_13711.nbe);
        strict_args_tab = (uu___324_13711.strict_args_tab);
        erasable_types_tab = (uu___324_13711.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13720  -> fun uu____13721  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___331_13743 = env  in
      {
        solver = (uu___331_13743.solver);
        range = (uu___331_13743.range);
        curmodule = (uu___331_13743.curmodule);
        gamma = (uu___331_13743.gamma);
        gamma_sig = (uu___331_13743.gamma_sig);
        gamma_cache = (uu___331_13743.gamma_cache);
        modules = (uu___331_13743.modules);
        expected_typ = (uu___331_13743.expected_typ);
        sigtab = (uu___331_13743.sigtab);
        attrtab = (uu___331_13743.attrtab);
        instantiate_imp = (uu___331_13743.instantiate_imp);
        effects = (uu___331_13743.effects);
        generalize = (uu___331_13743.generalize);
        letrecs = (uu___331_13743.letrecs);
        top_level = (uu___331_13743.top_level);
        check_uvars = (uu___331_13743.check_uvars);
        use_eq = (uu___331_13743.use_eq);
        is_iface = (uu___331_13743.is_iface);
        admit = (uu___331_13743.admit);
        lax = (uu___331_13743.lax);
        lax_universes = (uu___331_13743.lax_universes);
        phase1 = (uu___331_13743.phase1);
        failhard = (uu___331_13743.failhard);
        nosynth = (uu___331_13743.nosynth);
        uvar_subtyping = (uu___331_13743.uvar_subtyping);
        tc_term = (uu___331_13743.tc_term);
        type_of = (uu___331_13743.type_of);
        universe_of = (uu___331_13743.universe_of);
        check_type_of = (uu___331_13743.check_type_of);
        use_bv_sorts = (uu___331_13743.use_bv_sorts);
        qtbl_name_and_index = (uu___331_13743.qtbl_name_and_index);
        normalized_eff_names = (uu___331_13743.normalized_eff_names);
        fv_delta_depths = (uu___331_13743.fv_delta_depths);
        proof_ns = (uu___331_13743.proof_ns);
        synth_hook = (uu___331_13743.synth_hook);
        try_solve_implicits_hook = (uu___331_13743.try_solve_implicits_hook);
        splice = (uu___331_13743.splice);
        mpreprocess = (uu___331_13743.mpreprocess);
        postprocess = (uu___331_13743.postprocess);
        is_native_tactic = (uu___331_13743.is_native_tactic);
        identifier_info = (uu___331_13743.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___331_13743.dsenv);
        nbe = (uu___331_13743.nbe);
        strict_args_tab = (uu___331_13743.strict_args_tab);
        erasable_types_tab = (uu___331_13743.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___335_13755 = e  in
      let uu____13756 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___335_13755.solver);
        range = (uu___335_13755.range);
        curmodule = (uu___335_13755.curmodule);
        gamma = (uu___335_13755.gamma);
        gamma_sig = (uu___335_13755.gamma_sig);
        gamma_cache = (uu___335_13755.gamma_cache);
        modules = (uu___335_13755.modules);
        expected_typ = (uu___335_13755.expected_typ);
        sigtab = (uu___335_13755.sigtab);
        attrtab = (uu___335_13755.attrtab);
        instantiate_imp = (uu___335_13755.instantiate_imp);
        effects = (uu___335_13755.effects);
        generalize = (uu___335_13755.generalize);
        letrecs = (uu___335_13755.letrecs);
        top_level = (uu___335_13755.top_level);
        check_uvars = (uu___335_13755.check_uvars);
        use_eq = (uu___335_13755.use_eq);
        is_iface = (uu___335_13755.is_iface);
        admit = (uu___335_13755.admit);
        lax = (uu___335_13755.lax);
        lax_universes = (uu___335_13755.lax_universes);
        phase1 = (uu___335_13755.phase1);
        failhard = (uu___335_13755.failhard);
        nosynth = (uu___335_13755.nosynth);
        uvar_subtyping = (uu___335_13755.uvar_subtyping);
        tc_term = (uu___335_13755.tc_term);
        type_of = (uu___335_13755.type_of);
        universe_of = (uu___335_13755.universe_of);
        check_type_of = (uu___335_13755.check_type_of);
        use_bv_sorts = (uu___335_13755.use_bv_sorts);
        qtbl_name_and_index = (uu___335_13755.qtbl_name_and_index);
        normalized_eff_names = (uu___335_13755.normalized_eff_names);
        fv_delta_depths = (uu___335_13755.fv_delta_depths);
        proof_ns = (uu___335_13755.proof_ns);
        synth_hook = (uu___335_13755.synth_hook);
        try_solve_implicits_hook = (uu___335_13755.try_solve_implicits_hook);
        splice = (uu___335_13755.splice);
        mpreprocess = (uu___335_13755.mpreprocess);
        postprocess = (uu___335_13755.postprocess);
        is_native_tactic = (uu___335_13755.is_native_tactic);
        identifier_info = (uu___335_13755.identifier_info);
        tc_hooks = (uu___335_13755.tc_hooks);
        dsenv = uu____13756;
        nbe = (uu___335_13755.nbe);
        strict_args_tab = (uu___335_13755.strict_args_tab);
        erasable_types_tab = (uu___335_13755.erasable_types_tab)
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
      | (NoDelta ,uu____13785) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13788,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13790,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13793 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13807 . unit -> 'Auu____13807 FStar_Util.smap =
  fun uu____13814  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13820 . unit -> 'Auu____13820 FStar_Util.smap =
  fun uu____13827  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13965 = new_gamma_cache ()  in
                  let uu____13968 = new_sigtab ()  in
                  let uu____13971 = new_sigtab ()  in
                  let uu____13978 =
                    let uu____13993 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13993, FStar_Pervasives_Native.None)  in
                  let uu____14014 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14018 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____14022 = FStar_Options.using_facts_from ()  in
                  let uu____14023 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____14026 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____14027 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____14041 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13965;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13968;
                    attrtab = uu____13971;
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
                    qtbl_name_and_index = uu____13978;
                    normalized_eff_names = uu____14014;
                    fv_delta_depths = uu____14018;
                    proof_ns = uu____14022;
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
                    is_native_tactic = (fun uu____14121  -> false);
                    identifier_info = uu____14023;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____14026;
                    nbe = nbe1;
                    strict_args_tab = uu____14027;
                    erasable_types_tab = uu____14041
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
  fun uu____14200  ->
    let uu____14201 = FStar_ST.op_Bang query_indices  in
    match uu____14201 with
    | [] -> failwith "Empty query indices!"
    | uu____14256 ->
        let uu____14266 =
          let uu____14276 =
            let uu____14284 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14284  in
          let uu____14338 = FStar_ST.op_Bang query_indices  in uu____14276 ::
            uu____14338
           in
        FStar_ST.op_Colon_Equals query_indices uu____14266
  
let (pop_query_indices : unit -> unit) =
  fun uu____14434  ->
    let uu____14435 = FStar_ST.op_Bang query_indices  in
    match uu____14435 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14562  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14599  ->
    match uu____14599 with
    | (l,n1) ->
        let uu____14609 = FStar_ST.op_Bang query_indices  in
        (match uu____14609 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14731 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14754  ->
    let uu____14755 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14755
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14823 =
       let uu____14826 = FStar_ST.op_Bang stack  in env :: uu____14826  in
     FStar_ST.op_Colon_Equals stack uu____14823);
    (let uu___409_14875 = env  in
     let uu____14876 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14879 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14882 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14889 =
       let uu____14904 =
         let uu____14908 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14908  in
       let uu____14940 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14904, uu____14940)  in
     let uu____14989 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14992 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14995 =
       let uu____14998 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14998  in
     let uu____15018 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____15031 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___409_14875.solver);
       range = (uu___409_14875.range);
       curmodule = (uu___409_14875.curmodule);
       gamma = (uu___409_14875.gamma);
       gamma_sig = (uu___409_14875.gamma_sig);
       gamma_cache = uu____14876;
       modules = (uu___409_14875.modules);
       expected_typ = (uu___409_14875.expected_typ);
       sigtab = uu____14879;
       attrtab = uu____14882;
       instantiate_imp = (uu___409_14875.instantiate_imp);
       effects = (uu___409_14875.effects);
       generalize = (uu___409_14875.generalize);
       letrecs = (uu___409_14875.letrecs);
       top_level = (uu___409_14875.top_level);
       check_uvars = (uu___409_14875.check_uvars);
       use_eq = (uu___409_14875.use_eq);
       is_iface = (uu___409_14875.is_iface);
       admit = (uu___409_14875.admit);
       lax = (uu___409_14875.lax);
       lax_universes = (uu___409_14875.lax_universes);
       phase1 = (uu___409_14875.phase1);
       failhard = (uu___409_14875.failhard);
       nosynth = (uu___409_14875.nosynth);
       uvar_subtyping = (uu___409_14875.uvar_subtyping);
       tc_term = (uu___409_14875.tc_term);
       type_of = (uu___409_14875.type_of);
       universe_of = (uu___409_14875.universe_of);
       check_type_of = (uu___409_14875.check_type_of);
       use_bv_sorts = (uu___409_14875.use_bv_sorts);
       qtbl_name_and_index = uu____14889;
       normalized_eff_names = uu____14989;
       fv_delta_depths = uu____14992;
       proof_ns = (uu___409_14875.proof_ns);
       synth_hook = (uu___409_14875.synth_hook);
       try_solve_implicits_hook = (uu___409_14875.try_solve_implicits_hook);
       splice = (uu___409_14875.splice);
       mpreprocess = (uu___409_14875.mpreprocess);
       postprocess = (uu___409_14875.postprocess);
       is_native_tactic = (uu___409_14875.is_native_tactic);
       identifier_info = uu____14995;
       tc_hooks = (uu___409_14875.tc_hooks);
       dsenv = (uu___409_14875.dsenv);
       nbe = (uu___409_14875.nbe);
       strict_args_tab = uu____15018;
       erasable_types_tab = uu____15031
     })
  
let (pop_stack : unit -> env) =
  fun uu____15041  ->
    let uu____15042 = FStar_ST.op_Bang stack  in
    match uu____15042 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15096 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15186  ->
           let uu____15187 = snapshot_stack env  in
           match uu____15187 with
           | (stack_depth,env1) ->
               let uu____15221 = snapshot_query_indices ()  in
               (match uu____15221 with
                | (query_indices_depth,()) ->
                    let uu____15254 = (env1.solver).snapshot msg  in
                    (match uu____15254 with
                     | (solver_depth,()) ->
                         let uu____15311 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____15311 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___434_15378 = env1  in
                                 {
                                   solver = (uu___434_15378.solver);
                                   range = (uu___434_15378.range);
                                   curmodule = (uu___434_15378.curmodule);
                                   gamma = (uu___434_15378.gamma);
                                   gamma_sig = (uu___434_15378.gamma_sig);
                                   gamma_cache = (uu___434_15378.gamma_cache);
                                   modules = (uu___434_15378.modules);
                                   expected_typ =
                                     (uu___434_15378.expected_typ);
                                   sigtab = (uu___434_15378.sigtab);
                                   attrtab = (uu___434_15378.attrtab);
                                   instantiate_imp =
                                     (uu___434_15378.instantiate_imp);
                                   effects = (uu___434_15378.effects);
                                   generalize = (uu___434_15378.generalize);
                                   letrecs = (uu___434_15378.letrecs);
                                   top_level = (uu___434_15378.top_level);
                                   check_uvars = (uu___434_15378.check_uvars);
                                   use_eq = (uu___434_15378.use_eq);
                                   is_iface = (uu___434_15378.is_iface);
                                   admit = (uu___434_15378.admit);
                                   lax = (uu___434_15378.lax);
                                   lax_universes =
                                     (uu___434_15378.lax_universes);
                                   phase1 = (uu___434_15378.phase1);
                                   failhard = (uu___434_15378.failhard);
                                   nosynth = (uu___434_15378.nosynth);
                                   uvar_subtyping =
                                     (uu___434_15378.uvar_subtyping);
                                   tc_term = (uu___434_15378.tc_term);
                                   type_of = (uu___434_15378.type_of);
                                   universe_of = (uu___434_15378.universe_of);
                                   check_type_of =
                                     (uu___434_15378.check_type_of);
                                   use_bv_sorts =
                                     (uu___434_15378.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___434_15378.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___434_15378.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___434_15378.fv_delta_depths);
                                   proof_ns = (uu___434_15378.proof_ns);
                                   synth_hook = (uu___434_15378.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___434_15378.try_solve_implicits_hook);
                                   splice = (uu___434_15378.splice);
                                   mpreprocess = (uu___434_15378.mpreprocess);
                                   postprocess = (uu___434_15378.postprocess);
                                   is_native_tactic =
                                     (uu___434_15378.is_native_tactic);
                                   identifier_info =
                                     (uu___434_15378.identifier_info);
                                   tc_hooks = (uu___434_15378.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___434_15378.nbe);
                                   strict_args_tab =
                                     (uu___434_15378.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___434_15378.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15412  ->
             let uu____15413 =
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
             match uu____15413 with
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
                             ((let uu____15593 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15593
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15609 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15609
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15641,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15683 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15713  ->
                  match uu____15713 with
                  | (m,uu____15721) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15683 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___479_15736 = env  in
               {
                 solver = (uu___479_15736.solver);
                 range = (uu___479_15736.range);
                 curmodule = (uu___479_15736.curmodule);
                 gamma = (uu___479_15736.gamma);
                 gamma_sig = (uu___479_15736.gamma_sig);
                 gamma_cache = (uu___479_15736.gamma_cache);
                 modules = (uu___479_15736.modules);
                 expected_typ = (uu___479_15736.expected_typ);
                 sigtab = (uu___479_15736.sigtab);
                 attrtab = (uu___479_15736.attrtab);
                 instantiate_imp = (uu___479_15736.instantiate_imp);
                 effects = (uu___479_15736.effects);
                 generalize = (uu___479_15736.generalize);
                 letrecs = (uu___479_15736.letrecs);
                 top_level = (uu___479_15736.top_level);
                 check_uvars = (uu___479_15736.check_uvars);
                 use_eq = (uu___479_15736.use_eq);
                 is_iface = (uu___479_15736.is_iface);
                 admit = (uu___479_15736.admit);
                 lax = (uu___479_15736.lax);
                 lax_universes = (uu___479_15736.lax_universes);
                 phase1 = (uu___479_15736.phase1);
                 failhard = (uu___479_15736.failhard);
                 nosynth = (uu___479_15736.nosynth);
                 uvar_subtyping = (uu___479_15736.uvar_subtyping);
                 tc_term = (uu___479_15736.tc_term);
                 type_of = (uu___479_15736.type_of);
                 universe_of = (uu___479_15736.universe_of);
                 check_type_of = (uu___479_15736.check_type_of);
                 use_bv_sorts = (uu___479_15736.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___479_15736.normalized_eff_names);
                 fv_delta_depths = (uu___479_15736.fv_delta_depths);
                 proof_ns = (uu___479_15736.proof_ns);
                 synth_hook = (uu___479_15736.synth_hook);
                 try_solve_implicits_hook =
                   (uu___479_15736.try_solve_implicits_hook);
                 splice = (uu___479_15736.splice);
                 mpreprocess = (uu___479_15736.mpreprocess);
                 postprocess = (uu___479_15736.postprocess);
                 is_native_tactic = (uu___479_15736.is_native_tactic);
                 identifier_info = (uu___479_15736.identifier_info);
                 tc_hooks = (uu___479_15736.tc_hooks);
                 dsenv = (uu___479_15736.dsenv);
                 nbe = (uu___479_15736.nbe);
                 strict_args_tab = (uu___479_15736.strict_args_tab);
                 erasable_types_tab = (uu___479_15736.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15753,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___488_15769 = env  in
               {
                 solver = (uu___488_15769.solver);
                 range = (uu___488_15769.range);
                 curmodule = (uu___488_15769.curmodule);
                 gamma = (uu___488_15769.gamma);
                 gamma_sig = (uu___488_15769.gamma_sig);
                 gamma_cache = (uu___488_15769.gamma_cache);
                 modules = (uu___488_15769.modules);
                 expected_typ = (uu___488_15769.expected_typ);
                 sigtab = (uu___488_15769.sigtab);
                 attrtab = (uu___488_15769.attrtab);
                 instantiate_imp = (uu___488_15769.instantiate_imp);
                 effects = (uu___488_15769.effects);
                 generalize = (uu___488_15769.generalize);
                 letrecs = (uu___488_15769.letrecs);
                 top_level = (uu___488_15769.top_level);
                 check_uvars = (uu___488_15769.check_uvars);
                 use_eq = (uu___488_15769.use_eq);
                 is_iface = (uu___488_15769.is_iface);
                 admit = (uu___488_15769.admit);
                 lax = (uu___488_15769.lax);
                 lax_universes = (uu___488_15769.lax_universes);
                 phase1 = (uu___488_15769.phase1);
                 failhard = (uu___488_15769.failhard);
                 nosynth = (uu___488_15769.nosynth);
                 uvar_subtyping = (uu___488_15769.uvar_subtyping);
                 tc_term = (uu___488_15769.tc_term);
                 type_of = (uu___488_15769.type_of);
                 universe_of = (uu___488_15769.universe_of);
                 check_type_of = (uu___488_15769.check_type_of);
                 use_bv_sorts = (uu___488_15769.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_15769.normalized_eff_names);
                 fv_delta_depths = (uu___488_15769.fv_delta_depths);
                 proof_ns = (uu___488_15769.proof_ns);
                 synth_hook = (uu___488_15769.synth_hook);
                 try_solve_implicits_hook =
                   (uu___488_15769.try_solve_implicits_hook);
                 splice = (uu___488_15769.splice);
                 mpreprocess = (uu___488_15769.mpreprocess);
                 postprocess = (uu___488_15769.postprocess);
                 is_native_tactic = (uu___488_15769.is_native_tactic);
                 identifier_info = (uu___488_15769.identifier_info);
                 tc_hooks = (uu___488_15769.tc_hooks);
                 dsenv = (uu___488_15769.dsenv);
                 nbe = (uu___488_15769.nbe);
                 strict_args_tab = (uu___488_15769.strict_args_tab);
                 erasable_types_tab = (uu___488_15769.erasable_types_tab)
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
        (let uu___495_15812 = e  in
         {
           solver = (uu___495_15812.solver);
           range = r;
           curmodule = (uu___495_15812.curmodule);
           gamma = (uu___495_15812.gamma);
           gamma_sig = (uu___495_15812.gamma_sig);
           gamma_cache = (uu___495_15812.gamma_cache);
           modules = (uu___495_15812.modules);
           expected_typ = (uu___495_15812.expected_typ);
           sigtab = (uu___495_15812.sigtab);
           attrtab = (uu___495_15812.attrtab);
           instantiate_imp = (uu___495_15812.instantiate_imp);
           effects = (uu___495_15812.effects);
           generalize = (uu___495_15812.generalize);
           letrecs = (uu___495_15812.letrecs);
           top_level = (uu___495_15812.top_level);
           check_uvars = (uu___495_15812.check_uvars);
           use_eq = (uu___495_15812.use_eq);
           is_iface = (uu___495_15812.is_iface);
           admit = (uu___495_15812.admit);
           lax = (uu___495_15812.lax);
           lax_universes = (uu___495_15812.lax_universes);
           phase1 = (uu___495_15812.phase1);
           failhard = (uu___495_15812.failhard);
           nosynth = (uu___495_15812.nosynth);
           uvar_subtyping = (uu___495_15812.uvar_subtyping);
           tc_term = (uu___495_15812.tc_term);
           type_of = (uu___495_15812.type_of);
           universe_of = (uu___495_15812.universe_of);
           check_type_of = (uu___495_15812.check_type_of);
           use_bv_sorts = (uu___495_15812.use_bv_sorts);
           qtbl_name_and_index = (uu___495_15812.qtbl_name_and_index);
           normalized_eff_names = (uu___495_15812.normalized_eff_names);
           fv_delta_depths = (uu___495_15812.fv_delta_depths);
           proof_ns = (uu___495_15812.proof_ns);
           synth_hook = (uu___495_15812.synth_hook);
           try_solve_implicits_hook =
             (uu___495_15812.try_solve_implicits_hook);
           splice = (uu___495_15812.splice);
           mpreprocess = (uu___495_15812.mpreprocess);
           postprocess = (uu___495_15812.postprocess);
           is_native_tactic = (uu___495_15812.is_native_tactic);
           identifier_info = (uu___495_15812.identifier_info);
           tc_hooks = (uu___495_15812.tc_hooks);
           dsenv = (uu___495_15812.dsenv);
           nbe = (uu___495_15812.nbe);
           strict_args_tab = (uu___495_15812.strict_args_tab);
           erasable_types_tab = (uu___495_15812.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15832 =
        let uu____15833 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15833 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15832
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15888 =
          let uu____15889 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15889 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15888
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15944 =
          let uu____15945 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15945 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15944
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____16000 =
        let uu____16001 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____16001 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____16000
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___512_16065 = env  in
      {
        solver = (uu___512_16065.solver);
        range = (uu___512_16065.range);
        curmodule = lid;
        gamma = (uu___512_16065.gamma);
        gamma_sig = (uu___512_16065.gamma_sig);
        gamma_cache = (uu___512_16065.gamma_cache);
        modules = (uu___512_16065.modules);
        expected_typ = (uu___512_16065.expected_typ);
        sigtab = (uu___512_16065.sigtab);
        attrtab = (uu___512_16065.attrtab);
        instantiate_imp = (uu___512_16065.instantiate_imp);
        effects = (uu___512_16065.effects);
        generalize = (uu___512_16065.generalize);
        letrecs = (uu___512_16065.letrecs);
        top_level = (uu___512_16065.top_level);
        check_uvars = (uu___512_16065.check_uvars);
        use_eq = (uu___512_16065.use_eq);
        is_iface = (uu___512_16065.is_iface);
        admit = (uu___512_16065.admit);
        lax = (uu___512_16065.lax);
        lax_universes = (uu___512_16065.lax_universes);
        phase1 = (uu___512_16065.phase1);
        failhard = (uu___512_16065.failhard);
        nosynth = (uu___512_16065.nosynth);
        uvar_subtyping = (uu___512_16065.uvar_subtyping);
        tc_term = (uu___512_16065.tc_term);
        type_of = (uu___512_16065.type_of);
        universe_of = (uu___512_16065.universe_of);
        check_type_of = (uu___512_16065.check_type_of);
        use_bv_sorts = (uu___512_16065.use_bv_sorts);
        qtbl_name_and_index = (uu___512_16065.qtbl_name_and_index);
        normalized_eff_names = (uu___512_16065.normalized_eff_names);
        fv_delta_depths = (uu___512_16065.fv_delta_depths);
        proof_ns = (uu___512_16065.proof_ns);
        synth_hook = (uu___512_16065.synth_hook);
        try_solve_implicits_hook = (uu___512_16065.try_solve_implicits_hook);
        splice = (uu___512_16065.splice);
        mpreprocess = (uu___512_16065.mpreprocess);
        postprocess = (uu___512_16065.postprocess);
        is_native_tactic = (uu___512_16065.is_native_tactic);
        identifier_info = (uu___512_16065.identifier_info);
        tc_hooks = (uu___512_16065.tc_hooks);
        dsenv = (uu___512_16065.dsenv);
        nbe = (uu___512_16065.nbe);
        strict_args_tab = (uu___512_16065.strict_args_tab);
        erasable_types_tab = (uu___512_16065.erasable_types_tab)
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
      let uu____16096 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16096
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16109 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16109)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16124 =
      let uu____16126 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16126  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16124)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16135  ->
    let uu____16136 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16136
  
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
      | ((formals,t),uu____16236) ->
          let vs = mk_univ_subst formals us  in
          let uu____16260 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16260)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16277  ->
    match uu___1_16277 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16303  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16323 = inst_tscheme t  in
      match uu____16323 with
      | (us,t1) ->
          let uu____16334 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16334)
  
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
          let uu____16359 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16361 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16359 uu____16361
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
        fun uu____16388  ->
          match uu____16388 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16402 =
                    let uu____16404 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16408 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16412 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16414 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16404 uu____16408 uu____16412 uu____16414
                     in
                  failwith uu____16402)
               else ();
               (let uu____16419 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16419))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16437 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16448 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16459 -> false
  
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
             | ([],uu____16507) -> Maybe
             | (uu____16514,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16534 -> No  in
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
          let uu____16628 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16628 with
          | FStar_Pervasives_Native.None  ->
              let uu____16651 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16695  ->
                     match uu___2_16695 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16734 = FStar_Ident.lid_equals lid l  in
                         if uu____16734
                         then
                           let uu____16757 =
                             let uu____16776 =
                               let uu____16791 = inst_tscheme t  in
                               FStar_Util.Inl uu____16791  in
                             let uu____16806 = FStar_Ident.range_of_lid l  in
                             (uu____16776, uu____16806)  in
                           FStar_Pervasives_Native.Some uu____16757
                         else FStar_Pervasives_Native.None
                     | uu____16859 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16651
                (fun uu____16897  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16907  ->
                        match uu___3_16907 with
                        | (uu____16910,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16912);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16913;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16914;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16915;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16916;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16917;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16939 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16939
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
                                  uu____16991 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16998 -> cache t  in
                            let uu____16999 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16999 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____17005 =
                                   let uu____17006 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____17006)
                                    in
                                 maybe_cache uu____17005)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17077 = find_in_sigtab env lid  in
         match uu____17077 with
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
      let uu____17158 = lookup_qname env lid  in
      match uu____17158 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17179,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17293 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17293 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____17338 =
          let uu____17341 = lookup_attr env1 attr  in se1 :: uu____17341  in
        FStar_Util.smap_add (attrtab env1) attr uu____17338  in
      FStar_List.iter
        (fun attr  ->
           let uu____17351 =
             let uu____17352 = FStar_Syntax_Subst.compress attr  in
             uu____17352.FStar_Syntax_Syntax.n  in
           match uu____17351 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17356 =
                 let uu____17358 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____17358.FStar_Ident.str  in
               add_one1 env se uu____17356
           | uu____17359 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17382) ->
          add_sigelts env ses
      | uu____17391 ->
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
        (fun uu___4_17429  ->
           match uu___4_17429 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17447 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17509,lb::[]),uu____17511) ->
            let uu____17520 =
              let uu____17529 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17538 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17529, uu____17538)  in
            FStar_Pervasives_Native.Some uu____17520
        | FStar_Syntax_Syntax.Sig_let ((uu____17551,lbs),uu____17553) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17585 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17598 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17598
                     then
                       let uu____17611 =
                         let uu____17620 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17629 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17620, uu____17629)  in
                       FStar_Pervasives_Native.Some uu____17611
                     else FStar_Pervasives_Native.None)
        | uu____17652 -> FStar_Pervasives_Native.None
  
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
                    let uu____17744 =
                      let uu____17746 =
                        let uu____17748 =
                          let uu____17750 =
                            let uu____17752 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17758 =
                              let uu____17760 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17760  in
                            Prims.op_Hat uu____17752 uu____17758  in
                          Prims.op_Hat ", expected " uu____17750  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17748
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17746
                       in
                    failwith uu____17744
                  else ());
             (let uu____17767 =
                let uu____17776 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17776, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17767))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17796,uu____17797) ->
            let uu____17802 =
              let uu____17811 =
                let uu____17816 =
                  let uu____17817 =
                    let uu____17820 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17820  in
                  (us, uu____17817)  in
                inst_ts us_opt uu____17816  in
              (uu____17811, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17802
        | uu____17839 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17928 =
          match uu____17928 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____18024,uvs,t,uu____18027,uu____18028,uu____18029);
                      FStar_Syntax_Syntax.sigrng = uu____18030;
                      FStar_Syntax_Syntax.sigquals = uu____18031;
                      FStar_Syntax_Syntax.sigmeta = uu____18032;
                      FStar_Syntax_Syntax.sigattrs = uu____18033;
                      FStar_Syntax_Syntax.sigopts = uu____18034;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18059 =
                     let uu____18068 = inst_tscheme1 (uvs, t)  in
                     (uu____18068, rng)  in
                   FStar_Pervasives_Native.Some uu____18059
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18092;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18094;
                      FStar_Syntax_Syntax.sigattrs = uu____18095;
                      FStar_Syntax_Syntax.sigopts = uu____18096;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18115 =
                     let uu____18117 = in_cur_mod env l  in uu____18117 = Yes
                      in
                   if uu____18115
                   then
                     let uu____18129 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18129
                      then
                        let uu____18145 =
                          let uu____18154 = inst_tscheme1 (uvs, t)  in
                          (uu____18154, rng)  in
                        FStar_Pervasives_Native.Some uu____18145
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18187 =
                        let uu____18196 = inst_tscheme1 (uvs, t)  in
                        (uu____18196, rng)  in
                      FStar_Pervasives_Native.Some uu____18187)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18221,uu____18222);
                      FStar_Syntax_Syntax.sigrng = uu____18223;
                      FStar_Syntax_Syntax.sigquals = uu____18224;
                      FStar_Syntax_Syntax.sigmeta = uu____18225;
                      FStar_Syntax_Syntax.sigattrs = uu____18226;
                      FStar_Syntax_Syntax.sigopts = uu____18227;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18270 =
                          let uu____18279 = inst_tscheme1 (uvs, k)  in
                          (uu____18279, rng)  in
                        FStar_Pervasives_Native.Some uu____18270
                    | uu____18300 ->
                        let uu____18301 =
                          let uu____18310 =
                            let uu____18315 =
                              let uu____18316 =
                                let uu____18319 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18319
                                 in
                              (uvs, uu____18316)  in
                            inst_tscheme1 uu____18315  in
                          (uu____18310, rng)  in
                        FStar_Pervasives_Native.Some uu____18301)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18342,uu____18343);
                      FStar_Syntax_Syntax.sigrng = uu____18344;
                      FStar_Syntax_Syntax.sigquals = uu____18345;
                      FStar_Syntax_Syntax.sigmeta = uu____18346;
                      FStar_Syntax_Syntax.sigattrs = uu____18347;
                      FStar_Syntax_Syntax.sigopts = uu____18348;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18392 =
                          let uu____18401 = inst_tscheme_with (uvs, k) us  in
                          (uu____18401, rng)  in
                        FStar_Pervasives_Native.Some uu____18392
                    | uu____18422 ->
                        let uu____18423 =
                          let uu____18432 =
                            let uu____18437 =
                              let uu____18438 =
                                let uu____18441 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18441
                                 in
                              (uvs, uu____18438)  in
                            inst_tscheme_with uu____18437 us  in
                          (uu____18432, rng)  in
                        FStar_Pervasives_Native.Some uu____18423)
               | FStar_Util.Inr se ->
                   let uu____18477 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18498;
                          FStar_Syntax_Syntax.sigrng = uu____18499;
                          FStar_Syntax_Syntax.sigquals = uu____18500;
                          FStar_Syntax_Syntax.sigmeta = uu____18501;
                          FStar_Syntax_Syntax.sigattrs = uu____18502;
                          FStar_Syntax_Syntax.sigopts = uu____18503;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18520 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18477
                     (FStar_Util.map_option
                        (fun uu____18568  ->
                           match uu____18568 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18599 =
          let uu____18610 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18610 mapper  in
        match uu____18599 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18684 =
              let uu____18695 =
                let uu____18702 =
                  let uu___849_18705 = t  in
                  let uu____18706 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___849_18705.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18706;
                    FStar_Syntax_Syntax.vars =
                      (uu___849_18705.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18702)  in
              (uu____18695, r)  in
            FStar_Pervasives_Native.Some uu____18684
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18755 = lookup_qname env l  in
      match uu____18755 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18776 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18830 = try_lookup_bv env bv  in
      match uu____18830 with
      | FStar_Pervasives_Native.None  ->
          let uu____18845 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18845 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18861 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18862 =
            let uu____18863 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18863  in
          (uu____18861, uu____18862)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18885 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18885 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18951 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18951  in
          let uu____18952 =
            let uu____18961 =
              let uu____18966 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18966)  in
            (uu____18961, r1)  in
          FStar_Pervasives_Native.Some uu____18952
  
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
        let uu____19001 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____19001 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____19034,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19059 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19059  in
            let uu____19060 =
              let uu____19065 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19065, r1)  in
            FStar_Pervasives_Native.Some uu____19060
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19089 = try_lookup_lid env l  in
      match uu____19089 with
      | FStar_Pervasives_Native.None  ->
          let uu____19116 = name_not_found l  in
          let uu____19122 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19116 uu____19122
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19165  ->
              match uu___5_19165 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19169 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19190 = lookup_qname env lid  in
      match uu____19190 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19199,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19202;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19204;
              FStar_Syntax_Syntax.sigattrs = uu____19205;
              FStar_Syntax_Syntax.sigopts = uu____19206;_},FStar_Pervasives_Native.None
            ),uu____19207)
          ->
          let uu____19258 =
            let uu____19265 =
              let uu____19266 =
                let uu____19269 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19269 t  in
              (uvs, uu____19266)  in
            (uu____19265, q)  in
          FStar_Pervasives_Native.Some uu____19258
      | uu____19282 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19304 = lookup_qname env lid  in
      match uu____19304 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19309,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19312;
              FStar_Syntax_Syntax.sigquals = uu____19313;
              FStar_Syntax_Syntax.sigmeta = uu____19314;
              FStar_Syntax_Syntax.sigattrs = uu____19315;
              FStar_Syntax_Syntax.sigopts = uu____19316;_},FStar_Pervasives_Native.None
            ),uu____19317)
          ->
          let uu____19368 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19368 (uvs, t)
      | uu____19373 ->
          let uu____19374 = name_not_found lid  in
          let uu____19380 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19374 uu____19380
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19400 = lookup_qname env lid  in
      match uu____19400 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19405,uvs,t,uu____19408,uu____19409,uu____19410);
              FStar_Syntax_Syntax.sigrng = uu____19411;
              FStar_Syntax_Syntax.sigquals = uu____19412;
              FStar_Syntax_Syntax.sigmeta = uu____19413;
              FStar_Syntax_Syntax.sigattrs = uu____19414;
              FStar_Syntax_Syntax.sigopts = uu____19415;_},FStar_Pervasives_Native.None
            ),uu____19416)
          ->
          let uu____19473 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19473 (uvs, t)
      | uu____19478 ->
          let uu____19479 = name_not_found lid  in
          let uu____19485 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19479 uu____19485
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19508 = lookup_qname env lid  in
      match uu____19508 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19516,uu____19517,uu____19518,uu____19519,uu____19520,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19522;
              FStar_Syntax_Syntax.sigquals = uu____19523;
              FStar_Syntax_Syntax.sigmeta = uu____19524;
              FStar_Syntax_Syntax.sigattrs = uu____19525;
              FStar_Syntax_Syntax.sigopts = uu____19526;_},uu____19527),uu____19528)
          -> (true, dcs)
      | uu____19593 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19609 = lookup_qname env lid  in
      match uu____19609 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19610,uu____19611,uu____19612,l,uu____19614,uu____19615);
              FStar_Syntax_Syntax.sigrng = uu____19616;
              FStar_Syntax_Syntax.sigquals = uu____19617;
              FStar_Syntax_Syntax.sigmeta = uu____19618;
              FStar_Syntax_Syntax.sigattrs = uu____19619;
              FStar_Syntax_Syntax.sigopts = uu____19620;_},uu____19621),uu____19622)
          -> l
      | uu____19681 ->
          let uu____19682 =
            let uu____19684 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19684  in
          failwith uu____19682
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19754)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19811) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19835 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19835
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19870 -> FStar_Pervasives_Native.None)
          | uu____19879 -> FStar_Pervasives_Native.None
  
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
        let uu____19941 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19941
  
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
        let uu____19974 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19974
  
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
             (FStar_Util.Inl uu____20026,uu____20027) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20076),uu____20077) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20126 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20144 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20154 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20171 ->
                  let uu____20178 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20178
              | FStar_Syntax_Syntax.Sig_let ((uu____20179,lbs),uu____20181)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20197 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20197
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____20204 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____20212 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20213 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20220 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20221 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20222 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20223 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20236 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20254 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20254
           (fun d_opt  ->
              let uu____20267 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20267
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20277 =
                   let uu____20280 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20280  in
                 match uu____20277 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20281 =
                       let uu____20283 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20283
                        in
                     failwith uu____20281
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20288 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20288
                       then
                         let uu____20291 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20293 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20295 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20291 uu____20293 uu____20295
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
        (FStar_Util.Inr (se,uu____20320),uu____20321) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20370 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20392),uu____20393) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20442 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20464 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20464
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20497 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20497 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20519 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20528 =
                        let uu____20529 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20529.FStar_Syntax_Syntax.n  in
                      match uu____20528 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20534 -> false))
               in
            (true, uu____20519)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20557 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20557
  
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
          let uu____20629 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20629.FStar_Ident.str  in
        let uu____20630 = FStar_Util.smap_try_find tab s  in
        match uu____20630 with
        | FStar_Pervasives_Native.None  ->
            let uu____20633 = f ()  in
            (match uu____20633 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20671 =
        let uu____20672 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20672 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20706 =
        let uu____20707 = FStar_Syntax_Util.unrefine t  in
        uu____20707.FStar_Syntax_Syntax.n  in
      match uu____20706 with
      | FStar_Syntax_Syntax.Tm_type uu____20711 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20715) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20741) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20746,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20768 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20801 =
        let attrs =
          let uu____20807 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20807  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20847 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20847)
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
      let uu____20892 = lookup_qname env ftv  in
      match uu____20892 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20896) ->
          let uu____20941 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20941 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20962,t),r) ->
               let uu____20977 =
                 let uu____20978 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20978 t  in
               FStar_Pervasives_Native.Some uu____20977)
      | uu____20979 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20991 = try_lookup_effect_lid env ftv  in
      match uu____20991 with
      | FStar_Pervasives_Native.None  ->
          let uu____20994 = name_not_found ftv  in
          let uu____21000 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20994 uu____21000
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
        let uu____21024 = lookup_qname env lid0  in
        match uu____21024 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____21035);
                FStar_Syntax_Syntax.sigrng = uu____21036;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21038;
                FStar_Syntax_Syntax.sigattrs = uu____21039;
                FStar_Syntax_Syntax.sigopts = uu____21040;_},FStar_Pervasives_Native.None
              ),uu____21041)
            ->
            let lid1 =
              let uu____21097 =
                let uu____21098 = FStar_Ident.range_of_lid lid  in
                let uu____21099 =
                  let uu____21100 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21100  in
                FStar_Range.set_use_range uu____21098 uu____21099  in
              FStar_Ident.set_lid_range lid uu____21097  in
            let uu____21101 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21107  ->
                      match uu___6_21107 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21110 -> false))
               in
            if uu____21101
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21129 =
                      let uu____21131 =
                        let uu____21133 = get_range env  in
                        FStar_Range.string_of_range uu____21133  in
                      let uu____21134 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21136 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21131 uu____21134 uu____21136
                       in
                    failwith uu____21129)
                  in
               match (binders, univs1) with
               | ([],uu____21157) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21183,uu____21184::uu____21185::uu____21186) ->
                   let uu____21207 =
                     let uu____21209 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21211 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21209 uu____21211
                      in
                   failwith uu____21207
               | uu____21222 ->
                   let uu____21237 =
                     let uu____21242 =
                       let uu____21243 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21243)  in
                     inst_tscheme_with uu____21242 insts  in
                   (match uu____21237 with
                    | (uu____21256,t) ->
                        let t1 =
                          let uu____21259 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21259 t  in
                        let uu____21260 =
                          let uu____21261 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21261.FStar_Syntax_Syntax.n  in
                        (match uu____21260 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21296 -> failwith "Impossible")))
        | uu____21304 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____21328 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21328 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21341,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21348 = find1 l2  in
            (match uu____21348 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21355 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____21355 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21359 = find1 l  in
            (match uu____21359 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____21364 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21364
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21385 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____21385 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21391) ->
            FStar_List.length bs
        | uu____21430 ->
            let uu____21431 =
              let uu____21437 =
                let uu____21439 = FStar_Ident.string_of_lid name  in
                let uu____21441 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21439 uu____21441
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21437)
               in
            FStar_Errors.raise_error uu____21431 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21460 = lookup_qname env l1  in
      match uu____21460 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21463;
              FStar_Syntax_Syntax.sigrng = uu____21464;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21466;
              FStar_Syntax_Syntax.sigattrs = uu____21467;
              FStar_Syntax_Syntax.sigopts = uu____21468;_},uu____21469),uu____21470)
          -> q
      | uu____21523 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21547 =
          let uu____21548 =
            let uu____21550 = FStar_Util.string_of_int i  in
            let uu____21552 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21550 uu____21552
             in
          failwith uu____21548  in
        let uu____21555 = lookup_datacon env lid  in
        match uu____21555 with
        | (uu____21560,t) ->
            let uu____21562 =
              let uu____21563 = FStar_Syntax_Subst.compress t  in
              uu____21563.FStar_Syntax_Syntax.n  in
            (match uu____21562 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21567) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21611 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21611
                      FStar_Pervasives_Native.fst)
             | uu____21622 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21636 = lookup_qname env l  in
      match uu____21636 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21638,uu____21639,uu____21640);
              FStar_Syntax_Syntax.sigrng = uu____21641;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21643;
              FStar_Syntax_Syntax.sigattrs = uu____21644;
              FStar_Syntax_Syntax.sigopts = uu____21645;_},uu____21646),uu____21647)
          ->
          FStar_Util.for_some
            (fun uu___7_21702  ->
               match uu___7_21702 with
               | FStar_Syntax_Syntax.Projector uu____21704 -> true
               | uu____21710 -> false) quals
      | uu____21712 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21726 = lookup_qname env lid  in
      match uu____21726 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21728,uu____21729,uu____21730,uu____21731,uu____21732,uu____21733);
              FStar_Syntax_Syntax.sigrng = uu____21734;
              FStar_Syntax_Syntax.sigquals = uu____21735;
              FStar_Syntax_Syntax.sigmeta = uu____21736;
              FStar_Syntax_Syntax.sigattrs = uu____21737;
              FStar_Syntax_Syntax.sigopts = uu____21738;_},uu____21739),uu____21740)
          -> true
      | uu____21800 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21814 = lookup_qname env lid  in
      match uu____21814 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21816,uu____21817,uu____21818,uu____21819,uu____21820,uu____21821);
              FStar_Syntax_Syntax.sigrng = uu____21822;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21824;
              FStar_Syntax_Syntax.sigattrs = uu____21825;
              FStar_Syntax_Syntax.sigopts = uu____21826;_},uu____21827),uu____21828)
          ->
          FStar_Util.for_some
            (fun uu___8_21891  ->
               match uu___8_21891 with
               | FStar_Syntax_Syntax.RecordType uu____21893 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21903 -> true
               | uu____21913 -> false) quals
      | uu____21915 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21925,uu____21926);
            FStar_Syntax_Syntax.sigrng = uu____21927;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21929;
            FStar_Syntax_Syntax.sigattrs = uu____21930;
            FStar_Syntax_Syntax.sigopts = uu____21931;_},uu____21932),uu____21933)
        ->
        FStar_Util.for_some
          (fun uu___9_21992  ->
             match uu___9_21992 with
             | FStar_Syntax_Syntax.Action uu____21994 -> true
             | uu____21996 -> false) quals
    | uu____21998 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____22012 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____22012
  
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
      let uu____22029 =
        let uu____22030 = FStar_Syntax_Util.un_uinst head1  in
        uu____22030.FStar_Syntax_Syntax.n  in
      match uu____22029 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____22036 ->
               true
           | uu____22039 -> false)
      | uu____22041 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22055 = lookup_qname env l  in
      match uu____22055 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22058),uu____22059) ->
          FStar_Util.for_some
            (fun uu___10_22107  ->
               match uu___10_22107 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22110 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22112 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22188 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22206) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22224 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22232 ->
                 FStar_Pervasives_Native.Some true
             | uu____22251 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22254 =
        let uu____22258 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22258 mapper  in
      match uu____22254 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____22318 = lookup_qname env lid  in
      match uu____22318 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22322,uu____22323,tps,uu____22325,uu____22326,uu____22327);
              FStar_Syntax_Syntax.sigrng = uu____22328;
              FStar_Syntax_Syntax.sigquals = uu____22329;
              FStar_Syntax_Syntax.sigmeta = uu____22330;
              FStar_Syntax_Syntax.sigattrs = uu____22331;
              FStar_Syntax_Syntax.sigopts = uu____22332;_},uu____22333),uu____22334)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22402 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22448  ->
              match uu____22448 with
              | (d,uu____22457) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____22473 = effect_decl_opt env l  in
      match uu____22473 with
      | FStar_Pervasives_Native.None  ->
          let uu____22488 = name_not_found l  in
          let uu____22494 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22488 uu____22494
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22522 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____22522
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22531  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22545  ->
            fun uu____22546  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22576 = FStar_Ident.lid_equals l1 l2  in
        if uu____22576
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____22587 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22587
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____22598 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22651  ->
                        match uu____22651 with
                        | (m1,m2,uu____22665,uu____22666,uu____22667) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22598 with
              | FStar_Pervasives_Native.None  ->
                  let uu____22684 =
                    let uu____22690 =
                      let uu____22692 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____22694 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____22692
                        uu____22694
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22690)
                     in
                  FStar_Errors.raise_error uu____22684 env.range
              | FStar_Pervasives_Native.Some
                  (uu____22704,uu____22705,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22739 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22739
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
  'Auu____22759 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22759) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22788 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22814  ->
                match uu____22814 with
                | (d,uu____22821) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22788 with
      | FStar_Pervasives_Native.None  ->
          let uu____22832 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22832
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22847 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22847 with
           | (uu____22858,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22876)::(wp,uu____22878)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22934 -> failwith "Impossible"))
  
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
        | uu____22999 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23012 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23012 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23029 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23029 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23054 =
                     let uu____23060 =
                       let uu____23062 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23070 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23081 =
                         let uu____23083 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23083  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23062 uu____23070 uu____23081
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23060)
                      in
                   FStar_Errors.raise_error uu____23054
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23091 =
                     let uu____23102 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23102 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23139  ->
                        fun uu____23140  ->
                          match (uu____23139, uu____23140) with
                          | ((x,uu____23170),(t,uu____23172)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23091
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23203 =
                     let uu___1598_23204 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1598_23204.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1598_23204.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1598_23204.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1598_23204.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23203
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23216 .
    'Auu____23216 ->
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
            let uu____23257 =
              let uu____23264 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____23264)  in
            match uu____23257 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23288 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23290 = FStar_Util.string_of_int given  in
                     let uu____23292 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23288 uu____23290 uu____23292
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23297 = effect_decl_opt env effect_name  in
          match uu____23297 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23319) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____23340 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr =
                     inst_effect_fun_with [u_res] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23347 =
                       let uu____23350 = get_range env  in
                       let uu____23351 =
                         let uu____23358 =
                           let uu____23359 =
                             let uu____23376 =
                               let uu____23387 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23387 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23376)  in
                           FStar_Syntax_Syntax.Tm_app uu____23359  in
                         FStar_Syntax_Syntax.mk uu____23358  in
                       uu____23351 FStar_Pervasives_Native.None uu____23350
                        in
                     FStar_Pervasives_Native.Some uu____23347)))
  
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
           (fun uu___11_23487  ->
              match uu___11_23487 with
              | FStar_Syntax_Syntax.Reflectable uu____23489 -> true
              | uu____23491 -> false))
  
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
      | uu____23551 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23566 =
        let uu____23567 = FStar_Syntax_Subst.compress t  in
        uu____23567.FStar_Syntax_Syntax.n  in
      match uu____23566 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23571,c) ->
          is_reifiable_comp env c
      | uu____23593 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23613 =
           let uu____23615 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23615  in
         if uu____23613
         then
           let uu____23618 =
             let uu____23624 =
               let uu____23626 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23626
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23624)  in
           let uu____23630 = get_range env  in
           FStar_Errors.raise_error uu____23618 uu____23630
         else ());
        (let uu____23633 = effect_repr_aux true env c u_c  in
         match uu____23633 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1674_23669 = env  in
        {
          solver = (uu___1674_23669.solver);
          range = (uu___1674_23669.range);
          curmodule = (uu___1674_23669.curmodule);
          gamma = (uu___1674_23669.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1674_23669.gamma_cache);
          modules = (uu___1674_23669.modules);
          expected_typ = (uu___1674_23669.expected_typ);
          sigtab = (uu___1674_23669.sigtab);
          attrtab = (uu___1674_23669.attrtab);
          instantiate_imp = (uu___1674_23669.instantiate_imp);
          effects = (uu___1674_23669.effects);
          generalize = (uu___1674_23669.generalize);
          letrecs = (uu___1674_23669.letrecs);
          top_level = (uu___1674_23669.top_level);
          check_uvars = (uu___1674_23669.check_uvars);
          use_eq = (uu___1674_23669.use_eq);
          is_iface = (uu___1674_23669.is_iface);
          admit = (uu___1674_23669.admit);
          lax = (uu___1674_23669.lax);
          lax_universes = (uu___1674_23669.lax_universes);
          phase1 = (uu___1674_23669.phase1);
          failhard = (uu___1674_23669.failhard);
          nosynth = (uu___1674_23669.nosynth);
          uvar_subtyping = (uu___1674_23669.uvar_subtyping);
          tc_term = (uu___1674_23669.tc_term);
          type_of = (uu___1674_23669.type_of);
          universe_of = (uu___1674_23669.universe_of);
          check_type_of = (uu___1674_23669.check_type_of);
          use_bv_sorts = (uu___1674_23669.use_bv_sorts);
          qtbl_name_and_index = (uu___1674_23669.qtbl_name_and_index);
          normalized_eff_names = (uu___1674_23669.normalized_eff_names);
          fv_delta_depths = (uu___1674_23669.fv_delta_depths);
          proof_ns = (uu___1674_23669.proof_ns);
          synth_hook = (uu___1674_23669.synth_hook);
          try_solve_implicits_hook =
            (uu___1674_23669.try_solve_implicits_hook);
          splice = (uu___1674_23669.splice);
          mpreprocess = (uu___1674_23669.mpreprocess);
          postprocess = (uu___1674_23669.postprocess);
          is_native_tactic = (uu___1674_23669.is_native_tactic);
          identifier_info = (uu___1674_23669.identifier_info);
          tc_hooks = (uu___1674_23669.tc_hooks);
          dsenv = (uu___1674_23669.dsenv);
          nbe = (uu___1674_23669.nbe);
          strict_args_tab = (uu___1674_23669.strict_args_tab);
          erasable_types_tab = (uu___1674_23669.erasable_types_tab)
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
    fun uu____23688  ->
      match uu____23688 with
      | (ed,quals) ->
          let effects =
            let uu___1683_23702 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1683_23702.order);
              joins = (uu___1683_23702.joins)
            }  in
          let uu___1686_23711 = env  in
          {
            solver = (uu___1686_23711.solver);
            range = (uu___1686_23711.range);
            curmodule = (uu___1686_23711.curmodule);
            gamma = (uu___1686_23711.gamma);
            gamma_sig = (uu___1686_23711.gamma_sig);
            gamma_cache = (uu___1686_23711.gamma_cache);
            modules = (uu___1686_23711.modules);
            expected_typ = (uu___1686_23711.expected_typ);
            sigtab = (uu___1686_23711.sigtab);
            attrtab = (uu___1686_23711.attrtab);
            instantiate_imp = (uu___1686_23711.instantiate_imp);
            effects;
            generalize = (uu___1686_23711.generalize);
            letrecs = (uu___1686_23711.letrecs);
            top_level = (uu___1686_23711.top_level);
            check_uvars = (uu___1686_23711.check_uvars);
            use_eq = (uu___1686_23711.use_eq);
            is_iface = (uu___1686_23711.is_iface);
            admit = (uu___1686_23711.admit);
            lax = (uu___1686_23711.lax);
            lax_universes = (uu___1686_23711.lax_universes);
            phase1 = (uu___1686_23711.phase1);
            failhard = (uu___1686_23711.failhard);
            nosynth = (uu___1686_23711.nosynth);
            uvar_subtyping = (uu___1686_23711.uvar_subtyping);
            tc_term = (uu___1686_23711.tc_term);
            type_of = (uu___1686_23711.type_of);
            universe_of = (uu___1686_23711.universe_of);
            check_type_of = (uu___1686_23711.check_type_of);
            use_bv_sorts = (uu___1686_23711.use_bv_sorts);
            qtbl_name_and_index = (uu___1686_23711.qtbl_name_and_index);
            normalized_eff_names = (uu___1686_23711.normalized_eff_names);
            fv_delta_depths = (uu___1686_23711.fv_delta_depths);
            proof_ns = (uu___1686_23711.proof_ns);
            synth_hook = (uu___1686_23711.synth_hook);
            try_solve_implicits_hook =
              (uu___1686_23711.try_solve_implicits_hook);
            splice = (uu___1686_23711.splice);
            mpreprocess = (uu___1686_23711.mpreprocess);
            postprocess = (uu___1686_23711.postprocess);
            is_native_tactic = (uu___1686_23711.is_native_tactic);
            identifier_info = (uu___1686_23711.identifier_info);
            tc_hooks = (uu___1686_23711.tc_hooks);
            dsenv = (uu___1686_23711.dsenv);
            nbe = (uu___1686_23711.nbe);
            strict_args_tab = (uu___1686_23711.strict_args_tab);
            erasable_types_tab = (uu___1686_23711.erasable_types_tab)
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
                let uu____23760 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____23760
                  (fun uu____23781  ->
                     match uu____23781 with
                     | (c1,g1) ->
                         let uu____23792 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____23792
                           (fun uu____23813  ->
                              match uu____23813 with
                              | (c2,g2) ->
                                  let uu____23824 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____23824)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____23946 = l1 u t e  in
                              l2 u t uu____23946))
                | uu____23947 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24015  ->
                    match uu____24015 with
                    | (e,uu____24023) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24046 =
            match uu____24046 with
            | (i,j) ->
                let uu____24057 = FStar_Ident.lid_equals i j  in
                if uu____24057
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _24064  -> FStar_Pervasives_Native.Some _24064)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24093 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24103 = FStar_Ident.lid_equals i k  in
                        if uu____24103
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24117 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24117
                                  then []
                                  else
                                    (let uu____24124 =
                                       let uu____24133 =
                                         find_edge order1 (i, k)  in
                                       let uu____24136 =
                                         find_edge order1 (k, j)  in
                                       (uu____24133, uu____24136)  in
                                     match uu____24124 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24151 =
                                           compose_edges e1 e2  in
                                         [uu____24151]
                                     | uu____24152 -> [])))))
                 in
              FStar_List.append order1 uu____24093  in
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
                  let uu____24182 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24185 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____24185
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24182
                  then
                    let uu____24192 =
                      let uu____24198 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24198)
                       in
                    let uu____24202 = get_range env  in
                    FStar_Errors.raise_error uu____24192 uu____24202
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt =
                               let uu____24280 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24280
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24332 =
                                             let uu____24341 =
                                               find_edge order2 (i, k)  in
                                             let uu____24344 =
                                               find_edge order2 (j, k)  in
                                             (uu____24341, uu____24344)  in
                                           match uu____24332 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____24386,uu____24387)
                                                    ->
                                                    let uu____24394 =
                                                      let uu____24401 =
                                                        let uu____24403 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24403
                                                         in
                                                      let uu____24406 =
                                                        let uu____24408 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24408
                                                         in
                                                      (uu____24401,
                                                        uu____24406)
                                                       in
                                                    (match uu____24394 with
                                                     | (true ,true ) ->
                                                         let uu____24425 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____24425
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
                                           | uu____24468 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1791_24541 = env.effects  in
             { decls = (uu___1791_24541.decls); order = order2; joins }  in
           let uu___1794_24542 = env  in
           {
             solver = (uu___1794_24542.solver);
             range = (uu___1794_24542.range);
             curmodule = (uu___1794_24542.curmodule);
             gamma = (uu___1794_24542.gamma);
             gamma_sig = (uu___1794_24542.gamma_sig);
             gamma_cache = (uu___1794_24542.gamma_cache);
             modules = (uu___1794_24542.modules);
             expected_typ = (uu___1794_24542.expected_typ);
             sigtab = (uu___1794_24542.sigtab);
             attrtab = (uu___1794_24542.attrtab);
             instantiate_imp = (uu___1794_24542.instantiate_imp);
             effects;
             generalize = (uu___1794_24542.generalize);
             letrecs = (uu___1794_24542.letrecs);
             top_level = (uu___1794_24542.top_level);
             check_uvars = (uu___1794_24542.check_uvars);
             use_eq = (uu___1794_24542.use_eq);
             is_iface = (uu___1794_24542.is_iface);
             admit = (uu___1794_24542.admit);
             lax = (uu___1794_24542.lax);
             lax_universes = (uu___1794_24542.lax_universes);
             phase1 = (uu___1794_24542.phase1);
             failhard = (uu___1794_24542.failhard);
             nosynth = (uu___1794_24542.nosynth);
             uvar_subtyping = (uu___1794_24542.uvar_subtyping);
             tc_term = (uu___1794_24542.tc_term);
             type_of = (uu___1794_24542.type_of);
             universe_of = (uu___1794_24542.universe_of);
             check_type_of = (uu___1794_24542.check_type_of);
             use_bv_sorts = (uu___1794_24542.use_bv_sorts);
             qtbl_name_and_index = (uu___1794_24542.qtbl_name_and_index);
             normalized_eff_names = (uu___1794_24542.normalized_eff_names);
             fv_delta_depths = (uu___1794_24542.fv_delta_depths);
             proof_ns = (uu___1794_24542.proof_ns);
             synth_hook = (uu___1794_24542.synth_hook);
             try_solve_implicits_hook =
               (uu___1794_24542.try_solve_implicits_hook);
             splice = (uu___1794_24542.splice);
             mpreprocess = (uu___1794_24542.mpreprocess);
             postprocess = (uu___1794_24542.postprocess);
             is_native_tactic = (uu___1794_24542.is_native_tactic);
             identifier_info = (uu___1794_24542.identifier_info);
             tc_hooks = (uu___1794_24542.tc_hooks);
             dsenv = (uu___1794_24542.dsenv);
             nbe = (uu___1794_24542.nbe);
             strict_args_tab = (uu___1794_24542.strict_args_tab);
             erasable_types_tab = (uu___1794_24542.erasable_types_tab)
           })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1798_24554 = env  in
      {
        solver = (uu___1798_24554.solver);
        range = (uu___1798_24554.range);
        curmodule = (uu___1798_24554.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1798_24554.gamma_sig);
        gamma_cache = (uu___1798_24554.gamma_cache);
        modules = (uu___1798_24554.modules);
        expected_typ = (uu___1798_24554.expected_typ);
        sigtab = (uu___1798_24554.sigtab);
        attrtab = (uu___1798_24554.attrtab);
        instantiate_imp = (uu___1798_24554.instantiate_imp);
        effects = (uu___1798_24554.effects);
        generalize = (uu___1798_24554.generalize);
        letrecs = (uu___1798_24554.letrecs);
        top_level = (uu___1798_24554.top_level);
        check_uvars = (uu___1798_24554.check_uvars);
        use_eq = (uu___1798_24554.use_eq);
        is_iface = (uu___1798_24554.is_iface);
        admit = (uu___1798_24554.admit);
        lax = (uu___1798_24554.lax);
        lax_universes = (uu___1798_24554.lax_universes);
        phase1 = (uu___1798_24554.phase1);
        failhard = (uu___1798_24554.failhard);
        nosynth = (uu___1798_24554.nosynth);
        uvar_subtyping = (uu___1798_24554.uvar_subtyping);
        tc_term = (uu___1798_24554.tc_term);
        type_of = (uu___1798_24554.type_of);
        universe_of = (uu___1798_24554.universe_of);
        check_type_of = (uu___1798_24554.check_type_of);
        use_bv_sorts = (uu___1798_24554.use_bv_sorts);
        qtbl_name_and_index = (uu___1798_24554.qtbl_name_and_index);
        normalized_eff_names = (uu___1798_24554.normalized_eff_names);
        fv_delta_depths = (uu___1798_24554.fv_delta_depths);
        proof_ns = (uu___1798_24554.proof_ns);
        synth_hook = (uu___1798_24554.synth_hook);
        try_solve_implicits_hook = (uu___1798_24554.try_solve_implicits_hook);
        splice = (uu___1798_24554.splice);
        mpreprocess = (uu___1798_24554.mpreprocess);
        postprocess = (uu___1798_24554.postprocess);
        is_native_tactic = (uu___1798_24554.is_native_tactic);
        identifier_info = (uu___1798_24554.identifier_info);
        tc_hooks = (uu___1798_24554.tc_hooks);
        dsenv = (uu___1798_24554.dsenv);
        nbe = (uu___1798_24554.nbe);
        strict_args_tab = (uu___1798_24554.strict_args_tab);
        erasable_types_tab = (uu___1798_24554.erasable_types_tab)
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
            (let uu___1811_24612 = env  in
             {
               solver = (uu___1811_24612.solver);
               range = (uu___1811_24612.range);
               curmodule = (uu___1811_24612.curmodule);
               gamma = rest;
               gamma_sig = (uu___1811_24612.gamma_sig);
               gamma_cache = (uu___1811_24612.gamma_cache);
               modules = (uu___1811_24612.modules);
               expected_typ = (uu___1811_24612.expected_typ);
               sigtab = (uu___1811_24612.sigtab);
               attrtab = (uu___1811_24612.attrtab);
               instantiate_imp = (uu___1811_24612.instantiate_imp);
               effects = (uu___1811_24612.effects);
               generalize = (uu___1811_24612.generalize);
               letrecs = (uu___1811_24612.letrecs);
               top_level = (uu___1811_24612.top_level);
               check_uvars = (uu___1811_24612.check_uvars);
               use_eq = (uu___1811_24612.use_eq);
               is_iface = (uu___1811_24612.is_iface);
               admit = (uu___1811_24612.admit);
               lax = (uu___1811_24612.lax);
               lax_universes = (uu___1811_24612.lax_universes);
               phase1 = (uu___1811_24612.phase1);
               failhard = (uu___1811_24612.failhard);
               nosynth = (uu___1811_24612.nosynth);
               uvar_subtyping = (uu___1811_24612.uvar_subtyping);
               tc_term = (uu___1811_24612.tc_term);
               type_of = (uu___1811_24612.type_of);
               universe_of = (uu___1811_24612.universe_of);
               check_type_of = (uu___1811_24612.check_type_of);
               use_bv_sorts = (uu___1811_24612.use_bv_sorts);
               qtbl_name_and_index = (uu___1811_24612.qtbl_name_and_index);
               normalized_eff_names = (uu___1811_24612.normalized_eff_names);
               fv_delta_depths = (uu___1811_24612.fv_delta_depths);
               proof_ns = (uu___1811_24612.proof_ns);
               synth_hook = (uu___1811_24612.synth_hook);
               try_solve_implicits_hook =
                 (uu___1811_24612.try_solve_implicits_hook);
               splice = (uu___1811_24612.splice);
               mpreprocess = (uu___1811_24612.mpreprocess);
               postprocess = (uu___1811_24612.postprocess);
               is_native_tactic = (uu___1811_24612.is_native_tactic);
               identifier_info = (uu___1811_24612.identifier_info);
               tc_hooks = (uu___1811_24612.tc_hooks);
               dsenv = (uu___1811_24612.dsenv);
               nbe = (uu___1811_24612.nbe);
               strict_args_tab = (uu___1811_24612.strict_args_tab);
               erasable_types_tab = (uu___1811_24612.erasable_types_tab)
             }))
    | uu____24613 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24642  ->
             match uu____24642 with | (x,uu____24650) -> push_bv env1 x) env
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
            let uu___1825_24685 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1825_24685.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1825_24685.FStar_Syntax_Syntax.index);
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
        let uu____24758 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24758 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24786 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24786)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1846_24802 = env  in
      {
        solver = (uu___1846_24802.solver);
        range = (uu___1846_24802.range);
        curmodule = (uu___1846_24802.curmodule);
        gamma = (uu___1846_24802.gamma);
        gamma_sig = (uu___1846_24802.gamma_sig);
        gamma_cache = (uu___1846_24802.gamma_cache);
        modules = (uu___1846_24802.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1846_24802.sigtab);
        attrtab = (uu___1846_24802.attrtab);
        instantiate_imp = (uu___1846_24802.instantiate_imp);
        effects = (uu___1846_24802.effects);
        generalize = (uu___1846_24802.generalize);
        letrecs = (uu___1846_24802.letrecs);
        top_level = (uu___1846_24802.top_level);
        check_uvars = (uu___1846_24802.check_uvars);
        use_eq = false;
        is_iface = (uu___1846_24802.is_iface);
        admit = (uu___1846_24802.admit);
        lax = (uu___1846_24802.lax);
        lax_universes = (uu___1846_24802.lax_universes);
        phase1 = (uu___1846_24802.phase1);
        failhard = (uu___1846_24802.failhard);
        nosynth = (uu___1846_24802.nosynth);
        uvar_subtyping = (uu___1846_24802.uvar_subtyping);
        tc_term = (uu___1846_24802.tc_term);
        type_of = (uu___1846_24802.type_of);
        universe_of = (uu___1846_24802.universe_of);
        check_type_of = (uu___1846_24802.check_type_of);
        use_bv_sorts = (uu___1846_24802.use_bv_sorts);
        qtbl_name_and_index = (uu___1846_24802.qtbl_name_and_index);
        normalized_eff_names = (uu___1846_24802.normalized_eff_names);
        fv_delta_depths = (uu___1846_24802.fv_delta_depths);
        proof_ns = (uu___1846_24802.proof_ns);
        synth_hook = (uu___1846_24802.synth_hook);
        try_solve_implicits_hook = (uu___1846_24802.try_solve_implicits_hook);
        splice = (uu___1846_24802.splice);
        mpreprocess = (uu___1846_24802.mpreprocess);
        postprocess = (uu___1846_24802.postprocess);
        is_native_tactic = (uu___1846_24802.is_native_tactic);
        identifier_info = (uu___1846_24802.identifier_info);
        tc_hooks = (uu___1846_24802.tc_hooks);
        dsenv = (uu___1846_24802.dsenv);
        nbe = (uu___1846_24802.nbe);
        strict_args_tab = (uu___1846_24802.strict_args_tab);
        erasable_types_tab = (uu___1846_24802.erasable_types_tab)
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
    let uu____24833 = expected_typ env_  in
    ((let uu___1853_24839 = env_  in
      {
        solver = (uu___1853_24839.solver);
        range = (uu___1853_24839.range);
        curmodule = (uu___1853_24839.curmodule);
        gamma = (uu___1853_24839.gamma);
        gamma_sig = (uu___1853_24839.gamma_sig);
        gamma_cache = (uu___1853_24839.gamma_cache);
        modules = (uu___1853_24839.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1853_24839.sigtab);
        attrtab = (uu___1853_24839.attrtab);
        instantiate_imp = (uu___1853_24839.instantiate_imp);
        effects = (uu___1853_24839.effects);
        generalize = (uu___1853_24839.generalize);
        letrecs = (uu___1853_24839.letrecs);
        top_level = (uu___1853_24839.top_level);
        check_uvars = (uu___1853_24839.check_uvars);
        use_eq = false;
        is_iface = (uu___1853_24839.is_iface);
        admit = (uu___1853_24839.admit);
        lax = (uu___1853_24839.lax);
        lax_universes = (uu___1853_24839.lax_universes);
        phase1 = (uu___1853_24839.phase1);
        failhard = (uu___1853_24839.failhard);
        nosynth = (uu___1853_24839.nosynth);
        uvar_subtyping = (uu___1853_24839.uvar_subtyping);
        tc_term = (uu___1853_24839.tc_term);
        type_of = (uu___1853_24839.type_of);
        universe_of = (uu___1853_24839.universe_of);
        check_type_of = (uu___1853_24839.check_type_of);
        use_bv_sorts = (uu___1853_24839.use_bv_sorts);
        qtbl_name_and_index = (uu___1853_24839.qtbl_name_and_index);
        normalized_eff_names = (uu___1853_24839.normalized_eff_names);
        fv_delta_depths = (uu___1853_24839.fv_delta_depths);
        proof_ns = (uu___1853_24839.proof_ns);
        synth_hook = (uu___1853_24839.synth_hook);
        try_solve_implicits_hook = (uu___1853_24839.try_solve_implicits_hook);
        splice = (uu___1853_24839.splice);
        mpreprocess = (uu___1853_24839.mpreprocess);
        postprocess = (uu___1853_24839.postprocess);
        is_native_tactic = (uu___1853_24839.is_native_tactic);
        identifier_info = (uu___1853_24839.identifier_info);
        tc_hooks = (uu___1853_24839.tc_hooks);
        dsenv = (uu___1853_24839.dsenv);
        nbe = (uu___1853_24839.nbe);
        strict_args_tab = (uu___1853_24839.strict_args_tab);
        erasable_types_tab = (uu___1853_24839.erasable_types_tab)
      }), uu____24833)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24851 =
      let uu____24854 = FStar_Ident.id_of_text ""  in [uu____24854]  in
    FStar_Ident.lid_of_ids uu____24851  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24861 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24861
        then
          let uu____24866 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24866 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1861_24894 = env  in
       {
         solver = (uu___1861_24894.solver);
         range = (uu___1861_24894.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1861_24894.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1861_24894.expected_typ);
         sigtab = (uu___1861_24894.sigtab);
         attrtab = (uu___1861_24894.attrtab);
         instantiate_imp = (uu___1861_24894.instantiate_imp);
         effects = (uu___1861_24894.effects);
         generalize = (uu___1861_24894.generalize);
         letrecs = (uu___1861_24894.letrecs);
         top_level = (uu___1861_24894.top_level);
         check_uvars = (uu___1861_24894.check_uvars);
         use_eq = (uu___1861_24894.use_eq);
         is_iface = (uu___1861_24894.is_iface);
         admit = (uu___1861_24894.admit);
         lax = (uu___1861_24894.lax);
         lax_universes = (uu___1861_24894.lax_universes);
         phase1 = (uu___1861_24894.phase1);
         failhard = (uu___1861_24894.failhard);
         nosynth = (uu___1861_24894.nosynth);
         uvar_subtyping = (uu___1861_24894.uvar_subtyping);
         tc_term = (uu___1861_24894.tc_term);
         type_of = (uu___1861_24894.type_of);
         universe_of = (uu___1861_24894.universe_of);
         check_type_of = (uu___1861_24894.check_type_of);
         use_bv_sorts = (uu___1861_24894.use_bv_sorts);
         qtbl_name_and_index = (uu___1861_24894.qtbl_name_and_index);
         normalized_eff_names = (uu___1861_24894.normalized_eff_names);
         fv_delta_depths = (uu___1861_24894.fv_delta_depths);
         proof_ns = (uu___1861_24894.proof_ns);
         synth_hook = (uu___1861_24894.synth_hook);
         try_solve_implicits_hook =
           (uu___1861_24894.try_solve_implicits_hook);
         splice = (uu___1861_24894.splice);
         mpreprocess = (uu___1861_24894.mpreprocess);
         postprocess = (uu___1861_24894.postprocess);
         is_native_tactic = (uu___1861_24894.is_native_tactic);
         identifier_info = (uu___1861_24894.identifier_info);
         tc_hooks = (uu___1861_24894.tc_hooks);
         dsenv = (uu___1861_24894.dsenv);
         nbe = (uu___1861_24894.nbe);
         strict_args_tab = (uu___1861_24894.strict_args_tab);
         erasable_types_tab = (uu___1861_24894.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24946)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24950,(uu____24951,t)))::tl1
          ->
          let uu____24972 =
            let uu____24975 = FStar_Syntax_Free.uvars t  in
            ext out uu____24975  in
          aux uu____24972 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24978;
            FStar_Syntax_Syntax.index = uu____24979;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24987 =
            let uu____24990 = FStar_Syntax_Free.uvars t  in
            ext out uu____24990  in
          aux uu____24987 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25048)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25052,(uu____25053,t)))::tl1
          ->
          let uu____25074 =
            let uu____25077 = FStar_Syntax_Free.univs t  in
            ext out uu____25077  in
          aux uu____25074 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25080;
            FStar_Syntax_Syntax.index = uu____25081;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25089 =
            let uu____25092 = FStar_Syntax_Free.univs t  in
            ext out uu____25092  in
          aux uu____25089 tl1
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
          let uu____25154 = FStar_Util.set_add uname out  in
          aux uu____25154 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25157,(uu____25158,t)))::tl1
          ->
          let uu____25179 =
            let uu____25182 = FStar_Syntax_Free.univnames t  in
            ext out uu____25182  in
          aux uu____25179 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25185;
            FStar_Syntax_Syntax.index = uu____25186;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25194 =
            let uu____25197 = FStar_Syntax_Free.univnames t  in
            ext out uu____25197  in
          aux uu____25194 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_25218  ->
            match uu___12_25218 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____25222 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____25235 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____25246 =
      let uu____25255 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____25255
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____25246 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____25303 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_25316  ->
              match uu___13_25316 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____25319 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____25319
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____25325) ->
                  let uu____25342 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____25342))
       in
    FStar_All.pipe_right uu____25303 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_25356  ->
    match uu___14_25356 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____25362 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____25362
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____25385  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____25440) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25473,uu____25474) -> false  in
      let uu____25488 =
        FStar_List.tryFind
          (fun uu____25510  ->
             match uu____25510 with | (p,uu____25521) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25488 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25540,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25570 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25570
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2004_25592 = e  in
        {
          solver = (uu___2004_25592.solver);
          range = (uu___2004_25592.range);
          curmodule = (uu___2004_25592.curmodule);
          gamma = (uu___2004_25592.gamma);
          gamma_sig = (uu___2004_25592.gamma_sig);
          gamma_cache = (uu___2004_25592.gamma_cache);
          modules = (uu___2004_25592.modules);
          expected_typ = (uu___2004_25592.expected_typ);
          sigtab = (uu___2004_25592.sigtab);
          attrtab = (uu___2004_25592.attrtab);
          instantiate_imp = (uu___2004_25592.instantiate_imp);
          effects = (uu___2004_25592.effects);
          generalize = (uu___2004_25592.generalize);
          letrecs = (uu___2004_25592.letrecs);
          top_level = (uu___2004_25592.top_level);
          check_uvars = (uu___2004_25592.check_uvars);
          use_eq = (uu___2004_25592.use_eq);
          is_iface = (uu___2004_25592.is_iface);
          admit = (uu___2004_25592.admit);
          lax = (uu___2004_25592.lax);
          lax_universes = (uu___2004_25592.lax_universes);
          phase1 = (uu___2004_25592.phase1);
          failhard = (uu___2004_25592.failhard);
          nosynth = (uu___2004_25592.nosynth);
          uvar_subtyping = (uu___2004_25592.uvar_subtyping);
          tc_term = (uu___2004_25592.tc_term);
          type_of = (uu___2004_25592.type_of);
          universe_of = (uu___2004_25592.universe_of);
          check_type_of = (uu___2004_25592.check_type_of);
          use_bv_sorts = (uu___2004_25592.use_bv_sorts);
          qtbl_name_and_index = (uu___2004_25592.qtbl_name_and_index);
          normalized_eff_names = (uu___2004_25592.normalized_eff_names);
          fv_delta_depths = (uu___2004_25592.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2004_25592.synth_hook);
          try_solve_implicits_hook =
            (uu___2004_25592.try_solve_implicits_hook);
          splice = (uu___2004_25592.splice);
          mpreprocess = (uu___2004_25592.mpreprocess);
          postprocess = (uu___2004_25592.postprocess);
          is_native_tactic = (uu___2004_25592.is_native_tactic);
          identifier_info = (uu___2004_25592.identifier_info);
          tc_hooks = (uu___2004_25592.tc_hooks);
          dsenv = (uu___2004_25592.dsenv);
          nbe = (uu___2004_25592.nbe);
          strict_args_tab = (uu___2004_25592.strict_args_tab);
          erasable_types_tab = (uu___2004_25592.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2013_25640 = e  in
      {
        solver = (uu___2013_25640.solver);
        range = (uu___2013_25640.range);
        curmodule = (uu___2013_25640.curmodule);
        gamma = (uu___2013_25640.gamma);
        gamma_sig = (uu___2013_25640.gamma_sig);
        gamma_cache = (uu___2013_25640.gamma_cache);
        modules = (uu___2013_25640.modules);
        expected_typ = (uu___2013_25640.expected_typ);
        sigtab = (uu___2013_25640.sigtab);
        attrtab = (uu___2013_25640.attrtab);
        instantiate_imp = (uu___2013_25640.instantiate_imp);
        effects = (uu___2013_25640.effects);
        generalize = (uu___2013_25640.generalize);
        letrecs = (uu___2013_25640.letrecs);
        top_level = (uu___2013_25640.top_level);
        check_uvars = (uu___2013_25640.check_uvars);
        use_eq = (uu___2013_25640.use_eq);
        is_iface = (uu___2013_25640.is_iface);
        admit = (uu___2013_25640.admit);
        lax = (uu___2013_25640.lax);
        lax_universes = (uu___2013_25640.lax_universes);
        phase1 = (uu___2013_25640.phase1);
        failhard = (uu___2013_25640.failhard);
        nosynth = (uu___2013_25640.nosynth);
        uvar_subtyping = (uu___2013_25640.uvar_subtyping);
        tc_term = (uu___2013_25640.tc_term);
        type_of = (uu___2013_25640.type_of);
        universe_of = (uu___2013_25640.universe_of);
        check_type_of = (uu___2013_25640.check_type_of);
        use_bv_sorts = (uu___2013_25640.use_bv_sorts);
        qtbl_name_and_index = (uu___2013_25640.qtbl_name_and_index);
        normalized_eff_names = (uu___2013_25640.normalized_eff_names);
        fv_delta_depths = (uu___2013_25640.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2013_25640.synth_hook);
        try_solve_implicits_hook = (uu___2013_25640.try_solve_implicits_hook);
        splice = (uu___2013_25640.splice);
        mpreprocess = (uu___2013_25640.mpreprocess);
        postprocess = (uu___2013_25640.postprocess);
        is_native_tactic = (uu___2013_25640.is_native_tactic);
        identifier_info = (uu___2013_25640.identifier_info);
        tc_hooks = (uu___2013_25640.tc_hooks);
        dsenv = (uu___2013_25640.dsenv);
        nbe = (uu___2013_25640.nbe);
        strict_args_tab = (uu___2013_25640.strict_args_tab);
        erasable_types_tab = (uu___2013_25640.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25656 = FStar_Syntax_Free.names t  in
      let uu____25659 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25656 uu____25659
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25682 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25682
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25692 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25692
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25713 =
      match uu____25713 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25733 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25733)
       in
    let uu____25741 =
      let uu____25745 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25745 FStar_List.rev  in
    FStar_All.pipe_right uu____25741 (FStar_String.concat " ")
  
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
                  (let uu____25813 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25813 with
                   | FStar_Pervasives_Native.Some uu____25817 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25820 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25830;
        FStar_TypeChecker_Common.univ_ineqs = uu____25831;
        FStar_TypeChecker_Common.implicits = uu____25832;_} -> true
    | uu____25842 -> false
  
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
          let uu___2057_25864 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2057_25864.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2057_25864.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2057_25864.FStar_TypeChecker_Common.implicits)
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
          let uu____25903 = FStar_Options.defensive ()  in
          if uu____25903
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25909 =
              let uu____25911 =
                let uu____25913 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25913  in
              Prims.op_Negation uu____25911  in
            (if uu____25909
             then
               let uu____25920 =
                 let uu____25926 =
                   let uu____25928 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25930 =
                     let uu____25932 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25932
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25928 uu____25930
                    in
                 (FStar_Errors.Warning_Defensive, uu____25926)  in
               FStar_Errors.log_issue rng uu____25920
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
          let uu____25972 =
            let uu____25974 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25974  in
          if uu____25972
          then ()
          else
            (let uu____25979 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25979 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26005 =
            let uu____26007 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26007  in
          if uu____26005
          then ()
          else
            (let uu____26012 = bound_vars e  in
             def_check_closed_in rng msg uu____26012 t)
  
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
          let uu___2094_26051 = g  in
          let uu____26052 =
            let uu____26053 =
              let uu____26054 =
                let uu____26061 =
                  let uu____26062 =
                    let uu____26079 =
                      let uu____26090 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____26090]  in
                    (f, uu____26079)  in
                  FStar_Syntax_Syntax.Tm_app uu____26062  in
                FStar_Syntax_Syntax.mk uu____26061  in
              uu____26054 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _26127  -> FStar_TypeChecker_Common.NonTrivial _26127)
              uu____26053
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____26052;
            FStar_TypeChecker_Common.deferred =
              (uu___2094_26051.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2094_26051.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2094_26051.FStar_TypeChecker_Common.implicits)
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
          let uu___2101_26145 = g  in
          let uu____26146 =
            let uu____26147 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26147  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26146;
            FStar_TypeChecker_Common.deferred =
              (uu___2101_26145.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2101_26145.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2101_26145.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2106_26164 = g  in
          let uu____26165 =
            let uu____26166 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____26166  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26165;
            FStar_TypeChecker_Common.deferred =
              (uu___2106_26164.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2106_26164.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2106_26164.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2110_26168 = g  in
          let uu____26169 =
            let uu____26170 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26170  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26169;
            FStar_TypeChecker_Common.deferred =
              (uu___2110_26168.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2110_26168.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2110_26168.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____26177 ->
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
                       let uu____26254 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____26254
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2133_26261 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2133_26261.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2133_26261.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2133_26261.FStar_TypeChecker_Common.implicits)
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
               let uu____26295 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____26295
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
            let uu___2148_26322 = g  in
            let uu____26323 =
              let uu____26324 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____26324  in
            {
              FStar_TypeChecker_Common.guard_f = uu____26323;
              FStar_TypeChecker_Common.deferred =
                (uu___2148_26322.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2148_26322.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2148_26322.FStar_TypeChecker_Common.implicits)
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
              let uu____26382 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26382 with
              | FStar_Pervasives_Native.Some
                  (uu____26407::(tm,uu____26409)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26473 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26491 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26491;
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
                      let uu___2170_26523 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2170_26523.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2170_26523.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2170_26523.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____26577 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____26634  ->
                      fun b  ->
                        match uu____26634 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____26676 =
                              let uu____26689 = reason b  in
                              new_implicit_var_aux uu____26689 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____26676 with
                             | (t,uu____26706,g_t) ->
                                 let uu____26720 =
                                   let uu____26723 =
                                     let uu____26726 =
                                       let uu____26727 =
                                         let uu____26734 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26734, t)  in
                                       FStar_Syntax_Syntax.NT uu____26727  in
                                     [uu____26726]  in
                                   FStar_List.append substs1 uu____26723  in
                                 let uu____26745 = conj_guard g g_t  in
                                 (uu____26720,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26745))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____26577
              (fun uu____26774  ->
                 match uu____26774 with
                 | (uu____26791,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26807  -> ());
    push = (fun uu____26809  -> ());
    pop = (fun uu____26812  -> ());
    snapshot =
      (fun uu____26815  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26834  -> fun uu____26835  -> ());
    encode_sig = (fun uu____26850  -> fun uu____26851  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26857 =
             let uu____26864 = FStar_Options.peek ()  in (e, g, uu____26864)
              in
           [uu____26857]);
    solve = (fun uu____26880  -> fun uu____26881  -> fun uu____26882  -> ());
    finish = (fun uu____26889  -> ());
    refresh = (fun uu____26891  -> ())
  } 