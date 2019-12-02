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
  abbrevs: FStar_Ident.lident Prims.list ;
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
  fun projectee  ->
    match projectee with | { decls; abbrevs; order; joins;_} -> decls
  
let (__proj__Mkeffects__item__abbrevs :
  effects -> FStar_Ident.lident Prims.list) =
  fun projectee  ->
    match projectee with | { decls; abbrevs; order; joins;_} -> abbrevs
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with | { decls; abbrevs; order; joins;_} -> order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift *
      mlift) Prims.list)
  =
  fun projectee  ->
    match projectee with | { decls; abbrevs; order; joins;_} -> joins
  
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
           (fun uu___0_13021  ->
              match uu___0_13021 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13024 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13024  in
                  let uu____13025 =
                    let uu____13026 = FStar_Syntax_Subst.compress y  in
                    uu____13026.FStar_Syntax_Syntax.n  in
                  (match uu____13025 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13030 =
                         let uu___318_13031 = y1  in
                         let uu____13032 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___318_13031.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___318_13031.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13032
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13030
                   | uu____13035 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___324_13049 = env  in
      let uu____13050 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___324_13049.solver);
        range = (uu___324_13049.range);
        curmodule = (uu___324_13049.curmodule);
        gamma = uu____13050;
        gamma_sig = (uu___324_13049.gamma_sig);
        gamma_cache = (uu___324_13049.gamma_cache);
        modules = (uu___324_13049.modules);
        expected_typ = (uu___324_13049.expected_typ);
        sigtab = (uu___324_13049.sigtab);
        attrtab = (uu___324_13049.attrtab);
        instantiate_imp = (uu___324_13049.instantiate_imp);
        effects = (uu___324_13049.effects);
        generalize = (uu___324_13049.generalize);
        letrecs = (uu___324_13049.letrecs);
        top_level = (uu___324_13049.top_level);
        check_uvars = (uu___324_13049.check_uvars);
        use_eq = (uu___324_13049.use_eq);
        is_iface = (uu___324_13049.is_iface);
        admit = (uu___324_13049.admit);
        lax = (uu___324_13049.lax);
        lax_universes = (uu___324_13049.lax_universes);
        phase1 = (uu___324_13049.phase1);
        failhard = (uu___324_13049.failhard);
        nosynth = (uu___324_13049.nosynth);
        uvar_subtyping = (uu___324_13049.uvar_subtyping);
        tc_term = (uu___324_13049.tc_term);
        type_of = (uu___324_13049.type_of);
        universe_of = (uu___324_13049.universe_of);
        check_type_of = (uu___324_13049.check_type_of);
        use_bv_sorts = (uu___324_13049.use_bv_sorts);
        qtbl_name_and_index = (uu___324_13049.qtbl_name_and_index);
        normalized_eff_names = (uu___324_13049.normalized_eff_names);
        fv_delta_depths = (uu___324_13049.fv_delta_depths);
        proof_ns = (uu___324_13049.proof_ns);
        synth_hook = (uu___324_13049.synth_hook);
        splice = (uu___324_13049.splice);
        mpreprocess = (uu___324_13049.mpreprocess);
        postprocess = (uu___324_13049.postprocess);
        is_native_tactic = (uu___324_13049.is_native_tactic);
        identifier_info = (uu___324_13049.identifier_info);
        tc_hooks = (uu___324_13049.tc_hooks);
        dsenv = (uu___324_13049.dsenv);
        nbe = (uu___324_13049.nbe);
        strict_args_tab = (uu___324_13049.strict_args_tab);
        erasable_types_tab = (uu___324_13049.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13058  -> fun uu____13059  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___331_13081 = env  in
      {
        solver = (uu___331_13081.solver);
        range = (uu___331_13081.range);
        curmodule = (uu___331_13081.curmodule);
        gamma = (uu___331_13081.gamma);
        gamma_sig = (uu___331_13081.gamma_sig);
        gamma_cache = (uu___331_13081.gamma_cache);
        modules = (uu___331_13081.modules);
        expected_typ = (uu___331_13081.expected_typ);
        sigtab = (uu___331_13081.sigtab);
        attrtab = (uu___331_13081.attrtab);
        instantiate_imp = (uu___331_13081.instantiate_imp);
        effects = (uu___331_13081.effects);
        generalize = (uu___331_13081.generalize);
        letrecs = (uu___331_13081.letrecs);
        top_level = (uu___331_13081.top_level);
        check_uvars = (uu___331_13081.check_uvars);
        use_eq = (uu___331_13081.use_eq);
        is_iface = (uu___331_13081.is_iface);
        admit = (uu___331_13081.admit);
        lax = (uu___331_13081.lax);
        lax_universes = (uu___331_13081.lax_universes);
        phase1 = (uu___331_13081.phase1);
        failhard = (uu___331_13081.failhard);
        nosynth = (uu___331_13081.nosynth);
        uvar_subtyping = (uu___331_13081.uvar_subtyping);
        tc_term = (uu___331_13081.tc_term);
        type_of = (uu___331_13081.type_of);
        universe_of = (uu___331_13081.universe_of);
        check_type_of = (uu___331_13081.check_type_of);
        use_bv_sorts = (uu___331_13081.use_bv_sorts);
        qtbl_name_and_index = (uu___331_13081.qtbl_name_and_index);
        normalized_eff_names = (uu___331_13081.normalized_eff_names);
        fv_delta_depths = (uu___331_13081.fv_delta_depths);
        proof_ns = (uu___331_13081.proof_ns);
        synth_hook = (uu___331_13081.synth_hook);
        splice = (uu___331_13081.splice);
        mpreprocess = (uu___331_13081.mpreprocess);
        postprocess = (uu___331_13081.postprocess);
        is_native_tactic = (uu___331_13081.is_native_tactic);
        identifier_info = (uu___331_13081.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___331_13081.dsenv);
        nbe = (uu___331_13081.nbe);
        strict_args_tab = (uu___331_13081.strict_args_tab);
        erasable_types_tab = (uu___331_13081.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___335_13093 = e  in
      let uu____13094 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___335_13093.solver);
        range = (uu___335_13093.range);
        curmodule = (uu___335_13093.curmodule);
        gamma = (uu___335_13093.gamma);
        gamma_sig = (uu___335_13093.gamma_sig);
        gamma_cache = (uu___335_13093.gamma_cache);
        modules = (uu___335_13093.modules);
        expected_typ = (uu___335_13093.expected_typ);
        sigtab = (uu___335_13093.sigtab);
        attrtab = (uu___335_13093.attrtab);
        instantiate_imp = (uu___335_13093.instantiate_imp);
        effects = (uu___335_13093.effects);
        generalize = (uu___335_13093.generalize);
        letrecs = (uu___335_13093.letrecs);
        top_level = (uu___335_13093.top_level);
        check_uvars = (uu___335_13093.check_uvars);
        use_eq = (uu___335_13093.use_eq);
        is_iface = (uu___335_13093.is_iface);
        admit = (uu___335_13093.admit);
        lax = (uu___335_13093.lax);
        lax_universes = (uu___335_13093.lax_universes);
        phase1 = (uu___335_13093.phase1);
        failhard = (uu___335_13093.failhard);
        nosynth = (uu___335_13093.nosynth);
        uvar_subtyping = (uu___335_13093.uvar_subtyping);
        tc_term = (uu___335_13093.tc_term);
        type_of = (uu___335_13093.type_of);
        universe_of = (uu___335_13093.universe_of);
        check_type_of = (uu___335_13093.check_type_of);
        use_bv_sorts = (uu___335_13093.use_bv_sorts);
        qtbl_name_and_index = (uu___335_13093.qtbl_name_and_index);
        normalized_eff_names = (uu___335_13093.normalized_eff_names);
        fv_delta_depths = (uu___335_13093.fv_delta_depths);
        proof_ns = (uu___335_13093.proof_ns);
        synth_hook = (uu___335_13093.synth_hook);
        splice = (uu___335_13093.splice);
        mpreprocess = (uu___335_13093.mpreprocess);
        postprocess = (uu___335_13093.postprocess);
        is_native_tactic = (uu___335_13093.is_native_tactic);
        identifier_info = (uu___335_13093.identifier_info);
        tc_hooks = (uu___335_13093.tc_hooks);
        dsenv = uu____13094;
        nbe = (uu___335_13093.nbe);
        strict_args_tab = (uu___335_13093.strict_args_tab);
        erasable_types_tab = (uu___335_13093.erasable_types_tab)
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
      | (NoDelta ,uu____13123) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13126,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13128,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13131 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13145 . unit -> 'Auu____13145 FStar_Util.smap =
  fun uu____13152  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13158 . unit -> 'Auu____13158 FStar_Util.smap =
  fun uu____13165  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13303 = new_gamma_cache ()  in
                  let uu____13306 = new_sigtab ()  in
                  let uu____13309 = new_sigtab ()  in
                  let uu____13316 =
                    let uu____13331 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13331, FStar_Pervasives_Native.None)  in
                  let uu____13352 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13356 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13360 = FStar_Options.using_facts_from ()  in
                  let uu____13361 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13364 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13365 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13379 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13303;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13306;
                    attrtab = uu____13309;
                    instantiate_imp = true;
                    effects =
                      { decls = []; abbrevs = []; order = []; joins = [] };
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
                    qtbl_name_and_index = uu____13316;
                    normalized_eff_names = uu____13352;
                    fv_delta_depths = uu____13356;
                    proof_ns = uu____13360;
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
                    is_native_tactic = (fun uu____13452  -> false);
                    identifier_info = uu____13361;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13364;
                    nbe = nbe1;
                    strict_args_tab = uu____13365;
                    erasable_types_tab = uu____13379
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
  fun uu____13531  ->
    let uu____13532 = FStar_ST.op_Bang query_indices  in
    match uu____13532 with
    | [] -> failwith "Empty query indices!"
    | uu____13587 ->
        let uu____13597 =
          let uu____13607 =
            let uu____13615 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13615  in
          let uu____13669 = FStar_ST.op_Bang query_indices  in uu____13607 ::
            uu____13669
           in
        FStar_ST.op_Colon_Equals query_indices uu____13597
  
let (pop_query_indices : unit -> unit) =
  fun uu____13765  ->
    let uu____13766 = FStar_ST.op_Bang query_indices  in
    match uu____13766 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13893  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13930  ->
    match uu____13930 with
    | (l,n1) ->
        let uu____13940 = FStar_ST.op_Bang query_indices  in
        (match uu____13940 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14062 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14085  ->
    let uu____14086 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14086
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14154 =
       let uu____14157 = FStar_ST.op_Bang stack  in env :: uu____14157  in
     FStar_ST.op_Colon_Equals stack uu____14154);
    (let uu___406_14206 = env  in
     let uu____14207 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14210 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14213 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14220 =
       let uu____14235 =
         let uu____14239 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14239  in
       let uu____14271 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14235, uu____14271)  in
     let uu____14320 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14323 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14326 =
       let uu____14329 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14329  in
     let uu____14349 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14362 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___406_14206.solver);
       range = (uu___406_14206.range);
       curmodule = (uu___406_14206.curmodule);
       gamma = (uu___406_14206.gamma);
       gamma_sig = (uu___406_14206.gamma_sig);
       gamma_cache = uu____14207;
       modules = (uu___406_14206.modules);
       expected_typ = (uu___406_14206.expected_typ);
       sigtab = uu____14210;
       attrtab = uu____14213;
       instantiate_imp = (uu___406_14206.instantiate_imp);
       effects = (uu___406_14206.effects);
       generalize = (uu___406_14206.generalize);
       letrecs = (uu___406_14206.letrecs);
       top_level = (uu___406_14206.top_level);
       check_uvars = (uu___406_14206.check_uvars);
       use_eq = (uu___406_14206.use_eq);
       is_iface = (uu___406_14206.is_iface);
       admit = (uu___406_14206.admit);
       lax = (uu___406_14206.lax);
       lax_universes = (uu___406_14206.lax_universes);
       phase1 = (uu___406_14206.phase1);
       failhard = (uu___406_14206.failhard);
       nosynth = (uu___406_14206.nosynth);
       uvar_subtyping = (uu___406_14206.uvar_subtyping);
       tc_term = (uu___406_14206.tc_term);
       type_of = (uu___406_14206.type_of);
       universe_of = (uu___406_14206.universe_of);
       check_type_of = (uu___406_14206.check_type_of);
       use_bv_sorts = (uu___406_14206.use_bv_sorts);
       qtbl_name_and_index = uu____14220;
       normalized_eff_names = uu____14320;
       fv_delta_depths = uu____14323;
       proof_ns = (uu___406_14206.proof_ns);
       synth_hook = (uu___406_14206.synth_hook);
       splice = (uu___406_14206.splice);
       mpreprocess = (uu___406_14206.mpreprocess);
       postprocess = (uu___406_14206.postprocess);
       is_native_tactic = (uu___406_14206.is_native_tactic);
       identifier_info = uu____14326;
       tc_hooks = (uu___406_14206.tc_hooks);
       dsenv = (uu___406_14206.dsenv);
       nbe = (uu___406_14206.nbe);
       strict_args_tab = uu____14349;
       erasable_types_tab = uu____14362
     })
  
let (pop_stack : unit -> env) =
  fun uu____14372  ->
    let uu____14373 = FStar_ST.op_Bang stack  in
    match uu____14373 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14427 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14517  ->
           let uu____14518 = snapshot_stack env  in
           match uu____14518 with
           | (stack_depth,env1) ->
               let uu____14552 = snapshot_query_indices ()  in
               (match uu____14552 with
                | (query_indices_depth,()) ->
                    let uu____14585 = (env1.solver).snapshot msg  in
                    (match uu____14585 with
                     | (solver_depth,()) ->
                         let uu____14642 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14642 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___431_14709 = env1  in
                                 {
                                   solver = (uu___431_14709.solver);
                                   range = (uu___431_14709.range);
                                   curmodule = (uu___431_14709.curmodule);
                                   gamma = (uu___431_14709.gamma);
                                   gamma_sig = (uu___431_14709.gamma_sig);
                                   gamma_cache = (uu___431_14709.gamma_cache);
                                   modules = (uu___431_14709.modules);
                                   expected_typ =
                                     (uu___431_14709.expected_typ);
                                   sigtab = (uu___431_14709.sigtab);
                                   attrtab = (uu___431_14709.attrtab);
                                   instantiate_imp =
                                     (uu___431_14709.instantiate_imp);
                                   effects = (uu___431_14709.effects);
                                   generalize = (uu___431_14709.generalize);
                                   letrecs = (uu___431_14709.letrecs);
                                   top_level = (uu___431_14709.top_level);
                                   check_uvars = (uu___431_14709.check_uvars);
                                   use_eq = (uu___431_14709.use_eq);
                                   is_iface = (uu___431_14709.is_iface);
                                   admit = (uu___431_14709.admit);
                                   lax = (uu___431_14709.lax);
                                   lax_universes =
                                     (uu___431_14709.lax_universes);
                                   phase1 = (uu___431_14709.phase1);
                                   failhard = (uu___431_14709.failhard);
                                   nosynth = (uu___431_14709.nosynth);
                                   uvar_subtyping =
                                     (uu___431_14709.uvar_subtyping);
                                   tc_term = (uu___431_14709.tc_term);
                                   type_of = (uu___431_14709.type_of);
                                   universe_of = (uu___431_14709.universe_of);
                                   check_type_of =
                                     (uu___431_14709.check_type_of);
                                   use_bv_sorts =
                                     (uu___431_14709.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___431_14709.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___431_14709.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___431_14709.fv_delta_depths);
                                   proof_ns = (uu___431_14709.proof_ns);
                                   synth_hook = (uu___431_14709.synth_hook);
                                   splice = (uu___431_14709.splice);
                                   mpreprocess = (uu___431_14709.mpreprocess);
                                   postprocess = (uu___431_14709.postprocess);
                                   is_native_tactic =
                                     (uu___431_14709.is_native_tactic);
                                   identifier_info =
                                     (uu___431_14709.identifier_info);
                                   tc_hooks = (uu___431_14709.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___431_14709.nbe);
                                   strict_args_tab =
                                     (uu___431_14709.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___431_14709.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14743  ->
             let uu____14744 =
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
             match uu____14744 with
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
                             ((let uu____14924 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14924
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14940 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14940
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14972,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15014 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15044  ->
                  match uu____15044 with
                  | (m,uu____15052) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15014 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___476_15067 = env  in
               {
                 solver = (uu___476_15067.solver);
                 range = (uu___476_15067.range);
                 curmodule = (uu___476_15067.curmodule);
                 gamma = (uu___476_15067.gamma);
                 gamma_sig = (uu___476_15067.gamma_sig);
                 gamma_cache = (uu___476_15067.gamma_cache);
                 modules = (uu___476_15067.modules);
                 expected_typ = (uu___476_15067.expected_typ);
                 sigtab = (uu___476_15067.sigtab);
                 attrtab = (uu___476_15067.attrtab);
                 instantiate_imp = (uu___476_15067.instantiate_imp);
                 effects = (uu___476_15067.effects);
                 generalize = (uu___476_15067.generalize);
                 letrecs = (uu___476_15067.letrecs);
                 top_level = (uu___476_15067.top_level);
                 check_uvars = (uu___476_15067.check_uvars);
                 use_eq = (uu___476_15067.use_eq);
                 is_iface = (uu___476_15067.is_iface);
                 admit = (uu___476_15067.admit);
                 lax = (uu___476_15067.lax);
                 lax_universes = (uu___476_15067.lax_universes);
                 phase1 = (uu___476_15067.phase1);
                 failhard = (uu___476_15067.failhard);
                 nosynth = (uu___476_15067.nosynth);
                 uvar_subtyping = (uu___476_15067.uvar_subtyping);
                 tc_term = (uu___476_15067.tc_term);
                 type_of = (uu___476_15067.type_of);
                 universe_of = (uu___476_15067.universe_of);
                 check_type_of = (uu___476_15067.check_type_of);
                 use_bv_sorts = (uu___476_15067.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___476_15067.normalized_eff_names);
                 fv_delta_depths = (uu___476_15067.fv_delta_depths);
                 proof_ns = (uu___476_15067.proof_ns);
                 synth_hook = (uu___476_15067.synth_hook);
                 splice = (uu___476_15067.splice);
                 mpreprocess = (uu___476_15067.mpreprocess);
                 postprocess = (uu___476_15067.postprocess);
                 is_native_tactic = (uu___476_15067.is_native_tactic);
                 identifier_info = (uu___476_15067.identifier_info);
                 tc_hooks = (uu___476_15067.tc_hooks);
                 dsenv = (uu___476_15067.dsenv);
                 nbe = (uu___476_15067.nbe);
                 strict_args_tab = (uu___476_15067.strict_args_tab);
                 erasable_types_tab = (uu___476_15067.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15084,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___485_15100 = env  in
               {
                 solver = (uu___485_15100.solver);
                 range = (uu___485_15100.range);
                 curmodule = (uu___485_15100.curmodule);
                 gamma = (uu___485_15100.gamma);
                 gamma_sig = (uu___485_15100.gamma_sig);
                 gamma_cache = (uu___485_15100.gamma_cache);
                 modules = (uu___485_15100.modules);
                 expected_typ = (uu___485_15100.expected_typ);
                 sigtab = (uu___485_15100.sigtab);
                 attrtab = (uu___485_15100.attrtab);
                 instantiate_imp = (uu___485_15100.instantiate_imp);
                 effects = (uu___485_15100.effects);
                 generalize = (uu___485_15100.generalize);
                 letrecs = (uu___485_15100.letrecs);
                 top_level = (uu___485_15100.top_level);
                 check_uvars = (uu___485_15100.check_uvars);
                 use_eq = (uu___485_15100.use_eq);
                 is_iface = (uu___485_15100.is_iface);
                 admit = (uu___485_15100.admit);
                 lax = (uu___485_15100.lax);
                 lax_universes = (uu___485_15100.lax_universes);
                 phase1 = (uu___485_15100.phase1);
                 failhard = (uu___485_15100.failhard);
                 nosynth = (uu___485_15100.nosynth);
                 uvar_subtyping = (uu___485_15100.uvar_subtyping);
                 tc_term = (uu___485_15100.tc_term);
                 type_of = (uu___485_15100.type_of);
                 universe_of = (uu___485_15100.universe_of);
                 check_type_of = (uu___485_15100.check_type_of);
                 use_bv_sorts = (uu___485_15100.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___485_15100.normalized_eff_names);
                 fv_delta_depths = (uu___485_15100.fv_delta_depths);
                 proof_ns = (uu___485_15100.proof_ns);
                 synth_hook = (uu___485_15100.synth_hook);
                 splice = (uu___485_15100.splice);
                 mpreprocess = (uu___485_15100.mpreprocess);
                 postprocess = (uu___485_15100.postprocess);
                 is_native_tactic = (uu___485_15100.is_native_tactic);
                 identifier_info = (uu___485_15100.identifier_info);
                 tc_hooks = (uu___485_15100.tc_hooks);
                 dsenv = (uu___485_15100.dsenv);
                 nbe = (uu___485_15100.nbe);
                 strict_args_tab = (uu___485_15100.strict_args_tab);
                 erasable_types_tab = (uu___485_15100.erasable_types_tab)
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
        (let uu___492_15143 = e  in
         {
           solver = (uu___492_15143.solver);
           range = r;
           curmodule = (uu___492_15143.curmodule);
           gamma = (uu___492_15143.gamma);
           gamma_sig = (uu___492_15143.gamma_sig);
           gamma_cache = (uu___492_15143.gamma_cache);
           modules = (uu___492_15143.modules);
           expected_typ = (uu___492_15143.expected_typ);
           sigtab = (uu___492_15143.sigtab);
           attrtab = (uu___492_15143.attrtab);
           instantiate_imp = (uu___492_15143.instantiate_imp);
           effects = (uu___492_15143.effects);
           generalize = (uu___492_15143.generalize);
           letrecs = (uu___492_15143.letrecs);
           top_level = (uu___492_15143.top_level);
           check_uvars = (uu___492_15143.check_uvars);
           use_eq = (uu___492_15143.use_eq);
           is_iface = (uu___492_15143.is_iface);
           admit = (uu___492_15143.admit);
           lax = (uu___492_15143.lax);
           lax_universes = (uu___492_15143.lax_universes);
           phase1 = (uu___492_15143.phase1);
           failhard = (uu___492_15143.failhard);
           nosynth = (uu___492_15143.nosynth);
           uvar_subtyping = (uu___492_15143.uvar_subtyping);
           tc_term = (uu___492_15143.tc_term);
           type_of = (uu___492_15143.type_of);
           universe_of = (uu___492_15143.universe_of);
           check_type_of = (uu___492_15143.check_type_of);
           use_bv_sorts = (uu___492_15143.use_bv_sorts);
           qtbl_name_and_index = (uu___492_15143.qtbl_name_and_index);
           normalized_eff_names = (uu___492_15143.normalized_eff_names);
           fv_delta_depths = (uu___492_15143.fv_delta_depths);
           proof_ns = (uu___492_15143.proof_ns);
           synth_hook = (uu___492_15143.synth_hook);
           splice = (uu___492_15143.splice);
           mpreprocess = (uu___492_15143.mpreprocess);
           postprocess = (uu___492_15143.postprocess);
           is_native_tactic = (uu___492_15143.is_native_tactic);
           identifier_info = (uu___492_15143.identifier_info);
           tc_hooks = (uu___492_15143.tc_hooks);
           dsenv = (uu___492_15143.dsenv);
           nbe = (uu___492_15143.nbe);
           strict_args_tab = (uu___492_15143.strict_args_tab);
           erasable_types_tab = (uu___492_15143.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15163 =
        let uu____15164 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15164 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15163
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15219 =
          let uu____15220 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15220 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15219
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15275 =
          let uu____15276 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15276 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15275
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15331 =
        let uu____15332 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15332 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15331
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___509_15396 = env  in
      {
        solver = (uu___509_15396.solver);
        range = (uu___509_15396.range);
        curmodule = lid;
        gamma = (uu___509_15396.gamma);
        gamma_sig = (uu___509_15396.gamma_sig);
        gamma_cache = (uu___509_15396.gamma_cache);
        modules = (uu___509_15396.modules);
        expected_typ = (uu___509_15396.expected_typ);
        sigtab = (uu___509_15396.sigtab);
        attrtab = (uu___509_15396.attrtab);
        instantiate_imp = (uu___509_15396.instantiate_imp);
        effects = (uu___509_15396.effects);
        generalize = (uu___509_15396.generalize);
        letrecs = (uu___509_15396.letrecs);
        top_level = (uu___509_15396.top_level);
        check_uvars = (uu___509_15396.check_uvars);
        use_eq = (uu___509_15396.use_eq);
        is_iface = (uu___509_15396.is_iface);
        admit = (uu___509_15396.admit);
        lax = (uu___509_15396.lax);
        lax_universes = (uu___509_15396.lax_universes);
        phase1 = (uu___509_15396.phase1);
        failhard = (uu___509_15396.failhard);
        nosynth = (uu___509_15396.nosynth);
        uvar_subtyping = (uu___509_15396.uvar_subtyping);
        tc_term = (uu___509_15396.tc_term);
        type_of = (uu___509_15396.type_of);
        universe_of = (uu___509_15396.universe_of);
        check_type_of = (uu___509_15396.check_type_of);
        use_bv_sorts = (uu___509_15396.use_bv_sorts);
        qtbl_name_and_index = (uu___509_15396.qtbl_name_and_index);
        normalized_eff_names = (uu___509_15396.normalized_eff_names);
        fv_delta_depths = (uu___509_15396.fv_delta_depths);
        proof_ns = (uu___509_15396.proof_ns);
        synth_hook = (uu___509_15396.synth_hook);
        splice = (uu___509_15396.splice);
        mpreprocess = (uu___509_15396.mpreprocess);
        postprocess = (uu___509_15396.postprocess);
        is_native_tactic = (uu___509_15396.is_native_tactic);
        identifier_info = (uu___509_15396.identifier_info);
        tc_hooks = (uu___509_15396.tc_hooks);
        dsenv = (uu___509_15396.dsenv);
        nbe = (uu___509_15396.nbe);
        strict_args_tab = (uu___509_15396.strict_args_tab);
        erasable_types_tab = (uu___509_15396.erasable_types_tab)
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
      let uu____15427 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15427
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15440 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15440)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15455 =
      let uu____15457 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15457  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15455)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15466  ->
    let uu____15467 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15467
  
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
      | ((formals,t),uu____15567) ->
          let vs = mk_univ_subst formals us  in
          let uu____15591 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15591)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15608  ->
    match uu___1_15608 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15634  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15654 = inst_tscheme t  in
      match uu____15654 with
      | (us,t1) ->
          let uu____15665 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15665)
  
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
          let uu____15690 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15692 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15690 uu____15692
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
        fun uu____15719  ->
          match uu____15719 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15733 =
                    let uu____15735 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15739 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15743 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15745 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15735 uu____15739 uu____15743 uu____15745
                     in
                  failwith uu____15733)
               else ();
               (let uu____15750 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15750))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15768 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15779 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15790 -> false
  
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
             | ([],uu____15838) -> Maybe
             | (uu____15845,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15865 -> No  in
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
          let uu____15959 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15959 with
          | FStar_Pervasives_Native.None  ->
              let uu____15982 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16026  ->
                     match uu___2_16026 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16065 = FStar_Ident.lid_equals lid l  in
                         if uu____16065
                         then
                           let uu____16088 =
                             let uu____16107 =
                               let uu____16122 = inst_tscheme t  in
                               FStar_Util.Inl uu____16122  in
                             let uu____16137 = FStar_Ident.range_of_lid l  in
                             (uu____16107, uu____16137)  in
                           FStar_Pervasives_Native.Some uu____16088
                         else FStar_Pervasives_Native.None
                     | uu____16190 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15982
                (fun uu____16228  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16238  ->
                        match uu___3_16238 with
                        | (uu____16241,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16243);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16244;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16245;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16246;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16247;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16248;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16270 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16270
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
                                  uu____16322 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16329 -> cache t  in
                            let uu____16330 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16330 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16336 =
                                   let uu____16337 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16337)
                                    in
                                 maybe_cache uu____16336)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16408 = find_in_sigtab env lid  in
         match uu____16408 with
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
      let uu____16489 = lookup_qname env lid  in
      match uu____16489 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16510,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16624 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16624 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16669 =
          let uu____16672 = lookup_attr env1 attr  in se1 :: uu____16672  in
        FStar_Util.smap_add (attrtab env1) attr uu____16669  in
      FStar_List.iter
        (fun attr  ->
           let uu____16682 =
             let uu____16683 = FStar_Syntax_Subst.compress attr  in
             uu____16683.FStar_Syntax_Syntax.n  in
           match uu____16682 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16687 =
                 let uu____16689 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16689.FStar_Ident.str  in
               add_one1 env se uu____16687
           | uu____16690 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16713) ->
          add_sigelts env ses
      | uu____16722 ->
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
        (fun uu___4_16760  ->
           match uu___4_16760 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16778 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16840,lb::[]),uu____16842) ->
            let uu____16851 =
              let uu____16860 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16869 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16860, uu____16869)  in
            FStar_Pervasives_Native.Some uu____16851
        | FStar_Syntax_Syntax.Sig_let ((uu____16882,lbs),uu____16884) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16916 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16929 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16929
                     then
                       let uu____16942 =
                         let uu____16951 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16960 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16951, uu____16960)  in
                       FStar_Pervasives_Native.Some uu____16942
                     else FStar_Pervasives_Native.None)
        | uu____16983 -> FStar_Pervasives_Native.None
  
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
                    let uu____17075 =
                      let uu____17077 =
                        let uu____17079 =
                          let uu____17081 =
                            let uu____17083 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17089 =
                              let uu____17091 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17091  in
                            Prims.op_Hat uu____17083 uu____17089  in
                          Prims.op_Hat ", expected " uu____17081  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17079
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17077
                       in
                    failwith uu____17075
                  else ());
             (let uu____17098 =
                let uu____17107 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17107, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17098))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17127,uu____17128) ->
            let uu____17133 =
              let uu____17142 =
                let uu____17147 =
                  let uu____17148 =
                    let uu____17151 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17151  in
                  (us, uu____17148)  in
                inst_ts us_opt uu____17147  in
              (uu____17142, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17133
        | uu____17170 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17259 =
          match uu____17259 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17355,uvs,t,uu____17358,uu____17359,uu____17360);
                      FStar_Syntax_Syntax.sigrng = uu____17361;
                      FStar_Syntax_Syntax.sigquals = uu____17362;
                      FStar_Syntax_Syntax.sigmeta = uu____17363;
                      FStar_Syntax_Syntax.sigattrs = uu____17364;
                      FStar_Syntax_Syntax.sigopts = uu____17365;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17390 =
                     let uu____17399 = inst_tscheme1 (uvs, t)  in
                     (uu____17399, rng)  in
                   FStar_Pervasives_Native.Some uu____17390
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17423;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17425;
                      FStar_Syntax_Syntax.sigattrs = uu____17426;
                      FStar_Syntax_Syntax.sigopts = uu____17427;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17446 =
                     let uu____17448 = in_cur_mod env l  in uu____17448 = Yes
                      in
                   if uu____17446
                   then
                     let uu____17460 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17460
                      then
                        let uu____17476 =
                          let uu____17485 = inst_tscheme1 (uvs, t)  in
                          (uu____17485, rng)  in
                        FStar_Pervasives_Native.Some uu____17476
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17518 =
                        let uu____17527 = inst_tscheme1 (uvs, t)  in
                        (uu____17527, rng)  in
                      FStar_Pervasives_Native.Some uu____17518)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17552,uu____17553);
                      FStar_Syntax_Syntax.sigrng = uu____17554;
                      FStar_Syntax_Syntax.sigquals = uu____17555;
                      FStar_Syntax_Syntax.sigmeta = uu____17556;
                      FStar_Syntax_Syntax.sigattrs = uu____17557;
                      FStar_Syntax_Syntax.sigopts = uu____17558;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17601 =
                          let uu____17610 = inst_tscheme1 (uvs, k)  in
                          (uu____17610, rng)  in
                        FStar_Pervasives_Native.Some uu____17601
                    | uu____17631 ->
                        let uu____17632 =
                          let uu____17641 =
                            let uu____17646 =
                              let uu____17647 =
                                let uu____17650 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17650
                                 in
                              (uvs, uu____17647)  in
                            inst_tscheme1 uu____17646  in
                          (uu____17641, rng)  in
                        FStar_Pervasives_Native.Some uu____17632)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17673,uu____17674);
                      FStar_Syntax_Syntax.sigrng = uu____17675;
                      FStar_Syntax_Syntax.sigquals = uu____17676;
                      FStar_Syntax_Syntax.sigmeta = uu____17677;
                      FStar_Syntax_Syntax.sigattrs = uu____17678;
                      FStar_Syntax_Syntax.sigopts = uu____17679;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17723 =
                          let uu____17732 = inst_tscheme_with (uvs, k) us  in
                          (uu____17732, rng)  in
                        FStar_Pervasives_Native.Some uu____17723
                    | uu____17753 ->
                        let uu____17754 =
                          let uu____17763 =
                            let uu____17768 =
                              let uu____17769 =
                                let uu____17772 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17772
                                 in
                              (uvs, uu____17769)  in
                            inst_tscheme_with uu____17768 us  in
                          (uu____17763, rng)  in
                        FStar_Pervasives_Native.Some uu____17754)
               | FStar_Util.Inr se ->
                   let uu____17808 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17829;
                          FStar_Syntax_Syntax.sigrng = uu____17830;
                          FStar_Syntax_Syntax.sigquals = uu____17831;
                          FStar_Syntax_Syntax.sigmeta = uu____17832;
                          FStar_Syntax_Syntax.sigattrs = uu____17833;
                          FStar_Syntax_Syntax.sigopts = uu____17834;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17851 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17808
                     (FStar_Util.map_option
                        (fun uu____17899  ->
                           match uu____17899 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17930 =
          let uu____17941 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17941 mapper  in
        match uu____17930 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18015 =
              let uu____18026 =
                let uu____18033 =
                  let uu___846_18036 = t  in
                  let uu____18037 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___846_18036.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18037;
                    FStar_Syntax_Syntax.vars =
                      (uu___846_18036.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18033)  in
              (uu____18026, r)  in
            FStar_Pervasives_Native.Some uu____18015
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18086 = lookup_qname env l  in
      match uu____18086 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18107 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18161 = try_lookup_bv env bv  in
      match uu____18161 with
      | FStar_Pervasives_Native.None  ->
          let uu____18176 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18176 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18192 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18193 =
            let uu____18194 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18194  in
          (uu____18192, uu____18193)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18216 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18216 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18282 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18282  in
          let uu____18283 =
            let uu____18292 =
              let uu____18297 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18297)  in
            (uu____18292, r1)  in
          FStar_Pervasives_Native.Some uu____18283
  
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
        let uu____18332 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18332 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18365,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18390 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18390  in
            let uu____18391 =
              let uu____18396 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18396, r1)  in
            FStar_Pervasives_Native.Some uu____18391
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18420 = try_lookup_lid env l  in
      match uu____18420 with
      | FStar_Pervasives_Native.None  ->
          let uu____18447 = name_not_found l  in
          let uu____18453 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18447 uu____18453
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18496  ->
              match uu___5_18496 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18500 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18521 = lookup_qname env lid  in
      match uu____18521 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18530,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18533;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18535;
              FStar_Syntax_Syntax.sigattrs = uu____18536;
              FStar_Syntax_Syntax.sigopts = uu____18537;_},FStar_Pervasives_Native.None
            ),uu____18538)
          ->
          let uu____18589 =
            let uu____18596 =
              let uu____18597 =
                let uu____18600 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18600 t  in
              (uvs, uu____18597)  in
            (uu____18596, q)  in
          FStar_Pervasives_Native.Some uu____18589
      | uu____18613 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18635 = lookup_qname env lid  in
      match uu____18635 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18640,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18643;
              FStar_Syntax_Syntax.sigquals = uu____18644;
              FStar_Syntax_Syntax.sigmeta = uu____18645;
              FStar_Syntax_Syntax.sigattrs = uu____18646;
              FStar_Syntax_Syntax.sigopts = uu____18647;_},FStar_Pervasives_Native.None
            ),uu____18648)
          ->
          let uu____18699 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18699 (uvs, t)
      | uu____18704 ->
          let uu____18705 = name_not_found lid  in
          let uu____18711 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18705 uu____18711
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18731 = lookup_qname env lid  in
      match uu____18731 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18736,uvs,t,uu____18739,uu____18740,uu____18741);
              FStar_Syntax_Syntax.sigrng = uu____18742;
              FStar_Syntax_Syntax.sigquals = uu____18743;
              FStar_Syntax_Syntax.sigmeta = uu____18744;
              FStar_Syntax_Syntax.sigattrs = uu____18745;
              FStar_Syntax_Syntax.sigopts = uu____18746;_},FStar_Pervasives_Native.None
            ),uu____18747)
          ->
          let uu____18804 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18804 (uvs, t)
      | uu____18809 ->
          let uu____18810 = name_not_found lid  in
          let uu____18816 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18810 uu____18816
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18839 = lookup_qname env lid  in
      match uu____18839 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18847,uu____18848,uu____18849,uu____18850,uu____18851,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18853;
              FStar_Syntax_Syntax.sigquals = uu____18854;
              FStar_Syntax_Syntax.sigmeta = uu____18855;
              FStar_Syntax_Syntax.sigattrs = uu____18856;
              FStar_Syntax_Syntax.sigopts = uu____18857;_},uu____18858),uu____18859)
          -> (true, dcs)
      | uu____18924 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18940 = lookup_qname env lid  in
      match uu____18940 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18941,uu____18942,uu____18943,l,uu____18945,uu____18946);
              FStar_Syntax_Syntax.sigrng = uu____18947;
              FStar_Syntax_Syntax.sigquals = uu____18948;
              FStar_Syntax_Syntax.sigmeta = uu____18949;
              FStar_Syntax_Syntax.sigattrs = uu____18950;
              FStar_Syntax_Syntax.sigopts = uu____18951;_},uu____18952),uu____18953)
          -> l
      | uu____19012 ->
          let uu____19013 =
            let uu____19015 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19015  in
          failwith uu____19013
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19085)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19142) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19166 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19166
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19201 -> FStar_Pervasives_Native.None)
          | uu____19210 -> FStar_Pervasives_Native.None
  
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
        let uu____19272 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19272
  
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
        let uu____19305 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19305
  
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
             (FStar_Util.Inl uu____19357,uu____19358) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19407),uu____19408) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19457 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19475 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19485 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19502 ->
                  let uu____19509 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19509
              | FStar_Syntax_Syntax.Sig_let ((uu____19510,lbs),uu____19512)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19528 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19528
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19535 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19543 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19544 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19551 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19552 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19553 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19566 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19584 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19584
           (fun d_opt  ->
              let uu____19597 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19597
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19607 =
                   let uu____19610 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19610  in
                 match uu____19607 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19611 =
                       let uu____19613 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19613
                        in
                     failwith uu____19611
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19618 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19618
                       then
                         let uu____19621 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19623 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19625 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19621 uu____19623 uu____19625
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
        (FStar_Util.Inr (se,uu____19650),uu____19651) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19700 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19722),uu____19723) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19772 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19794 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19794
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19827 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19827 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19849 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19858 =
                        let uu____19859 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19859.FStar_Syntax_Syntax.n  in
                      match uu____19858 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19864 -> false))
               in
            (true, uu____19849)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19887 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19887
  
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
          let uu____19959 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19959.FStar_Ident.str  in
        let uu____19960 = FStar_Util.smap_try_find tab s  in
        match uu____19960 with
        | FStar_Pervasives_Native.None  ->
            let uu____19963 = f ()  in
            (match uu____19963 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20001 =
        let uu____20002 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20002 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20036 =
        let uu____20037 = FStar_Syntax_Util.unrefine t  in
        uu____20037.FStar_Syntax_Syntax.n  in
      match uu____20036 with
      | FStar_Syntax_Syntax.Tm_type uu____20041 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20045) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20071) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20076,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20098 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20131 =
        let attrs =
          let uu____20137 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20137  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20177 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20177)
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
      let uu____20222 = lookup_qname env ftv  in
      match uu____20222 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20226) ->
          let uu____20271 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20271 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20292,t),r) ->
               let uu____20307 =
                 let uu____20308 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20308 t  in
               FStar_Pervasives_Native.Some uu____20307)
      | uu____20309 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20321 = try_lookup_effect_lid env ftv  in
      match uu____20321 with
      | FStar_Pervasives_Native.None  ->
          let uu____20324 = name_not_found ftv  in
          let uu____20330 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20324 uu____20330
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
        let uu____20354 = lookup_qname env lid0  in
        match uu____20354 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20365);
                FStar_Syntax_Syntax.sigrng = uu____20366;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20368;
                FStar_Syntax_Syntax.sigattrs = uu____20369;
                FStar_Syntax_Syntax.sigopts = uu____20370;_},FStar_Pervasives_Native.None
              ),uu____20371)
            ->
            let lid1 =
              let uu____20427 =
                let uu____20428 = FStar_Ident.range_of_lid lid  in
                let uu____20429 =
                  let uu____20430 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20430  in
                FStar_Range.set_use_range uu____20428 uu____20429  in
              FStar_Ident.set_lid_range lid uu____20427  in
            let uu____20431 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20437  ->
                      match uu___6_20437 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20440 -> false))
               in
            if uu____20431
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20459 =
                      let uu____20461 =
                        let uu____20463 = get_range env  in
                        FStar_Range.string_of_range uu____20463  in
                      let uu____20464 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20466 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20461 uu____20464 uu____20466
                       in
                    failwith uu____20459)
                  in
               match (binders, univs1) with
               | ([],uu____20487) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20513,uu____20514::uu____20515::uu____20516) ->
                   let uu____20537 =
                     let uu____20539 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20541 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20539 uu____20541
                      in
                   failwith uu____20537
               | uu____20552 ->
                   let uu____20567 =
                     let uu____20572 =
                       let uu____20573 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20573)  in
                     inst_tscheme_with uu____20572 insts  in
                   (match uu____20567 with
                    | (uu____20586,t) ->
                        let t1 =
                          let uu____20589 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20589 t  in
                        let uu____20590 =
                          let uu____20591 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20591.FStar_Syntax_Syntax.n  in
                        (match uu____20590 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20626 -> failwith "Impossible")))
        | uu____20634 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20658 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20658 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20671,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20678 = find1 l2  in
            (match uu____20678 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20685 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20685 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20689 = find1 l  in
            (match uu____20689 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20694 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20694
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____20715 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____20715 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____20721) ->
            FStar_List.length bs
        | uu____20760 ->
            let uu____20761 =
              let uu____20767 =
                let uu____20769 = FStar_Ident.string_of_lid name  in
                let uu____20771 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____20769 uu____20771
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____20767)
               in
            FStar_Errors.raise_error uu____20761 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20790 = lookup_qname env l1  in
      match uu____20790 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20793;
              FStar_Syntax_Syntax.sigrng = uu____20794;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20796;
              FStar_Syntax_Syntax.sigattrs = uu____20797;
              FStar_Syntax_Syntax.sigopts = uu____20798;_},uu____20799),uu____20800)
          -> q
      | uu____20853 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20877 =
          let uu____20878 =
            let uu____20880 = FStar_Util.string_of_int i  in
            let uu____20882 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20880 uu____20882
             in
          failwith uu____20878  in
        let uu____20885 = lookup_datacon env lid  in
        match uu____20885 with
        | (uu____20890,t) ->
            let uu____20892 =
              let uu____20893 = FStar_Syntax_Subst.compress t  in
              uu____20893.FStar_Syntax_Syntax.n  in
            (match uu____20892 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20897) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20941 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20941
                      FStar_Pervasives_Native.fst)
             | uu____20952 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20966 = lookup_qname env l  in
      match uu____20966 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20968,uu____20969,uu____20970);
              FStar_Syntax_Syntax.sigrng = uu____20971;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20973;
              FStar_Syntax_Syntax.sigattrs = uu____20974;
              FStar_Syntax_Syntax.sigopts = uu____20975;_},uu____20976),uu____20977)
          ->
          FStar_Util.for_some
            (fun uu___7_21032  ->
               match uu___7_21032 with
               | FStar_Syntax_Syntax.Projector uu____21034 -> true
               | uu____21040 -> false) quals
      | uu____21042 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21056 = lookup_qname env lid  in
      match uu____21056 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21058,uu____21059,uu____21060,uu____21061,uu____21062,uu____21063);
              FStar_Syntax_Syntax.sigrng = uu____21064;
              FStar_Syntax_Syntax.sigquals = uu____21065;
              FStar_Syntax_Syntax.sigmeta = uu____21066;
              FStar_Syntax_Syntax.sigattrs = uu____21067;
              FStar_Syntax_Syntax.sigopts = uu____21068;_},uu____21069),uu____21070)
          -> true
      | uu____21130 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21144 = lookup_qname env lid  in
      match uu____21144 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21146,uu____21147,uu____21148,uu____21149,uu____21150,uu____21151);
              FStar_Syntax_Syntax.sigrng = uu____21152;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21154;
              FStar_Syntax_Syntax.sigattrs = uu____21155;
              FStar_Syntax_Syntax.sigopts = uu____21156;_},uu____21157),uu____21158)
          ->
          FStar_Util.for_some
            (fun uu___8_21221  ->
               match uu___8_21221 with
               | FStar_Syntax_Syntax.RecordType uu____21223 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21233 -> true
               | uu____21243 -> false) quals
      | uu____21245 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21255,uu____21256);
            FStar_Syntax_Syntax.sigrng = uu____21257;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21259;
            FStar_Syntax_Syntax.sigattrs = uu____21260;
            FStar_Syntax_Syntax.sigopts = uu____21261;_},uu____21262),uu____21263)
        ->
        FStar_Util.for_some
          (fun uu___9_21322  ->
             match uu___9_21322 with
             | FStar_Syntax_Syntax.Action uu____21324 -> true
             | uu____21326 -> false) quals
    | uu____21328 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21342 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21342
  
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
      let uu____21359 =
        let uu____21360 = FStar_Syntax_Util.un_uinst head1  in
        uu____21360.FStar_Syntax_Syntax.n  in
      match uu____21359 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21366 ->
               true
           | uu____21369 -> false)
      | uu____21371 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21385 = lookup_qname env l  in
      match uu____21385 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21388),uu____21389) ->
          FStar_Util.for_some
            (fun uu___10_21437  ->
               match uu___10_21437 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21440 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21442 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21518 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21536) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21554 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21562 ->
                 FStar_Pervasives_Native.Some true
             | uu____21581 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21584 =
        let uu____21588 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21588 mapper  in
      match uu____21584 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21648 = lookup_qname env lid  in
      match uu____21648 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21652,uu____21653,tps,uu____21655,uu____21656,uu____21657);
              FStar_Syntax_Syntax.sigrng = uu____21658;
              FStar_Syntax_Syntax.sigquals = uu____21659;
              FStar_Syntax_Syntax.sigmeta = uu____21660;
              FStar_Syntax_Syntax.sigattrs = uu____21661;
              FStar_Syntax_Syntax.sigopts = uu____21662;_},uu____21663),uu____21664)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21732 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21778  ->
              match uu____21778 with
              | (d,uu____21787) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21803 = effect_decl_opt env l  in
      match uu____21803 with
      | FStar_Pervasives_Native.None  ->
          let uu____21818 = name_not_found l  in
          let uu____21824 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21818 uu____21824
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21852 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____21852 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____21859  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21873  ->
            fun uu____21874  -> fun e  -> FStar_Util.return_all e))
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
        let uu____21900 = FStar_Ident.lid_equals l1 l2  in
        if uu____21900
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____21919 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21919
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____21938 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21991  ->
                        match uu____21991 with
                        | (m1,m2,uu____22005,uu____22006,uu____22007) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21938 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____22032,uu____22033,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22081 = join_opt env l1 l2  in
        match uu____22081 with
        | FStar_Pervasives_Native.None  ->
            let uu____22102 =
              let uu____22108 =
                let uu____22110 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____22112 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____22110 uu____22112
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22108)  in
            FStar_Errors.raise_error uu____22102 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22155 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22155
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
  'Auu____22175 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22175) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22204 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22230  ->
                match uu____22230 with
                | (d,uu____22237) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22204 with
      | FStar_Pervasives_Native.None  ->
          let uu____22248 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22248
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22263 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22263 with
           | (uu____22274,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22292)::(wp,uu____22294)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22350 -> failwith "Impossible"))
  
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
        | uu____22415 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let (unfold_effect_abbrev_one_step :
  env -> FStar_Syntax_Syntax.comp -> (FStar_Syntax_Syntax.comp * Prims.bool))
  =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22433 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22433 with
      | FStar_Pervasives_Native.None  ->
          let uu____22449 =
            FStar_All.pipe_right c FStar_Syntax_Syntax.mk_Comp  in
          (uu____22449, false)
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22458 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22458 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22488 =
                     let uu____22494 =
                       let uu____22496 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22504 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22515 =
                         let uu____22517 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22517  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22496 uu____22504 uu____22515
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22494)
                      in
                   FStar_Errors.raise_error uu____22488
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22525 =
                     let uu____22536 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22536 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22573  ->
                        fun uu____22574  ->
                          match (uu____22573, uu____22574) with
                          | ((x,uu____22604),(t,uu____22606)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22525
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let uu____22636 =
                   let uu____22637 =
                     let uu___1598_22638 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1598_22638.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1598_22638.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1598_22638.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1598_22638.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22637
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 (uu____22636, true))))
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let uu____22652 = unfold_effect_abbrev_one_step env comp  in
      match uu____22652 with
      | (c,b) ->
          if b then unfold_effect_abbrev env c else comp_to_comp_typ env c
  
let effect_repr_aux :
  'Auu____22676 .
    'Auu____22676 ->
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
            let uu____22717 =
              let uu____22724 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____22724)  in
            match uu____22717 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____22748 = FStar_Ident.string_of_lid eff_name  in
                     let uu____22750 = FStar_Util.string_of_int given  in
                     let uu____22752 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____22748 uu____22750 uu____22752
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____22757 = effect_decl_opt env effect_name  in
          match uu____22757 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____22779) ->
              let uu____22790 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____22790 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____22808 =
                       let uu____22811 = get_range env  in
                       let uu____22812 =
                         let uu____22819 =
                           let uu____22820 =
                             let uu____22837 =
                               let uu____22848 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____22848 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____22837)  in
                           FStar_Syntax_Syntax.Tm_app uu____22820  in
                         FStar_Syntax_Syntax.mk uu____22819  in
                       uu____22812 FStar_Pervasives_Native.None uu____22811
                        in
                     FStar_Pervasives_Native.Some uu____22808)))
  
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
           (fun uu___11_22948  ->
              match uu___11_22948 with
              | FStar_Syntax_Syntax.Reflectable uu____22950 -> true
              | uu____22952 -> false))
  
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
      | uu____23012 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23027 =
        let uu____23028 = FStar_Syntax_Subst.compress t  in
        uu____23028.FStar_Syntax_Syntax.n  in
      match uu____23027 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23032,c) ->
          is_reifiable_comp env c
      | uu____23054 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23074 =
           let uu____23076 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23076  in
         if uu____23074
         then
           let uu____23079 =
             let uu____23085 =
               let uu____23087 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23087
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23085)  in
           let uu____23091 = get_range env  in
           FStar_Errors.raise_error uu____23079 uu____23091
         else ());
        (let uu____23094 = effect_repr_aux true env c u_c  in
         match uu____23094 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1680_23130 = env  in
        {
          solver = (uu___1680_23130.solver);
          range = (uu___1680_23130.range);
          curmodule = (uu___1680_23130.curmodule);
          gamma = (uu___1680_23130.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1680_23130.gamma_cache);
          modules = (uu___1680_23130.modules);
          expected_typ = (uu___1680_23130.expected_typ);
          sigtab = (uu___1680_23130.sigtab);
          attrtab = (uu___1680_23130.attrtab);
          instantiate_imp = (uu___1680_23130.instantiate_imp);
          effects = (uu___1680_23130.effects);
          generalize = (uu___1680_23130.generalize);
          letrecs = (uu___1680_23130.letrecs);
          top_level = (uu___1680_23130.top_level);
          check_uvars = (uu___1680_23130.check_uvars);
          use_eq = (uu___1680_23130.use_eq);
          is_iface = (uu___1680_23130.is_iface);
          admit = (uu___1680_23130.admit);
          lax = (uu___1680_23130.lax);
          lax_universes = (uu___1680_23130.lax_universes);
          phase1 = (uu___1680_23130.phase1);
          failhard = (uu___1680_23130.failhard);
          nosynth = (uu___1680_23130.nosynth);
          uvar_subtyping = (uu___1680_23130.uvar_subtyping);
          tc_term = (uu___1680_23130.tc_term);
          type_of = (uu___1680_23130.type_of);
          universe_of = (uu___1680_23130.universe_of);
          check_type_of = (uu___1680_23130.check_type_of);
          use_bv_sorts = (uu___1680_23130.use_bv_sorts);
          qtbl_name_and_index = (uu___1680_23130.qtbl_name_and_index);
          normalized_eff_names = (uu___1680_23130.normalized_eff_names);
          fv_delta_depths = (uu___1680_23130.fv_delta_depths);
          proof_ns = (uu___1680_23130.proof_ns);
          synth_hook = (uu___1680_23130.synth_hook);
          splice = (uu___1680_23130.splice);
          mpreprocess = (uu___1680_23130.mpreprocess);
          postprocess = (uu___1680_23130.postprocess);
          is_native_tactic = (uu___1680_23130.is_native_tactic);
          identifier_info = (uu___1680_23130.identifier_info);
          tc_hooks = (uu___1680_23130.tc_hooks);
          dsenv = (uu___1680_23130.dsenv);
          nbe = (uu___1680_23130.nbe);
          strict_args_tab = (uu___1680_23130.strict_args_tab);
          erasable_types_tab = (uu___1680_23130.erasable_types_tab)
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
    fun uu____23149  ->
      match uu____23149 with
      | (ed,quals) ->
          let effects =
            let uu___1689_23163 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              abbrevs = (uu___1689_23163.abbrevs);
              order = (uu___1689_23163.order);
              joins = (uu___1689_23163.joins)
            }  in
          let uu___1692_23172 = env  in
          {
            solver = (uu___1692_23172.solver);
            range = (uu___1692_23172.range);
            curmodule = (uu___1692_23172.curmodule);
            gamma = (uu___1692_23172.gamma);
            gamma_sig = (uu___1692_23172.gamma_sig);
            gamma_cache = (uu___1692_23172.gamma_cache);
            modules = (uu___1692_23172.modules);
            expected_typ = (uu___1692_23172.expected_typ);
            sigtab = (uu___1692_23172.sigtab);
            attrtab = (uu___1692_23172.attrtab);
            instantiate_imp = (uu___1692_23172.instantiate_imp);
            effects;
            generalize = (uu___1692_23172.generalize);
            letrecs = (uu___1692_23172.letrecs);
            top_level = (uu___1692_23172.top_level);
            check_uvars = (uu___1692_23172.check_uvars);
            use_eq = (uu___1692_23172.use_eq);
            is_iface = (uu___1692_23172.is_iface);
            admit = (uu___1692_23172.admit);
            lax = (uu___1692_23172.lax);
            lax_universes = (uu___1692_23172.lax_universes);
            phase1 = (uu___1692_23172.phase1);
            failhard = (uu___1692_23172.failhard);
            nosynth = (uu___1692_23172.nosynth);
            uvar_subtyping = (uu___1692_23172.uvar_subtyping);
            tc_term = (uu___1692_23172.tc_term);
            type_of = (uu___1692_23172.type_of);
            universe_of = (uu___1692_23172.universe_of);
            check_type_of = (uu___1692_23172.check_type_of);
            use_bv_sorts = (uu___1692_23172.use_bv_sorts);
            qtbl_name_and_index = (uu___1692_23172.qtbl_name_and_index);
            normalized_eff_names = (uu___1692_23172.normalized_eff_names);
            fv_delta_depths = (uu___1692_23172.fv_delta_depths);
            proof_ns = (uu___1692_23172.proof_ns);
            synth_hook = (uu___1692_23172.synth_hook);
            splice = (uu___1692_23172.splice);
            mpreprocess = (uu___1692_23172.mpreprocess);
            postprocess = (uu___1692_23172.postprocess);
            is_native_tactic = (uu___1692_23172.is_native_tactic);
            identifier_info = (uu___1692_23172.identifier_info);
            tc_hooks = (uu___1692_23172.tc_hooks);
            dsenv = (uu___1692_23172.dsenv);
            nbe = (uu___1692_23172.nbe);
            strict_args_tab = (uu___1692_23172.strict_args_tab);
            erasable_types_tab = (uu___1692_23172.erasable_types_tab)
          }
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          (let uu____23195 = FStar_Ident.string_of_lid src  in
           let uu____23197 = FStar_Ident.string_of_lid tgt  in
           FStar_Util.print2
             "Updating effect lattice with an edge %s ~~> %s\n\n" uu____23195
             uu____23197);
          (let compose_edges e1 e2 =
             let composed_lift =
               let mlift_wp env1 c =
                 let uu____23227 =
                   FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                 FStar_All.pipe_right uu____23227
                   (fun uu____23248  ->
                      match uu____23248 with
                      | (c1,g1) ->
                          let uu____23259 =
                            FStar_All.pipe_right c1
                              ((e2.mlift).mlift_wp env1)
                             in
                          FStar_All.pipe_right uu____23259
                            (fun uu____23280  ->
                               match uu____23280 with
                               | (c2,g2) ->
                                   let uu____23291 =
                                     FStar_TypeChecker_Common.conj_guard g1
                                       g2
                                      in
                                   (c2, uu____23291)))
                  in
               let mlift_term =
                 match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term))
                 with
                 | (FStar_Pervasives_Native.Some
                    l1,FStar_Pervasives_Native.Some l2) ->
                     FStar_Pervasives_Native.Some
                       ((fun u  ->
                           fun t  ->
                             fun e  ->
                               let uu____23413 = l1 u t e  in
                               l2 u t uu____23413))
                 | uu____23414 -> FStar_Pervasives_Native.None  in
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
             let uu____23463 =
               FStar_All.pipe_right (env.effects).decls
                 (FStar_List.map
                    (fun uu____23485  ->
                       match uu____23485 with
                       | (e,uu____23493) -> e.FStar_Syntax_Syntax.mname))
                in
             FStar_List.append uu____23463 (env.effects).abbrevs  in
           let find_edge order1 uu____23516 =
             match uu____23516 with
             | (i,j) ->
                 let uu____23527 = FStar_Ident.lid_equals i j  in
                 if uu____23527
                 then
                   FStar_All.pipe_right (id_edge i)
                     (fun _23534  -> FStar_Pervasives_Native.Some _23534)
                 else
                   FStar_All.pipe_right order1
                     (FStar_Util.find_opt
                        (fun e  ->
                           (FStar_Ident.lid_equals e.msource i) &&
                             (FStar_Ident.lid_equals e.mtarget j)))
              in
           let order1 =
             let fold_fun order1 k =
               let uu____23563 =
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun i  ->
                         let uu____23573 = FStar_Ident.lid_equals i k  in
                         if uu____23573
                         then []
                         else
                           FStar_All.pipe_right ms
                             (FStar_List.collect
                                (fun j  ->
                                   let uu____23587 =
                                     FStar_Ident.lid_equals j k  in
                                   if uu____23587
                                   then []
                                   else
                                     (let uu____23594 =
                                        let uu____23603 =
                                          find_edge order1 (i, k)  in
                                        let uu____23606 =
                                          find_edge order1 (k, j)  in
                                        (uu____23603, uu____23606)  in
                                      match uu____23594 with
                                      | (FStar_Pervasives_Native.Some
                                         e1,FStar_Pervasives_Native.Some e2)
                                          ->
                                          let uu____23621 =
                                            compose_edges e1 e2  in
                                          [uu____23621]
                                      | uu____23622 -> [])))))
                  in
               FStar_List.append order1 uu____23563  in
             FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)
              in
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
                   let uu____23652 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____23655 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____23655
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____23652
                   then
                     let uu____23662 =
                       let uu____23668 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____23668)
                        in
                     let uu____23672 = get_range env  in
                     FStar_Errors.raise_error uu____23662 uu____23672
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt1 =
                                let uu____23750 = FStar_Ident.lid_equals i j
                                   in
                                if uu____23750
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____23802 =
                                              let uu____23811 =
                                                find_edge order2 (i, k)  in
                                              let uu____23814 =
                                                find_edge order2 (j, k)  in
                                              (uu____23811, uu____23814)  in
                                            match uu____23802 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____23856,uu____23857)
                                                     ->
                                                     let uu____23864 =
                                                       let uu____23871 =
                                                         let uu____23873 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____23873
                                                          in
                                                       let uu____23876 =
                                                         let uu____23878 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____23878
                                                          in
                                                       (uu____23871,
                                                         uu____23876)
                                                        in
                                                     (match uu____23864 with
                                                      | (true ,true ) ->
                                                          let uu____23895 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____23895
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
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____23938 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt1 with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1798_24011 = env.effects  in
              {
                decls = (uu___1798_24011.decls);
                abbrevs = (uu___1798_24011.abbrevs);
                order = order2;
                joins
              }  in
            FStar_All.pipe_right joins
              (FStar_List.iter
                 (fun uu____24041  ->
                    match uu____24041 with
                    | (e1,e2,e3,l1,l2) ->
                        FStar_Util.print3 "%s join %s = %s\n\n"
                          e1.FStar_Ident.str e2.FStar_Ident.str
                          e3.FStar_Ident.str));
            (let uu___1808_24058 = env  in
             {
               solver = (uu___1808_24058.solver);
               range = (uu___1808_24058.range);
               curmodule = (uu___1808_24058.curmodule);
               gamma = (uu___1808_24058.gamma);
               gamma_sig = (uu___1808_24058.gamma_sig);
               gamma_cache = (uu___1808_24058.gamma_cache);
               modules = (uu___1808_24058.modules);
               expected_typ = (uu___1808_24058.expected_typ);
               sigtab = (uu___1808_24058.sigtab);
               attrtab = (uu___1808_24058.attrtab);
               instantiate_imp = (uu___1808_24058.instantiate_imp);
               effects;
               generalize = (uu___1808_24058.generalize);
               letrecs = (uu___1808_24058.letrecs);
               top_level = (uu___1808_24058.top_level);
               check_uvars = (uu___1808_24058.check_uvars);
               use_eq = (uu___1808_24058.use_eq);
               is_iface = (uu___1808_24058.is_iface);
               admit = (uu___1808_24058.admit);
               lax = (uu___1808_24058.lax);
               lax_universes = (uu___1808_24058.lax_universes);
               phase1 = (uu___1808_24058.phase1);
               failhard = (uu___1808_24058.failhard);
               nosynth = (uu___1808_24058.nosynth);
               uvar_subtyping = (uu___1808_24058.uvar_subtyping);
               tc_term = (uu___1808_24058.tc_term);
               type_of = (uu___1808_24058.type_of);
               universe_of = (uu___1808_24058.universe_of);
               check_type_of = (uu___1808_24058.check_type_of);
               use_bv_sorts = (uu___1808_24058.use_bv_sorts);
               qtbl_name_and_index = (uu___1808_24058.qtbl_name_and_index);
               normalized_eff_names = (uu___1808_24058.normalized_eff_names);
               fv_delta_depths = (uu___1808_24058.fv_delta_depths);
               proof_ns = (uu___1808_24058.proof_ns);
               synth_hook = (uu___1808_24058.synth_hook);
               splice = (uu___1808_24058.splice);
               mpreprocess = (uu___1808_24058.mpreprocess);
               postprocess = (uu___1808_24058.postprocess);
               is_native_tactic = (uu___1808_24058.is_native_tactic);
               identifier_info = (uu___1808_24058.identifier_info);
               tc_hooks = (uu___1808_24058.tc_hooks);
               dsenv = (uu___1808_24058.dsenv);
               nbe = (uu___1808_24058.nbe);
               strict_args_tab = (uu___1808_24058.strict_args_tab);
               erasable_types_tab = (uu___1808_24058.erasable_types_tab)
             })))
  
let (push_new_effect_abbrev : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun l  ->
      let effects =
        let uu___1812_24071 = env.effects  in
        {
          decls = (uu___1812_24071.decls);
          abbrevs = (FStar_List.append (env.effects).abbrevs [l]);
          order = (uu___1812_24071.order);
          joins = (uu___1812_24071.joins)
        }  in
      let uu___1815_24072 = env  in
      {
        solver = (uu___1815_24072.solver);
        range = (uu___1815_24072.range);
        curmodule = (uu___1815_24072.curmodule);
        gamma = (uu___1815_24072.gamma);
        gamma_sig = (uu___1815_24072.gamma_sig);
        gamma_cache = (uu___1815_24072.gamma_cache);
        modules = (uu___1815_24072.modules);
        expected_typ = (uu___1815_24072.expected_typ);
        sigtab = (uu___1815_24072.sigtab);
        attrtab = (uu___1815_24072.attrtab);
        instantiate_imp = (uu___1815_24072.instantiate_imp);
        effects;
        generalize = (uu___1815_24072.generalize);
        letrecs = (uu___1815_24072.letrecs);
        top_level = (uu___1815_24072.top_level);
        check_uvars = (uu___1815_24072.check_uvars);
        use_eq = (uu___1815_24072.use_eq);
        is_iface = (uu___1815_24072.is_iface);
        admit = (uu___1815_24072.admit);
        lax = (uu___1815_24072.lax);
        lax_universes = (uu___1815_24072.lax_universes);
        phase1 = (uu___1815_24072.phase1);
        failhard = (uu___1815_24072.failhard);
        nosynth = (uu___1815_24072.nosynth);
        uvar_subtyping = (uu___1815_24072.uvar_subtyping);
        tc_term = (uu___1815_24072.tc_term);
        type_of = (uu___1815_24072.type_of);
        universe_of = (uu___1815_24072.universe_of);
        check_type_of = (uu___1815_24072.check_type_of);
        use_bv_sorts = (uu___1815_24072.use_bv_sorts);
        qtbl_name_and_index = (uu___1815_24072.qtbl_name_and_index);
        normalized_eff_names = (uu___1815_24072.normalized_eff_names);
        fv_delta_depths = (uu___1815_24072.fv_delta_depths);
        proof_ns = (uu___1815_24072.proof_ns);
        synth_hook = (uu___1815_24072.synth_hook);
        splice = (uu___1815_24072.splice);
        mpreprocess = (uu___1815_24072.mpreprocess);
        postprocess = (uu___1815_24072.postprocess);
        is_native_tactic = (uu___1815_24072.is_native_tactic);
        identifier_info = (uu___1815_24072.identifier_info);
        tc_hooks = (uu___1815_24072.tc_hooks);
        dsenv = (uu___1815_24072.dsenv);
        nbe = (uu___1815_24072.nbe);
        strict_args_tab = (uu___1815_24072.strict_args_tab);
        erasable_types_tab = (uu___1815_24072.erasable_types_tab)
      }
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1819_24084 = env  in
      {
        solver = (uu___1819_24084.solver);
        range = (uu___1819_24084.range);
        curmodule = (uu___1819_24084.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1819_24084.gamma_sig);
        gamma_cache = (uu___1819_24084.gamma_cache);
        modules = (uu___1819_24084.modules);
        expected_typ = (uu___1819_24084.expected_typ);
        sigtab = (uu___1819_24084.sigtab);
        attrtab = (uu___1819_24084.attrtab);
        instantiate_imp = (uu___1819_24084.instantiate_imp);
        effects = (uu___1819_24084.effects);
        generalize = (uu___1819_24084.generalize);
        letrecs = (uu___1819_24084.letrecs);
        top_level = (uu___1819_24084.top_level);
        check_uvars = (uu___1819_24084.check_uvars);
        use_eq = (uu___1819_24084.use_eq);
        is_iface = (uu___1819_24084.is_iface);
        admit = (uu___1819_24084.admit);
        lax = (uu___1819_24084.lax);
        lax_universes = (uu___1819_24084.lax_universes);
        phase1 = (uu___1819_24084.phase1);
        failhard = (uu___1819_24084.failhard);
        nosynth = (uu___1819_24084.nosynth);
        uvar_subtyping = (uu___1819_24084.uvar_subtyping);
        tc_term = (uu___1819_24084.tc_term);
        type_of = (uu___1819_24084.type_of);
        universe_of = (uu___1819_24084.universe_of);
        check_type_of = (uu___1819_24084.check_type_of);
        use_bv_sorts = (uu___1819_24084.use_bv_sorts);
        qtbl_name_and_index = (uu___1819_24084.qtbl_name_and_index);
        normalized_eff_names = (uu___1819_24084.normalized_eff_names);
        fv_delta_depths = (uu___1819_24084.fv_delta_depths);
        proof_ns = (uu___1819_24084.proof_ns);
        synth_hook = (uu___1819_24084.synth_hook);
        splice = (uu___1819_24084.splice);
        mpreprocess = (uu___1819_24084.mpreprocess);
        postprocess = (uu___1819_24084.postprocess);
        is_native_tactic = (uu___1819_24084.is_native_tactic);
        identifier_info = (uu___1819_24084.identifier_info);
        tc_hooks = (uu___1819_24084.tc_hooks);
        dsenv = (uu___1819_24084.dsenv);
        nbe = (uu___1819_24084.nbe);
        strict_args_tab = (uu___1819_24084.strict_args_tab);
        erasable_types_tab = (uu___1819_24084.erasable_types_tab)
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
            (let uu___1832_24142 = env  in
             {
               solver = (uu___1832_24142.solver);
               range = (uu___1832_24142.range);
               curmodule = (uu___1832_24142.curmodule);
               gamma = rest;
               gamma_sig = (uu___1832_24142.gamma_sig);
               gamma_cache = (uu___1832_24142.gamma_cache);
               modules = (uu___1832_24142.modules);
               expected_typ = (uu___1832_24142.expected_typ);
               sigtab = (uu___1832_24142.sigtab);
               attrtab = (uu___1832_24142.attrtab);
               instantiate_imp = (uu___1832_24142.instantiate_imp);
               effects = (uu___1832_24142.effects);
               generalize = (uu___1832_24142.generalize);
               letrecs = (uu___1832_24142.letrecs);
               top_level = (uu___1832_24142.top_level);
               check_uvars = (uu___1832_24142.check_uvars);
               use_eq = (uu___1832_24142.use_eq);
               is_iface = (uu___1832_24142.is_iface);
               admit = (uu___1832_24142.admit);
               lax = (uu___1832_24142.lax);
               lax_universes = (uu___1832_24142.lax_universes);
               phase1 = (uu___1832_24142.phase1);
               failhard = (uu___1832_24142.failhard);
               nosynth = (uu___1832_24142.nosynth);
               uvar_subtyping = (uu___1832_24142.uvar_subtyping);
               tc_term = (uu___1832_24142.tc_term);
               type_of = (uu___1832_24142.type_of);
               universe_of = (uu___1832_24142.universe_of);
               check_type_of = (uu___1832_24142.check_type_of);
               use_bv_sorts = (uu___1832_24142.use_bv_sorts);
               qtbl_name_and_index = (uu___1832_24142.qtbl_name_and_index);
               normalized_eff_names = (uu___1832_24142.normalized_eff_names);
               fv_delta_depths = (uu___1832_24142.fv_delta_depths);
               proof_ns = (uu___1832_24142.proof_ns);
               synth_hook = (uu___1832_24142.synth_hook);
               splice = (uu___1832_24142.splice);
               mpreprocess = (uu___1832_24142.mpreprocess);
               postprocess = (uu___1832_24142.postprocess);
               is_native_tactic = (uu___1832_24142.is_native_tactic);
               identifier_info = (uu___1832_24142.identifier_info);
               tc_hooks = (uu___1832_24142.tc_hooks);
               dsenv = (uu___1832_24142.dsenv);
               nbe = (uu___1832_24142.nbe);
               strict_args_tab = (uu___1832_24142.strict_args_tab);
               erasable_types_tab = (uu___1832_24142.erasable_types_tab)
             }))
    | uu____24143 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24172  ->
             match uu____24172 with | (x,uu____24180) -> push_bv env1 x) env
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
            let uu___1846_24215 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1846_24215.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1846_24215.FStar_Syntax_Syntax.index);
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
        let uu____24288 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24288 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24316 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24316)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1867_24332 = env  in
      {
        solver = (uu___1867_24332.solver);
        range = (uu___1867_24332.range);
        curmodule = (uu___1867_24332.curmodule);
        gamma = (uu___1867_24332.gamma);
        gamma_sig = (uu___1867_24332.gamma_sig);
        gamma_cache = (uu___1867_24332.gamma_cache);
        modules = (uu___1867_24332.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1867_24332.sigtab);
        attrtab = (uu___1867_24332.attrtab);
        instantiate_imp = (uu___1867_24332.instantiate_imp);
        effects = (uu___1867_24332.effects);
        generalize = (uu___1867_24332.generalize);
        letrecs = (uu___1867_24332.letrecs);
        top_level = (uu___1867_24332.top_level);
        check_uvars = (uu___1867_24332.check_uvars);
        use_eq = false;
        is_iface = (uu___1867_24332.is_iface);
        admit = (uu___1867_24332.admit);
        lax = (uu___1867_24332.lax);
        lax_universes = (uu___1867_24332.lax_universes);
        phase1 = (uu___1867_24332.phase1);
        failhard = (uu___1867_24332.failhard);
        nosynth = (uu___1867_24332.nosynth);
        uvar_subtyping = (uu___1867_24332.uvar_subtyping);
        tc_term = (uu___1867_24332.tc_term);
        type_of = (uu___1867_24332.type_of);
        universe_of = (uu___1867_24332.universe_of);
        check_type_of = (uu___1867_24332.check_type_of);
        use_bv_sorts = (uu___1867_24332.use_bv_sorts);
        qtbl_name_and_index = (uu___1867_24332.qtbl_name_and_index);
        normalized_eff_names = (uu___1867_24332.normalized_eff_names);
        fv_delta_depths = (uu___1867_24332.fv_delta_depths);
        proof_ns = (uu___1867_24332.proof_ns);
        synth_hook = (uu___1867_24332.synth_hook);
        splice = (uu___1867_24332.splice);
        mpreprocess = (uu___1867_24332.mpreprocess);
        postprocess = (uu___1867_24332.postprocess);
        is_native_tactic = (uu___1867_24332.is_native_tactic);
        identifier_info = (uu___1867_24332.identifier_info);
        tc_hooks = (uu___1867_24332.tc_hooks);
        dsenv = (uu___1867_24332.dsenv);
        nbe = (uu___1867_24332.nbe);
        strict_args_tab = (uu___1867_24332.strict_args_tab);
        erasable_types_tab = (uu___1867_24332.erasable_types_tab)
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
    let uu____24363 = expected_typ env_  in
    ((let uu___1874_24369 = env_  in
      {
        solver = (uu___1874_24369.solver);
        range = (uu___1874_24369.range);
        curmodule = (uu___1874_24369.curmodule);
        gamma = (uu___1874_24369.gamma);
        gamma_sig = (uu___1874_24369.gamma_sig);
        gamma_cache = (uu___1874_24369.gamma_cache);
        modules = (uu___1874_24369.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1874_24369.sigtab);
        attrtab = (uu___1874_24369.attrtab);
        instantiate_imp = (uu___1874_24369.instantiate_imp);
        effects = (uu___1874_24369.effects);
        generalize = (uu___1874_24369.generalize);
        letrecs = (uu___1874_24369.letrecs);
        top_level = (uu___1874_24369.top_level);
        check_uvars = (uu___1874_24369.check_uvars);
        use_eq = false;
        is_iface = (uu___1874_24369.is_iface);
        admit = (uu___1874_24369.admit);
        lax = (uu___1874_24369.lax);
        lax_universes = (uu___1874_24369.lax_universes);
        phase1 = (uu___1874_24369.phase1);
        failhard = (uu___1874_24369.failhard);
        nosynth = (uu___1874_24369.nosynth);
        uvar_subtyping = (uu___1874_24369.uvar_subtyping);
        tc_term = (uu___1874_24369.tc_term);
        type_of = (uu___1874_24369.type_of);
        universe_of = (uu___1874_24369.universe_of);
        check_type_of = (uu___1874_24369.check_type_of);
        use_bv_sorts = (uu___1874_24369.use_bv_sorts);
        qtbl_name_and_index = (uu___1874_24369.qtbl_name_and_index);
        normalized_eff_names = (uu___1874_24369.normalized_eff_names);
        fv_delta_depths = (uu___1874_24369.fv_delta_depths);
        proof_ns = (uu___1874_24369.proof_ns);
        synth_hook = (uu___1874_24369.synth_hook);
        splice = (uu___1874_24369.splice);
        mpreprocess = (uu___1874_24369.mpreprocess);
        postprocess = (uu___1874_24369.postprocess);
        is_native_tactic = (uu___1874_24369.is_native_tactic);
        identifier_info = (uu___1874_24369.identifier_info);
        tc_hooks = (uu___1874_24369.tc_hooks);
        dsenv = (uu___1874_24369.dsenv);
        nbe = (uu___1874_24369.nbe);
        strict_args_tab = (uu___1874_24369.strict_args_tab);
        erasable_types_tab = (uu___1874_24369.erasable_types_tab)
      }), uu____24363)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24381 =
      let uu____24384 = FStar_Ident.id_of_text ""  in [uu____24384]  in
    FStar_Ident.lid_of_ids uu____24381  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24391 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24391
        then
          let uu____24396 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24396 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1882_24424 = env  in
       {
         solver = (uu___1882_24424.solver);
         range = (uu___1882_24424.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1882_24424.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1882_24424.expected_typ);
         sigtab = (uu___1882_24424.sigtab);
         attrtab = (uu___1882_24424.attrtab);
         instantiate_imp = (uu___1882_24424.instantiate_imp);
         effects = (uu___1882_24424.effects);
         generalize = (uu___1882_24424.generalize);
         letrecs = (uu___1882_24424.letrecs);
         top_level = (uu___1882_24424.top_level);
         check_uvars = (uu___1882_24424.check_uvars);
         use_eq = (uu___1882_24424.use_eq);
         is_iface = (uu___1882_24424.is_iface);
         admit = (uu___1882_24424.admit);
         lax = (uu___1882_24424.lax);
         lax_universes = (uu___1882_24424.lax_universes);
         phase1 = (uu___1882_24424.phase1);
         failhard = (uu___1882_24424.failhard);
         nosynth = (uu___1882_24424.nosynth);
         uvar_subtyping = (uu___1882_24424.uvar_subtyping);
         tc_term = (uu___1882_24424.tc_term);
         type_of = (uu___1882_24424.type_of);
         universe_of = (uu___1882_24424.universe_of);
         check_type_of = (uu___1882_24424.check_type_of);
         use_bv_sorts = (uu___1882_24424.use_bv_sorts);
         qtbl_name_and_index = (uu___1882_24424.qtbl_name_and_index);
         normalized_eff_names = (uu___1882_24424.normalized_eff_names);
         fv_delta_depths = (uu___1882_24424.fv_delta_depths);
         proof_ns = (uu___1882_24424.proof_ns);
         synth_hook = (uu___1882_24424.synth_hook);
         splice = (uu___1882_24424.splice);
         mpreprocess = (uu___1882_24424.mpreprocess);
         postprocess = (uu___1882_24424.postprocess);
         is_native_tactic = (uu___1882_24424.is_native_tactic);
         identifier_info = (uu___1882_24424.identifier_info);
         tc_hooks = (uu___1882_24424.tc_hooks);
         dsenv = (uu___1882_24424.dsenv);
         nbe = (uu___1882_24424.nbe);
         strict_args_tab = (uu___1882_24424.strict_args_tab);
         erasable_types_tab = (uu___1882_24424.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24476)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24480,(uu____24481,t)))::tl1
          ->
          let uu____24502 =
            let uu____24505 = FStar_Syntax_Free.uvars t  in
            ext out uu____24505  in
          aux uu____24502 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24508;
            FStar_Syntax_Syntax.index = uu____24509;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24517 =
            let uu____24520 = FStar_Syntax_Free.uvars t  in
            ext out uu____24520  in
          aux uu____24517 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24578)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24582,(uu____24583,t)))::tl1
          ->
          let uu____24604 =
            let uu____24607 = FStar_Syntax_Free.univs t  in
            ext out uu____24607  in
          aux uu____24604 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24610;
            FStar_Syntax_Syntax.index = uu____24611;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24619 =
            let uu____24622 = FStar_Syntax_Free.univs t  in
            ext out uu____24622  in
          aux uu____24619 tl1
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
          let uu____24684 = FStar_Util.set_add uname out  in
          aux uu____24684 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24687,(uu____24688,t)))::tl1
          ->
          let uu____24709 =
            let uu____24712 = FStar_Syntax_Free.univnames t  in
            ext out uu____24712  in
          aux uu____24709 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24715;
            FStar_Syntax_Syntax.index = uu____24716;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24724 =
            let uu____24727 = FStar_Syntax_Free.univnames t  in
            ext out uu____24727  in
          aux uu____24724 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_24748  ->
            match uu___12_24748 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24752 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24765 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24776 =
      let uu____24785 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24785
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24776 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24833 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_24846  ->
              match uu___13_24846 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24849 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24849
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24855) ->
                  let uu____24872 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24872))
       in
    FStar_All.pipe_right uu____24833 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_24886  ->
    match uu___14_24886 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24892 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24892
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24915  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24970) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25003,uu____25004) -> false  in
      let uu____25018 =
        FStar_List.tryFind
          (fun uu____25040  ->
             match uu____25040 with | (p,uu____25051) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25018 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25070,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25100 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25100
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2025_25122 = e  in
        {
          solver = (uu___2025_25122.solver);
          range = (uu___2025_25122.range);
          curmodule = (uu___2025_25122.curmodule);
          gamma = (uu___2025_25122.gamma);
          gamma_sig = (uu___2025_25122.gamma_sig);
          gamma_cache = (uu___2025_25122.gamma_cache);
          modules = (uu___2025_25122.modules);
          expected_typ = (uu___2025_25122.expected_typ);
          sigtab = (uu___2025_25122.sigtab);
          attrtab = (uu___2025_25122.attrtab);
          instantiate_imp = (uu___2025_25122.instantiate_imp);
          effects = (uu___2025_25122.effects);
          generalize = (uu___2025_25122.generalize);
          letrecs = (uu___2025_25122.letrecs);
          top_level = (uu___2025_25122.top_level);
          check_uvars = (uu___2025_25122.check_uvars);
          use_eq = (uu___2025_25122.use_eq);
          is_iface = (uu___2025_25122.is_iface);
          admit = (uu___2025_25122.admit);
          lax = (uu___2025_25122.lax);
          lax_universes = (uu___2025_25122.lax_universes);
          phase1 = (uu___2025_25122.phase1);
          failhard = (uu___2025_25122.failhard);
          nosynth = (uu___2025_25122.nosynth);
          uvar_subtyping = (uu___2025_25122.uvar_subtyping);
          tc_term = (uu___2025_25122.tc_term);
          type_of = (uu___2025_25122.type_of);
          universe_of = (uu___2025_25122.universe_of);
          check_type_of = (uu___2025_25122.check_type_of);
          use_bv_sorts = (uu___2025_25122.use_bv_sorts);
          qtbl_name_and_index = (uu___2025_25122.qtbl_name_and_index);
          normalized_eff_names = (uu___2025_25122.normalized_eff_names);
          fv_delta_depths = (uu___2025_25122.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2025_25122.synth_hook);
          splice = (uu___2025_25122.splice);
          mpreprocess = (uu___2025_25122.mpreprocess);
          postprocess = (uu___2025_25122.postprocess);
          is_native_tactic = (uu___2025_25122.is_native_tactic);
          identifier_info = (uu___2025_25122.identifier_info);
          tc_hooks = (uu___2025_25122.tc_hooks);
          dsenv = (uu___2025_25122.dsenv);
          nbe = (uu___2025_25122.nbe);
          strict_args_tab = (uu___2025_25122.strict_args_tab);
          erasable_types_tab = (uu___2025_25122.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2034_25170 = e  in
      {
        solver = (uu___2034_25170.solver);
        range = (uu___2034_25170.range);
        curmodule = (uu___2034_25170.curmodule);
        gamma = (uu___2034_25170.gamma);
        gamma_sig = (uu___2034_25170.gamma_sig);
        gamma_cache = (uu___2034_25170.gamma_cache);
        modules = (uu___2034_25170.modules);
        expected_typ = (uu___2034_25170.expected_typ);
        sigtab = (uu___2034_25170.sigtab);
        attrtab = (uu___2034_25170.attrtab);
        instantiate_imp = (uu___2034_25170.instantiate_imp);
        effects = (uu___2034_25170.effects);
        generalize = (uu___2034_25170.generalize);
        letrecs = (uu___2034_25170.letrecs);
        top_level = (uu___2034_25170.top_level);
        check_uvars = (uu___2034_25170.check_uvars);
        use_eq = (uu___2034_25170.use_eq);
        is_iface = (uu___2034_25170.is_iface);
        admit = (uu___2034_25170.admit);
        lax = (uu___2034_25170.lax);
        lax_universes = (uu___2034_25170.lax_universes);
        phase1 = (uu___2034_25170.phase1);
        failhard = (uu___2034_25170.failhard);
        nosynth = (uu___2034_25170.nosynth);
        uvar_subtyping = (uu___2034_25170.uvar_subtyping);
        tc_term = (uu___2034_25170.tc_term);
        type_of = (uu___2034_25170.type_of);
        universe_of = (uu___2034_25170.universe_of);
        check_type_of = (uu___2034_25170.check_type_of);
        use_bv_sorts = (uu___2034_25170.use_bv_sorts);
        qtbl_name_and_index = (uu___2034_25170.qtbl_name_and_index);
        normalized_eff_names = (uu___2034_25170.normalized_eff_names);
        fv_delta_depths = (uu___2034_25170.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2034_25170.synth_hook);
        splice = (uu___2034_25170.splice);
        mpreprocess = (uu___2034_25170.mpreprocess);
        postprocess = (uu___2034_25170.postprocess);
        is_native_tactic = (uu___2034_25170.is_native_tactic);
        identifier_info = (uu___2034_25170.identifier_info);
        tc_hooks = (uu___2034_25170.tc_hooks);
        dsenv = (uu___2034_25170.dsenv);
        nbe = (uu___2034_25170.nbe);
        strict_args_tab = (uu___2034_25170.strict_args_tab);
        erasable_types_tab = (uu___2034_25170.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25186 = FStar_Syntax_Free.names t  in
      let uu____25189 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25186 uu____25189
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25212 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25212
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25222 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25222
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25243 =
      match uu____25243 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25263 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25263)
       in
    let uu____25271 =
      let uu____25275 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25275 FStar_List.rev  in
    FStar_All.pipe_right uu____25271 (FStar_String.concat " ")
  
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
                  (let uu____25343 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25343 with
                   | FStar_Pervasives_Native.Some uu____25347 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25350 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25360;
        FStar_TypeChecker_Common.univ_ineqs = uu____25361;
        FStar_TypeChecker_Common.implicits = uu____25362;_} -> true
    | uu____25372 -> false
  
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
          let uu___2078_25394 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2078_25394.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2078_25394.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2078_25394.FStar_TypeChecker_Common.implicits)
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
          let uu____25433 = FStar_Options.defensive ()  in
          if uu____25433
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25439 =
              let uu____25441 =
                let uu____25443 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25443  in
              Prims.op_Negation uu____25441  in
            (if uu____25439
             then
               let uu____25450 =
                 let uu____25456 =
                   let uu____25458 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25460 =
                     let uu____25462 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25462
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25458 uu____25460
                    in
                 (FStar_Errors.Warning_Defensive, uu____25456)  in
               FStar_Errors.log_issue rng uu____25450
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
          let uu____25502 =
            let uu____25504 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25504  in
          if uu____25502
          then ()
          else
            (let uu____25509 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25509 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25535 =
            let uu____25537 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25537  in
          if uu____25535
          then ()
          else
            (let uu____25542 = bound_vars e  in
             def_check_closed_in rng msg uu____25542 t)
  
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
          let uu___2115_25581 = g  in
          let uu____25582 =
            let uu____25583 =
              let uu____25584 =
                let uu____25591 =
                  let uu____25592 =
                    let uu____25609 =
                      let uu____25620 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25620]  in
                    (f, uu____25609)  in
                  FStar_Syntax_Syntax.Tm_app uu____25592  in
                FStar_Syntax_Syntax.mk uu____25591  in
              uu____25584 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25657  -> FStar_TypeChecker_Common.NonTrivial _25657)
              uu____25583
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____25582;
            FStar_TypeChecker_Common.deferred =
              (uu___2115_25581.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2115_25581.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2115_25581.FStar_TypeChecker_Common.implicits)
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
          let uu___2122_25675 = g  in
          let uu____25676 =
            let uu____25677 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25677  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25676;
            FStar_TypeChecker_Common.deferred =
              (uu___2122_25675.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2122_25675.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2122_25675.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2127_25694 = g  in
          let uu____25695 =
            let uu____25696 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25696  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25695;
            FStar_TypeChecker_Common.deferred =
              (uu___2127_25694.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2127_25694.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2127_25694.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2131_25698 = g  in
          let uu____25699 =
            let uu____25700 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25700  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25699;
            FStar_TypeChecker_Common.deferred =
              (uu___2131_25698.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2131_25698.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2131_25698.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25707 ->
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
                       let uu____25784 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25784
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2154_25791 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2154_25791.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2154_25791.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2154_25791.FStar_TypeChecker_Common.implicits)
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
               let uu____25825 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25825
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
            let uu___2169_25852 = g  in
            let uu____25853 =
              let uu____25854 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25854  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25853;
              FStar_TypeChecker_Common.deferred =
                (uu___2169_25852.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2169_25852.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2169_25852.FStar_TypeChecker_Common.implicits)
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
              let uu____25912 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25912 with
              | FStar_Pervasives_Native.Some
                  (uu____25937::(tm,uu____25939)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26003 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26021 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26021;
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
                      let uu___2191_26053 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2191_26053.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2191_26053.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2191_26053.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____26107 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____26164  ->
                      fun b  ->
                        match uu____26164 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____26206 =
                              let uu____26219 = reason b  in
                              new_implicit_var_aux uu____26219 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____26206 with
                             | (t,uu____26236,g_t) ->
                                 let uu____26250 =
                                   let uu____26253 =
                                     let uu____26256 =
                                       let uu____26257 =
                                         let uu____26264 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26264, t)  in
                                       FStar_Syntax_Syntax.NT uu____26257  in
                                     [uu____26256]  in
                                   FStar_List.append substs1 uu____26253  in
                                 let uu____26275 = conj_guard g g_t  in
                                 (uu____26250,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26275))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____26107
              (fun uu____26304  ->
                 match uu____26304 with
                 | (uu____26321,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26337  -> ());
    push = (fun uu____26339  -> ());
    pop = (fun uu____26342  -> ());
    snapshot =
      (fun uu____26345  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26364  -> fun uu____26365  -> ());
    encode_sig = (fun uu____26380  -> fun uu____26381  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26387 =
             let uu____26394 = FStar_Options.peek ()  in (e, g, uu____26394)
              in
           [uu____26387]);
    solve = (fun uu____26410  -> fun uu____26411  -> fun uu____26412  -> ());
    finish = (fun uu____26419  -> ());
    refresh = (fun uu____26421  -> ())
  } 