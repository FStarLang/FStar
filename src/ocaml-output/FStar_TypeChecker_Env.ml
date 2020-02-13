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
           (fun uu___0_13291  ->
              match uu___0_13291 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13294 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13294  in
                  let uu____13295 =
                    let uu____13296 = FStar_Syntax_Subst.compress y  in
                    uu____13296.FStar_Syntax_Syntax.n  in
                  (match uu____13295 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13300 =
                         let uu___318_13301 = y1  in
                         let uu____13302 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___318_13301.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___318_13301.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13302
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13300
                   | uu____13305 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___324_13319 = env  in
      let uu____13320 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___324_13319.solver);
        range = (uu___324_13319.range);
        curmodule = (uu___324_13319.curmodule);
        gamma = uu____13320;
        gamma_sig = (uu___324_13319.gamma_sig);
        gamma_cache = (uu___324_13319.gamma_cache);
        modules = (uu___324_13319.modules);
        expected_typ = (uu___324_13319.expected_typ);
        sigtab = (uu___324_13319.sigtab);
        attrtab = (uu___324_13319.attrtab);
        instantiate_imp = (uu___324_13319.instantiate_imp);
        effects = (uu___324_13319.effects);
        generalize = (uu___324_13319.generalize);
        letrecs = (uu___324_13319.letrecs);
        top_level = (uu___324_13319.top_level);
        check_uvars = (uu___324_13319.check_uvars);
        use_eq = (uu___324_13319.use_eq);
        is_iface = (uu___324_13319.is_iface);
        admit = (uu___324_13319.admit);
        lax = (uu___324_13319.lax);
        lax_universes = (uu___324_13319.lax_universes);
        phase1 = (uu___324_13319.phase1);
        failhard = (uu___324_13319.failhard);
        nosynth = (uu___324_13319.nosynth);
        uvar_subtyping = (uu___324_13319.uvar_subtyping);
        tc_term = (uu___324_13319.tc_term);
        type_of = (uu___324_13319.type_of);
        universe_of = (uu___324_13319.universe_of);
        check_type_of = (uu___324_13319.check_type_of);
        use_bv_sorts = (uu___324_13319.use_bv_sorts);
        qtbl_name_and_index = (uu___324_13319.qtbl_name_and_index);
        normalized_eff_names = (uu___324_13319.normalized_eff_names);
        fv_delta_depths = (uu___324_13319.fv_delta_depths);
        proof_ns = (uu___324_13319.proof_ns);
        synth_hook = (uu___324_13319.synth_hook);
        splice = (uu___324_13319.splice);
        mpreprocess = (uu___324_13319.mpreprocess);
        postprocess = (uu___324_13319.postprocess);
        is_native_tactic = (uu___324_13319.is_native_tactic);
        identifier_info = (uu___324_13319.identifier_info);
        tc_hooks = (uu___324_13319.tc_hooks);
        dsenv = (uu___324_13319.dsenv);
        nbe = (uu___324_13319.nbe);
        strict_args_tab = (uu___324_13319.strict_args_tab);
        erasable_types_tab = (uu___324_13319.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13328  -> fun uu____13329  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___331_13351 = env  in
      {
        solver = (uu___331_13351.solver);
        range = (uu___331_13351.range);
        curmodule = (uu___331_13351.curmodule);
        gamma = (uu___331_13351.gamma);
        gamma_sig = (uu___331_13351.gamma_sig);
        gamma_cache = (uu___331_13351.gamma_cache);
        modules = (uu___331_13351.modules);
        expected_typ = (uu___331_13351.expected_typ);
        sigtab = (uu___331_13351.sigtab);
        attrtab = (uu___331_13351.attrtab);
        instantiate_imp = (uu___331_13351.instantiate_imp);
        effects = (uu___331_13351.effects);
        generalize = (uu___331_13351.generalize);
        letrecs = (uu___331_13351.letrecs);
        top_level = (uu___331_13351.top_level);
        check_uvars = (uu___331_13351.check_uvars);
        use_eq = (uu___331_13351.use_eq);
        is_iface = (uu___331_13351.is_iface);
        admit = (uu___331_13351.admit);
        lax = (uu___331_13351.lax);
        lax_universes = (uu___331_13351.lax_universes);
        phase1 = (uu___331_13351.phase1);
        failhard = (uu___331_13351.failhard);
        nosynth = (uu___331_13351.nosynth);
        uvar_subtyping = (uu___331_13351.uvar_subtyping);
        tc_term = (uu___331_13351.tc_term);
        type_of = (uu___331_13351.type_of);
        universe_of = (uu___331_13351.universe_of);
        check_type_of = (uu___331_13351.check_type_of);
        use_bv_sorts = (uu___331_13351.use_bv_sorts);
        qtbl_name_and_index = (uu___331_13351.qtbl_name_and_index);
        normalized_eff_names = (uu___331_13351.normalized_eff_names);
        fv_delta_depths = (uu___331_13351.fv_delta_depths);
        proof_ns = (uu___331_13351.proof_ns);
        synth_hook = (uu___331_13351.synth_hook);
        splice = (uu___331_13351.splice);
        mpreprocess = (uu___331_13351.mpreprocess);
        postprocess = (uu___331_13351.postprocess);
        is_native_tactic = (uu___331_13351.is_native_tactic);
        identifier_info = (uu___331_13351.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___331_13351.dsenv);
        nbe = (uu___331_13351.nbe);
        strict_args_tab = (uu___331_13351.strict_args_tab);
        erasable_types_tab = (uu___331_13351.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___335_13363 = e  in
      let uu____13364 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___335_13363.solver);
        range = (uu___335_13363.range);
        curmodule = (uu___335_13363.curmodule);
        gamma = (uu___335_13363.gamma);
        gamma_sig = (uu___335_13363.gamma_sig);
        gamma_cache = (uu___335_13363.gamma_cache);
        modules = (uu___335_13363.modules);
        expected_typ = (uu___335_13363.expected_typ);
        sigtab = (uu___335_13363.sigtab);
        attrtab = (uu___335_13363.attrtab);
        instantiate_imp = (uu___335_13363.instantiate_imp);
        effects = (uu___335_13363.effects);
        generalize = (uu___335_13363.generalize);
        letrecs = (uu___335_13363.letrecs);
        top_level = (uu___335_13363.top_level);
        check_uvars = (uu___335_13363.check_uvars);
        use_eq = (uu___335_13363.use_eq);
        is_iface = (uu___335_13363.is_iface);
        admit = (uu___335_13363.admit);
        lax = (uu___335_13363.lax);
        lax_universes = (uu___335_13363.lax_universes);
        phase1 = (uu___335_13363.phase1);
        failhard = (uu___335_13363.failhard);
        nosynth = (uu___335_13363.nosynth);
        uvar_subtyping = (uu___335_13363.uvar_subtyping);
        tc_term = (uu___335_13363.tc_term);
        type_of = (uu___335_13363.type_of);
        universe_of = (uu___335_13363.universe_of);
        check_type_of = (uu___335_13363.check_type_of);
        use_bv_sorts = (uu___335_13363.use_bv_sorts);
        qtbl_name_and_index = (uu___335_13363.qtbl_name_and_index);
        normalized_eff_names = (uu___335_13363.normalized_eff_names);
        fv_delta_depths = (uu___335_13363.fv_delta_depths);
        proof_ns = (uu___335_13363.proof_ns);
        synth_hook = (uu___335_13363.synth_hook);
        splice = (uu___335_13363.splice);
        mpreprocess = (uu___335_13363.mpreprocess);
        postprocess = (uu___335_13363.postprocess);
        is_native_tactic = (uu___335_13363.is_native_tactic);
        identifier_info = (uu___335_13363.identifier_info);
        tc_hooks = (uu___335_13363.tc_hooks);
        dsenv = uu____13364;
        nbe = (uu___335_13363.nbe);
        strict_args_tab = (uu___335_13363.strict_args_tab);
        erasable_types_tab = (uu___335_13363.erasable_types_tab)
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
      | (NoDelta ,uu____13393) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13396,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13398,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13401 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13415 . unit -> 'Auu____13415 FStar_Util.smap =
  fun uu____13422  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13428 . unit -> 'Auu____13428 FStar_Util.smap =
  fun uu____13435  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13573 = new_gamma_cache ()  in
                  let uu____13576 = new_sigtab ()  in
                  let uu____13579 = new_sigtab ()  in
                  let uu____13586 =
                    let uu____13601 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13601, FStar_Pervasives_Native.None)  in
                  let uu____13622 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13626 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13630 = FStar_Options.using_facts_from ()  in
                  let uu____13631 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13634 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13635 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13649 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13573;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13576;
                    attrtab = uu____13579;
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
                    qtbl_name_and_index = uu____13586;
                    normalized_eff_names = uu____13622;
                    fv_delta_depths = uu____13626;
                    proof_ns = uu____13630;
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
                    is_native_tactic = (fun uu____13756  -> false);
                    identifier_info = uu____13631;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13634;
                    nbe = nbe1;
                    strict_args_tab = uu____13635;
                    erasable_types_tab = uu____13649
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
  fun uu____13835  ->
    let uu____13836 = FStar_ST.op_Bang query_indices  in
    match uu____13836 with
    | [] -> failwith "Empty query indices!"
    | uu____13891 ->
        let uu____13901 =
          let uu____13911 =
            let uu____13919 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13919  in
          let uu____13973 = FStar_ST.op_Bang query_indices  in uu____13911 ::
            uu____13973
           in
        FStar_ST.op_Colon_Equals query_indices uu____13901
  
let (pop_query_indices : unit -> unit) =
  fun uu____14069  ->
    let uu____14070 = FStar_ST.op_Bang query_indices  in
    match uu____14070 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14197  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14234  ->
    match uu____14234 with
    | (l,n1) ->
        let uu____14244 = FStar_ST.op_Bang query_indices  in
        (match uu____14244 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14366 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14389  ->
    let uu____14390 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14390
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14458 =
       let uu____14461 = FStar_ST.op_Bang stack  in env :: uu____14461  in
     FStar_ST.op_Colon_Equals stack uu____14458);
    (let uu___406_14510 = env  in
     let uu____14511 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14514 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14517 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14524 =
       let uu____14539 =
         let uu____14543 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14543  in
       let uu____14575 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14539, uu____14575)  in
     let uu____14624 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14627 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14630 =
       let uu____14633 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14633  in
     let uu____14653 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14666 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___406_14510.solver);
       range = (uu___406_14510.range);
       curmodule = (uu___406_14510.curmodule);
       gamma = (uu___406_14510.gamma);
       gamma_sig = (uu___406_14510.gamma_sig);
       gamma_cache = uu____14511;
       modules = (uu___406_14510.modules);
       expected_typ = (uu___406_14510.expected_typ);
       sigtab = uu____14514;
       attrtab = uu____14517;
       instantiate_imp = (uu___406_14510.instantiate_imp);
       effects = (uu___406_14510.effects);
       generalize = (uu___406_14510.generalize);
       letrecs = (uu___406_14510.letrecs);
       top_level = (uu___406_14510.top_level);
       check_uvars = (uu___406_14510.check_uvars);
       use_eq = (uu___406_14510.use_eq);
       is_iface = (uu___406_14510.is_iface);
       admit = (uu___406_14510.admit);
       lax = (uu___406_14510.lax);
       lax_universes = (uu___406_14510.lax_universes);
       phase1 = (uu___406_14510.phase1);
       failhard = (uu___406_14510.failhard);
       nosynth = (uu___406_14510.nosynth);
       uvar_subtyping = (uu___406_14510.uvar_subtyping);
       tc_term = (uu___406_14510.tc_term);
       type_of = (uu___406_14510.type_of);
       universe_of = (uu___406_14510.universe_of);
       check_type_of = (uu___406_14510.check_type_of);
       use_bv_sorts = (uu___406_14510.use_bv_sorts);
       qtbl_name_and_index = uu____14524;
       normalized_eff_names = uu____14624;
       fv_delta_depths = uu____14627;
       proof_ns = (uu___406_14510.proof_ns);
       synth_hook = (uu___406_14510.synth_hook);
       splice = (uu___406_14510.splice);
       mpreprocess = (uu___406_14510.mpreprocess);
       postprocess = (uu___406_14510.postprocess);
       is_native_tactic = (uu___406_14510.is_native_tactic);
       identifier_info = uu____14630;
       tc_hooks = (uu___406_14510.tc_hooks);
       dsenv = (uu___406_14510.dsenv);
       nbe = (uu___406_14510.nbe);
       strict_args_tab = uu____14653;
       erasable_types_tab = uu____14666
     })
  
let (pop_stack : unit -> env) =
  fun uu____14676  ->
    let uu____14677 = FStar_ST.op_Bang stack  in
    match uu____14677 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14731 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14821  ->
           let uu____14822 = snapshot_stack env  in
           match uu____14822 with
           | (stack_depth,env1) ->
               let uu____14856 = snapshot_query_indices ()  in
               (match uu____14856 with
                | (query_indices_depth,()) ->
                    let uu____14889 = (env1.solver).snapshot msg  in
                    (match uu____14889 with
                     | (solver_depth,()) ->
                         let uu____14946 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14946 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___431_15013 = env1  in
                                 {
                                   solver = (uu___431_15013.solver);
                                   range = (uu___431_15013.range);
                                   curmodule = (uu___431_15013.curmodule);
                                   gamma = (uu___431_15013.gamma);
                                   gamma_sig = (uu___431_15013.gamma_sig);
                                   gamma_cache = (uu___431_15013.gamma_cache);
                                   modules = (uu___431_15013.modules);
                                   expected_typ =
                                     (uu___431_15013.expected_typ);
                                   sigtab = (uu___431_15013.sigtab);
                                   attrtab = (uu___431_15013.attrtab);
                                   instantiate_imp =
                                     (uu___431_15013.instantiate_imp);
                                   effects = (uu___431_15013.effects);
                                   generalize = (uu___431_15013.generalize);
                                   letrecs = (uu___431_15013.letrecs);
                                   top_level = (uu___431_15013.top_level);
                                   check_uvars = (uu___431_15013.check_uvars);
                                   use_eq = (uu___431_15013.use_eq);
                                   is_iface = (uu___431_15013.is_iface);
                                   admit = (uu___431_15013.admit);
                                   lax = (uu___431_15013.lax);
                                   lax_universes =
                                     (uu___431_15013.lax_universes);
                                   phase1 = (uu___431_15013.phase1);
                                   failhard = (uu___431_15013.failhard);
                                   nosynth = (uu___431_15013.nosynth);
                                   uvar_subtyping =
                                     (uu___431_15013.uvar_subtyping);
                                   tc_term = (uu___431_15013.tc_term);
                                   type_of = (uu___431_15013.type_of);
                                   universe_of = (uu___431_15013.universe_of);
                                   check_type_of =
                                     (uu___431_15013.check_type_of);
                                   use_bv_sorts =
                                     (uu___431_15013.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___431_15013.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___431_15013.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___431_15013.fv_delta_depths);
                                   proof_ns = (uu___431_15013.proof_ns);
                                   synth_hook = (uu___431_15013.synth_hook);
                                   splice = (uu___431_15013.splice);
                                   mpreprocess = (uu___431_15013.mpreprocess);
                                   postprocess = (uu___431_15013.postprocess);
                                   is_native_tactic =
                                     (uu___431_15013.is_native_tactic);
                                   identifier_info =
                                     (uu___431_15013.identifier_info);
                                   tc_hooks = (uu___431_15013.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___431_15013.nbe);
                                   strict_args_tab =
                                     (uu___431_15013.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___431_15013.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15047  ->
             let uu____15048 =
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
             match uu____15048 with
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
                             ((let uu____15228 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15228
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15244 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15244
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15276,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15318 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15348  ->
                  match uu____15348 with
                  | (m,uu____15356) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15318 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___476_15371 = env  in
               {
                 solver = (uu___476_15371.solver);
                 range = (uu___476_15371.range);
                 curmodule = (uu___476_15371.curmodule);
                 gamma = (uu___476_15371.gamma);
                 gamma_sig = (uu___476_15371.gamma_sig);
                 gamma_cache = (uu___476_15371.gamma_cache);
                 modules = (uu___476_15371.modules);
                 expected_typ = (uu___476_15371.expected_typ);
                 sigtab = (uu___476_15371.sigtab);
                 attrtab = (uu___476_15371.attrtab);
                 instantiate_imp = (uu___476_15371.instantiate_imp);
                 effects = (uu___476_15371.effects);
                 generalize = (uu___476_15371.generalize);
                 letrecs = (uu___476_15371.letrecs);
                 top_level = (uu___476_15371.top_level);
                 check_uvars = (uu___476_15371.check_uvars);
                 use_eq = (uu___476_15371.use_eq);
                 is_iface = (uu___476_15371.is_iface);
                 admit = (uu___476_15371.admit);
                 lax = (uu___476_15371.lax);
                 lax_universes = (uu___476_15371.lax_universes);
                 phase1 = (uu___476_15371.phase1);
                 failhard = (uu___476_15371.failhard);
                 nosynth = (uu___476_15371.nosynth);
                 uvar_subtyping = (uu___476_15371.uvar_subtyping);
                 tc_term = (uu___476_15371.tc_term);
                 type_of = (uu___476_15371.type_of);
                 universe_of = (uu___476_15371.universe_of);
                 check_type_of = (uu___476_15371.check_type_of);
                 use_bv_sorts = (uu___476_15371.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___476_15371.normalized_eff_names);
                 fv_delta_depths = (uu___476_15371.fv_delta_depths);
                 proof_ns = (uu___476_15371.proof_ns);
                 synth_hook = (uu___476_15371.synth_hook);
                 splice = (uu___476_15371.splice);
                 mpreprocess = (uu___476_15371.mpreprocess);
                 postprocess = (uu___476_15371.postprocess);
                 is_native_tactic = (uu___476_15371.is_native_tactic);
                 identifier_info = (uu___476_15371.identifier_info);
                 tc_hooks = (uu___476_15371.tc_hooks);
                 dsenv = (uu___476_15371.dsenv);
                 nbe = (uu___476_15371.nbe);
                 strict_args_tab = (uu___476_15371.strict_args_tab);
                 erasable_types_tab = (uu___476_15371.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15388,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___485_15404 = env  in
               {
                 solver = (uu___485_15404.solver);
                 range = (uu___485_15404.range);
                 curmodule = (uu___485_15404.curmodule);
                 gamma = (uu___485_15404.gamma);
                 gamma_sig = (uu___485_15404.gamma_sig);
                 gamma_cache = (uu___485_15404.gamma_cache);
                 modules = (uu___485_15404.modules);
                 expected_typ = (uu___485_15404.expected_typ);
                 sigtab = (uu___485_15404.sigtab);
                 attrtab = (uu___485_15404.attrtab);
                 instantiate_imp = (uu___485_15404.instantiate_imp);
                 effects = (uu___485_15404.effects);
                 generalize = (uu___485_15404.generalize);
                 letrecs = (uu___485_15404.letrecs);
                 top_level = (uu___485_15404.top_level);
                 check_uvars = (uu___485_15404.check_uvars);
                 use_eq = (uu___485_15404.use_eq);
                 is_iface = (uu___485_15404.is_iface);
                 admit = (uu___485_15404.admit);
                 lax = (uu___485_15404.lax);
                 lax_universes = (uu___485_15404.lax_universes);
                 phase1 = (uu___485_15404.phase1);
                 failhard = (uu___485_15404.failhard);
                 nosynth = (uu___485_15404.nosynth);
                 uvar_subtyping = (uu___485_15404.uvar_subtyping);
                 tc_term = (uu___485_15404.tc_term);
                 type_of = (uu___485_15404.type_of);
                 universe_of = (uu___485_15404.universe_of);
                 check_type_of = (uu___485_15404.check_type_of);
                 use_bv_sorts = (uu___485_15404.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___485_15404.normalized_eff_names);
                 fv_delta_depths = (uu___485_15404.fv_delta_depths);
                 proof_ns = (uu___485_15404.proof_ns);
                 synth_hook = (uu___485_15404.synth_hook);
                 splice = (uu___485_15404.splice);
                 mpreprocess = (uu___485_15404.mpreprocess);
                 postprocess = (uu___485_15404.postprocess);
                 is_native_tactic = (uu___485_15404.is_native_tactic);
                 identifier_info = (uu___485_15404.identifier_info);
                 tc_hooks = (uu___485_15404.tc_hooks);
                 dsenv = (uu___485_15404.dsenv);
                 nbe = (uu___485_15404.nbe);
                 strict_args_tab = (uu___485_15404.strict_args_tab);
                 erasable_types_tab = (uu___485_15404.erasable_types_tab)
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
        (let uu___492_15447 = e  in
         {
           solver = (uu___492_15447.solver);
           range = r;
           curmodule = (uu___492_15447.curmodule);
           gamma = (uu___492_15447.gamma);
           gamma_sig = (uu___492_15447.gamma_sig);
           gamma_cache = (uu___492_15447.gamma_cache);
           modules = (uu___492_15447.modules);
           expected_typ = (uu___492_15447.expected_typ);
           sigtab = (uu___492_15447.sigtab);
           attrtab = (uu___492_15447.attrtab);
           instantiate_imp = (uu___492_15447.instantiate_imp);
           effects = (uu___492_15447.effects);
           generalize = (uu___492_15447.generalize);
           letrecs = (uu___492_15447.letrecs);
           top_level = (uu___492_15447.top_level);
           check_uvars = (uu___492_15447.check_uvars);
           use_eq = (uu___492_15447.use_eq);
           is_iface = (uu___492_15447.is_iface);
           admit = (uu___492_15447.admit);
           lax = (uu___492_15447.lax);
           lax_universes = (uu___492_15447.lax_universes);
           phase1 = (uu___492_15447.phase1);
           failhard = (uu___492_15447.failhard);
           nosynth = (uu___492_15447.nosynth);
           uvar_subtyping = (uu___492_15447.uvar_subtyping);
           tc_term = (uu___492_15447.tc_term);
           type_of = (uu___492_15447.type_of);
           universe_of = (uu___492_15447.universe_of);
           check_type_of = (uu___492_15447.check_type_of);
           use_bv_sorts = (uu___492_15447.use_bv_sorts);
           qtbl_name_and_index = (uu___492_15447.qtbl_name_and_index);
           normalized_eff_names = (uu___492_15447.normalized_eff_names);
           fv_delta_depths = (uu___492_15447.fv_delta_depths);
           proof_ns = (uu___492_15447.proof_ns);
           synth_hook = (uu___492_15447.synth_hook);
           splice = (uu___492_15447.splice);
           mpreprocess = (uu___492_15447.mpreprocess);
           postprocess = (uu___492_15447.postprocess);
           is_native_tactic = (uu___492_15447.is_native_tactic);
           identifier_info = (uu___492_15447.identifier_info);
           tc_hooks = (uu___492_15447.tc_hooks);
           dsenv = (uu___492_15447.dsenv);
           nbe = (uu___492_15447.nbe);
           strict_args_tab = (uu___492_15447.strict_args_tab);
           erasable_types_tab = (uu___492_15447.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15467 =
        let uu____15468 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15468 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15467
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15523 =
          let uu____15524 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15524 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15523
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15579 =
          let uu____15580 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15580 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15579
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15635 =
        let uu____15636 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15636 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15635
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___509_15700 = env  in
      {
        solver = (uu___509_15700.solver);
        range = (uu___509_15700.range);
        curmodule = lid;
        gamma = (uu___509_15700.gamma);
        gamma_sig = (uu___509_15700.gamma_sig);
        gamma_cache = (uu___509_15700.gamma_cache);
        modules = (uu___509_15700.modules);
        expected_typ = (uu___509_15700.expected_typ);
        sigtab = (uu___509_15700.sigtab);
        attrtab = (uu___509_15700.attrtab);
        instantiate_imp = (uu___509_15700.instantiate_imp);
        effects = (uu___509_15700.effects);
        generalize = (uu___509_15700.generalize);
        letrecs = (uu___509_15700.letrecs);
        top_level = (uu___509_15700.top_level);
        check_uvars = (uu___509_15700.check_uvars);
        use_eq = (uu___509_15700.use_eq);
        is_iface = (uu___509_15700.is_iface);
        admit = (uu___509_15700.admit);
        lax = (uu___509_15700.lax);
        lax_universes = (uu___509_15700.lax_universes);
        phase1 = (uu___509_15700.phase1);
        failhard = (uu___509_15700.failhard);
        nosynth = (uu___509_15700.nosynth);
        uvar_subtyping = (uu___509_15700.uvar_subtyping);
        tc_term = (uu___509_15700.tc_term);
        type_of = (uu___509_15700.type_of);
        universe_of = (uu___509_15700.universe_of);
        check_type_of = (uu___509_15700.check_type_of);
        use_bv_sorts = (uu___509_15700.use_bv_sorts);
        qtbl_name_and_index = (uu___509_15700.qtbl_name_and_index);
        normalized_eff_names = (uu___509_15700.normalized_eff_names);
        fv_delta_depths = (uu___509_15700.fv_delta_depths);
        proof_ns = (uu___509_15700.proof_ns);
        synth_hook = (uu___509_15700.synth_hook);
        splice = (uu___509_15700.splice);
        mpreprocess = (uu___509_15700.mpreprocess);
        postprocess = (uu___509_15700.postprocess);
        is_native_tactic = (uu___509_15700.is_native_tactic);
        identifier_info = (uu___509_15700.identifier_info);
        tc_hooks = (uu___509_15700.tc_hooks);
        dsenv = (uu___509_15700.dsenv);
        nbe = (uu___509_15700.nbe);
        strict_args_tab = (uu___509_15700.strict_args_tab);
        erasable_types_tab = (uu___509_15700.erasable_types_tab)
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
      let uu____15731 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15731
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15744 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15744)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15759 =
      let uu____15761 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15761  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15759)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15770  ->
    let uu____15771 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15771
  
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
      | ((formals,t),uu____15871) ->
          let vs = mk_univ_subst formals us  in
          let uu____15895 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15895)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15912  ->
    match uu___1_15912 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15938  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15958 = inst_tscheme t  in
      match uu____15958 with
      | (us,t1) ->
          let uu____15969 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15969)
  
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
          let uu____15994 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15996 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15994 uu____15996
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
        fun uu____16023  ->
          match uu____16023 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16037 =
                    let uu____16039 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16043 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16047 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16049 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16039 uu____16043 uu____16047 uu____16049
                     in
                  failwith uu____16037)
               else ();
               (let uu____16054 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16054))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16072 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16083 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16094 -> false
  
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
             | ([],uu____16142) -> Maybe
             | (uu____16149,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16169 -> No  in
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
          let uu____16263 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16263 with
          | FStar_Pervasives_Native.None  ->
              let uu____16286 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16330  ->
                     match uu___2_16330 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16369 = FStar_Ident.lid_equals lid l  in
                         if uu____16369
                         then
                           let uu____16392 =
                             let uu____16411 =
                               let uu____16426 = inst_tscheme t  in
                               FStar_Util.Inl uu____16426  in
                             let uu____16441 = FStar_Ident.range_of_lid l  in
                             (uu____16411, uu____16441)  in
                           FStar_Pervasives_Native.Some uu____16392
                         else FStar_Pervasives_Native.None
                     | uu____16494 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16286
                (fun uu____16532  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16542  ->
                        match uu___3_16542 with
                        | (uu____16545,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16547);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16548;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16549;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16550;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16551;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16552;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16574 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16574
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
                                  uu____16626 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16633 -> cache t  in
                            let uu____16634 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16634 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16640 =
                                   let uu____16641 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16641)
                                    in
                                 maybe_cache uu____16640)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16712 = find_in_sigtab env lid  in
         match uu____16712 with
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
      let uu____16793 = lookup_qname env lid  in
      match uu____16793 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16814,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16928 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16928 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16973 =
          let uu____16976 = lookup_attr env1 attr  in se1 :: uu____16976  in
        FStar_Util.smap_add (attrtab env1) attr uu____16973  in
      FStar_List.iter
        (fun attr  ->
           let uu____16986 =
             let uu____16987 = FStar_Syntax_Subst.compress attr  in
             uu____16987.FStar_Syntax_Syntax.n  in
           match uu____16986 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16991 =
                 let uu____16993 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16993.FStar_Ident.str  in
               add_one1 env se uu____16991
           | uu____16994 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17017) ->
          add_sigelts env ses
      | uu____17026 ->
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
        (fun uu___4_17064  ->
           match uu___4_17064 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17082 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17144,lb::[]),uu____17146) ->
            let uu____17155 =
              let uu____17164 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17173 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17164, uu____17173)  in
            FStar_Pervasives_Native.Some uu____17155
        | FStar_Syntax_Syntax.Sig_let ((uu____17186,lbs),uu____17188) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17220 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17233 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17233
                     then
                       let uu____17246 =
                         let uu____17255 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17264 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17255, uu____17264)  in
                       FStar_Pervasives_Native.Some uu____17246
                     else FStar_Pervasives_Native.None)
        | uu____17287 -> FStar_Pervasives_Native.None
  
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
                    let uu____17379 =
                      let uu____17381 =
                        let uu____17383 =
                          let uu____17385 =
                            let uu____17387 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17393 =
                              let uu____17395 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17395  in
                            Prims.op_Hat uu____17387 uu____17393  in
                          Prims.op_Hat ", expected " uu____17385  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17383
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17381
                       in
                    failwith uu____17379
                  else ());
             (let uu____17402 =
                let uu____17411 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17411, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17402))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17431,uu____17432) ->
            let uu____17437 =
              let uu____17446 =
                let uu____17451 =
                  let uu____17452 =
                    let uu____17455 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17455  in
                  (us, uu____17452)  in
                inst_ts us_opt uu____17451  in
              (uu____17446, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17437
        | uu____17474 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17563 =
          match uu____17563 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17659,uvs,t,uu____17662,uu____17663,uu____17664);
                      FStar_Syntax_Syntax.sigrng = uu____17665;
                      FStar_Syntax_Syntax.sigquals = uu____17666;
                      FStar_Syntax_Syntax.sigmeta = uu____17667;
                      FStar_Syntax_Syntax.sigattrs = uu____17668;
                      FStar_Syntax_Syntax.sigopts = uu____17669;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17694 =
                     let uu____17703 = inst_tscheme1 (uvs, t)  in
                     (uu____17703, rng)  in
                   FStar_Pervasives_Native.Some uu____17694
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17727;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17729;
                      FStar_Syntax_Syntax.sigattrs = uu____17730;
                      FStar_Syntax_Syntax.sigopts = uu____17731;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17750 =
                     let uu____17752 = in_cur_mod env l  in uu____17752 = Yes
                      in
                   if uu____17750
                   then
                     let uu____17764 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17764
                      then
                        let uu____17780 =
                          let uu____17789 = inst_tscheme1 (uvs, t)  in
                          (uu____17789, rng)  in
                        FStar_Pervasives_Native.Some uu____17780
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17822 =
                        let uu____17831 = inst_tscheme1 (uvs, t)  in
                        (uu____17831, rng)  in
                      FStar_Pervasives_Native.Some uu____17822)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17856,uu____17857);
                      FStar_Syntax_Syntax.sigrng = uu____17858;
                      FStar_Syntax_Syntax.sigquals = uu____17859;
                      FStar_Syntax_Syntax.sigmeta = uu____17860;
                      FStar_Syntax_Syntax.sigattrs = uu____17861;
                      FStar_Syntax_Syntax.sigopts = uu____17862;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17905 =
                          let uu____17914 = inst_tscheme1 (uvs, k)  in
                          (uu____17914, rng)  in
                        FStar_Pervasives_Native.Some uu____17905
                    | uu____17935 ->
                        let uu____17936 =
                          let uu____17945 =
                            let uu____17950 =
                              let uu____17951 =
                                let uu____17954 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17954
                                 in
                              (uvs, uu____17951)  in
                            inst_tscheme1 uu____17950  in
                          (uu____17945, rng)  in
                        FStar_Pervasives_Native.Some uu____17936)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17977,uu____17978);
                      FStar_Syntax_Syntax.sigrng = uu____17979;
                      FStar_Syntax_Syntax.sigquals = uu____17980;
                      FStar_Syntax_Syntax.sigmeta = uu____17981;
                      FStar_Syntax_Syntax.sigattrs = uu____17982;
                      FStar_Syntax_Syntax.sigopts = uu____17983;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18027 =
                          let uu____18036 = inst_tscheme_with (uvs, k) us  in
                          (uu____18036, rng)  in
                        FStar_Pervasives_Native.Some uu____18027
                    | uu____18057 ->
                        let uu____18058 =
                          let uu____18067 =
                            let uu____18072 =
                              let uu____18073 =
                                let uu____18076 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18076
                                 in
                              (uvs, uu____18073)  in
                            inst_tscheme_with uu____18072 us  in
                          (uu____18067, rng)  in
                        FStar_Pervasives_Native.Some uu____18058)
               | FStar_Util.Inr se ->
                   let uu____18112 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18133;
                          FStar_Syntax_Syntax.sigrng = uu____18134;
                          FStar_Syntax_Syntax.sigquals = uu____18135;
                          FStar_Syntax_Syntax.sigmeta = uu____18136;
                          FStar_Syntax_Syntax.sigattrs = uu____18137;
                          FStar_Syntax_Syntax.sigopts = uu____18138;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18155 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18112
                     (FStar_Util.map_option
                        (fun uu____18203  ->
                           match uu____18203 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18234 =
          let uu____18245 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18245 mapper  in
        match uu____18234 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18319 =
              let uu____18330 =
                let uu____18337 =
                  let uu___846_18340 = t  in
                  let uu____18341 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___846_18340.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18341;
                    FStar_Syntax_Syntax.vars =
                      (uu___846_18340.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18337)  in
              (uu____18330, r)  in
            FStar_Pervasives_Native.Some uu____18319
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18390 = lookup_qname env l  in
      match uu____18390 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18411 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18465 = try_lookup_bv env bv  in
      match uu____18465 with
      | FStar_Pervasives_Native.None  ->
          let uu____18480 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18480 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18496 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18497 =
            let uu____18498 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18498  in
          (uu____18496, uu____18497)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18520 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18520 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18586 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18586  in
          let uu____18587 =
            let uu____18596 =
              let uu____18601 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18601)  in
            (uu____18596, r1)  in
          FStar_Pervasives_Native.Some uu____18587
  
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
        let uu____18636 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18636 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18669,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18694 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18694  in
            let uu____18695 =
              let uu____18700 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18700, r1)  in
            FStar_Pervasives_Native.Some uu____18695
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18724 = try_lookup_lid env l  in
      match uu____18724 with
      | FStar_Pervasives_Native.None  ->
          let uu____18751 = name_not_found l  in
          let uu____18757 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18751 uu____18757
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18800  ->
              match uu___5_18800 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18804 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18825 = lookup_qname env lid  in
      match uu____18825 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18834,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18837;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18839;
              FStar_Syntax_Syntax.sigattrs = uu____18840;
              FStar_Syntax_Syntax.sigopts = uu____18841;_},FStar_Pervasives_Native.None
            ),uu____18842)
          ->
          let uu____18893 =
            let uu____18900 =
              let uu____18901 =
                let uu____18904 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18904 t  in
              (uvs, uu____18901)  in
            (uu____18900, q)  in
          FStar_Pervasives_Native.Some uu____18893
      | uu____18917 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18939 = lookup_qname env lid  in
      match uu____18939 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18944,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18947;
              FStar_Syntax_Syntax.sigquals = uu____18948;
              FStar_Syntax_Syntax.sigmeta = uu____18949;
              FStar_Syntax_Syntax.sigattrs = uu____18950;
              FStar_Syntax_Syntax.sigopts = uu____18951;_},FStar_Pervasives_Native.None
            ),uu____18952)
          ->
          let uu____19003 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19003 (uvs, t)
      | uu____19008 ->
          let uu____19009 = name_not_found lid  in
          let uu____19015 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19009 uu____19015
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19035 = lookup_qname env lid  in
      match uu____19035 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19040,uvs,t,uu____19043,uu____19044,uu____19045);
              FStar_Syntax_Syntax.sigrng = uu____19046;
              FStar_Syntax_Syntax.sigquals = uu____19047;
              FStar_Syntax_Syntax.sigmeta = uu____19048;
              FStar_Syntax_Syntax.sigattrs = uu____19049;
              FStar_Syntax_Syntax.sigopts = uu____19050;_},FStar_Pervasives_Native.None
            ),uu____19051)
          ->
          let uu____19108 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19108 (uvs, t)
      | uu____19113 ->
          let uu____19114 = name_not_found lid  in
          let uu____19120 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19114 uu____19120
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19143 = lookup_qname env lid  in
      match uu____19143 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19151,uu____19152,uu____19153,uu____19154,uu____19155,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19157;
              FStar_Syntax_Syntax.sigquals = uu____19158;
              FStar_Syntax_Syntax.sigmeta = uu____19159;
              FStar_Syntax_Syntax.sigattrs = uu____19160;
              FStar_Syntax_Syntax.sigopts = uu____19161;_},uu____19162),uu____19163)
          -> (true, dcs)
      | uu____19228 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19244 = lookup_qname env lid  in
      match uu____19244 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19245,uu____19246,uu____19247,l,uu____19249,uu____19250);
              FStar_Syntax_Syntax.sigrng = uu____19251;
              FStar_Syntax_Syntax.sigquals = uu____19252;
              FStar_Syntax_Syntax.sigmeta = uu____19253;
              FStar_Syntax_Syntax.sigattrs = uu____19254;
              FStar_Syntax_Syntax.sigopts = uu____19255;_},uu____19256),uu____19257)
          -> l
      | uu____19316 ->
          let uu____19317 =
            let uu____19319 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19319  in
          failwith uu____19317
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19389)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19446) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19470 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19470
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19505 -> FStar_Pervasives_Native.None)
          | uu____19514 -> FStar_Pervasives_Native.None
  
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
        let uu____19576 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19576
  
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
        let uu____19609 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19609
  
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
             (FStar_Util.Inl uu____19661,uu____19662) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19711),uu____19712) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19761 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19779 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19789 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19806 ->
                  let uu____19813 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19813
              | FStar_Syntax_Syntax.Sig_let ((uu____19814,lbs),uu____19816)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19832 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19832
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19839 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19847 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19848 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19855 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19856 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19857 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19870 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____19871 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19899 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19899
           (fun d_opt  ->
              let uu____19912 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19912
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19922 =
                   let uu____19925 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19925  in
                 match uu____19922 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19926 =
                       let uu____19928 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19928
                        in
                     failwith uu____19926
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19933 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19933
                       then
                         let uu____19936 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19938 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19940 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19936 uu____19938 uu____19940
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
        (FStar_Util.Inr (se,uu____19965),uu____19966) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20015 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20037),uu____20038) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20087 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20109 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20109
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20142 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20142 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20164 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20173 =
                        let uu____20174 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20174.FStar_Syntax_Syntax.n  in
                      match uu____20173 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20179 -> false))
               in
            (true, uu____20164)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20202 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20202
  
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
          let uu____20274 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20274.FStar_Ident.str  in
        let uu____20275 = FStar_Util.smap_try_find tab s  in
        match uu____20275 with
        | FStar_Pervasives_Native.None  ->
            let uu____20278 = f ()  in
            (match uu____20278 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20316 =
        let uu____20317 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20317 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20351 =
        let uu____20352 = FStar_Syntax_Util.unrefine t  in
        uu____20352.FStar_Syntax_Syntax.n  in
      match uu____20351 with
      | FStar_Syntax_Syntax.Tm_type uu____20356 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20360) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20386) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20391,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20413 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20446 =
        let attrs =
          let uu____20452 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20452  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20492 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20492)
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
      let uu____20537 = lookup_qname env ftv  in
      match uu____20537 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20541) ->
          let uu____20586 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20586 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20607,t),r) ->
               let uu____20622 =
                 let uu____20623 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20623 t  in
               FStar_Pervasives_Native.Some uu____20622)
      | uu____20624 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20636 = try_lookup_effect_lid env ftv  in
      match uu____20636 with
      | FStar_Pervasives_Native.None  ->
          let uu____20639 = name_not_found ftv  in
          let uu____20645 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20639 uu____20645
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
        let uu____20669 = lookup_qname env lid0  in
        match uu____20669 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20680);
                FStar_Syntax_Syntax.sigrng = uu____20681;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____20683;
                FStar_Syntax_Syntax.sigattrs = uu____20684;
                FStar_Syntax_Syntax.sigopts = uu____20685;_},FStar_Pervasives_Native.None
              ),uu____20686)
            ->
            let lid1 =
              let uu____20742 =
                let uu____20743 = FStar_Ident.range_of_lid lid  in
                let uu____20744 =
                  let uu____20745 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20745  in
                FStar_Range.set_use_range uu____20743 uu____20744  in
              FStar_Ident.set_lid_range lid uu____20742  in
            let uu____20746 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20752  ->
                      match uu___6_20752 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20755 -> false))
               in
            if uu____20746
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20774 =
                      let uu____20776 =
                        let uu____20778 = get_range env  in
                        FStar_Range.string_of_range uu____20778  in
                      let uu____20779 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20781 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20776 uu____20779 uu____20781
                       in
                    failwith uu____20774)
                  in
               match (binders, univs1) with
               | ([],uu____20802) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20828,uu____20829::uu____20830::uu____20831) ->
                   let uu____20852 =
                     let uu____20854 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20856 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20854 uu____20856
                      in
                   failwith uu____20852
               | uu____20867 ->
                   let uu____20882 =
                     let uu____20887 =
                       let uu____20888 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20888)  in
                     inst_tscheme_with uu____20887 insts  in
                   (match uu____20882 with
                    | (uu____20901,t) ->
                        let t1 =
                          let uu____20904 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20904 t  in
                        let uu____20905 =
                          let uu____20906 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20906.FStar_Syntax_Syntax.n  in
                        (match uu____20905 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20941 -> failwith "Impossible")))
        | uu____20949 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20973 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20973 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20986,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20993 = find1 l2  in
            (match uu____20993 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21000 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____21000 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21004 = find1 l  in
            (match uu____21004 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____21009 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21009
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21030 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____21030 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21036) ->
            FStar_List.length bs
        | uu____21075 ->
            let uu____21076 =
              let uu____21082 =
                let uu____21084 = FStar_Ident.string_of_lid name  in
                let uu____21086 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21084 uu____21086
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21082)
               in
            FStar_Errors.raise_error uu____21076 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21105 = lookup_qname env l1  in
      match uu____21105 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21108;
              FStar_Syntax_Syntax.sigrng = uu____21109;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21111;
              FStar_Syntax_Syntax.sigattrs = uu____21112;
              FStar_Syntax_Syntax.sigopts = uu____21113;_},uu____21114),uu____21115)
          -> q
      | uu____21168 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21192 =
          let uu____21193 =
            let uu____21195 = FStar_Util.string_of_int i  in
            let uu____21197 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21195 uu____21197
             in
          failwith uu____21193  in
        let uu____21200 = lookup_datacon env lid  in
        match uu____21200 with
        | (uu____21205,t) ->
            let uu____21207 =
              let uu____21208 = FStar_Syntax_Subst.compress t  in
              uu____21208.FStar_Syntax_Syntax.n  in
            (match uu____21207 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21212) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21256 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21256
                      FStar_Pervasives_Native.fst)
             | uu____21267 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21281 = lookup_qname env l  in
      match uu____21281 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21283,uu____21284,uu____21285);
              FStar_Syntax_Syntax.sigrng = uu____21286;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21288;
              FStar_Syntax_Syntax.sigattrs = uu____21289;
              FStar_Syntax_Syntax.sigopts = uu____21290;_},uu____21291),uu____21292)
          ->
          FStar_Util.for_some
            (fun uu___7_21347  ->
               match uu___7_21347 with
               | FStar_Syntax_Syntax.Projector uu____21349 -> true
               | uu____21355 -> false) quals
      | uu____21357 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21371 = lookup_qname env lid  in
      match uu____21371 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21373,uu____21374,uu____21375,uu____21376,uu____21377,uu____21378);
              FStar_Syntax_Syntax.sigrng = uu____21379;
              FStar_Syntax_Syntax.sigquals = uu____21380;
              FStar_Syntax_Syntax.sigmeta = uu____21381;
              FStar_Syntax_Syntax.sigattrs = uu____21382;
              FStar_Syntax_Syntax.sigopts = uu____21383;_},uu____21384),uu____21385)
          -> true
      | uu____21445 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21459 = lookup_qname env lid  in
      match uu____21459 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21461,uu____21462,uu____21463,uu____21464,uu____21465,uu____21466);
              FStar_Syntax_Syntax.sigrng = uu____21467;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21469;
              FStar_Syntax_Syntax.sigattrs = uu____21470;
              FStar_Syntax_Syntax.sigopts = uu____21471;_},uu____21472),uu____21473)
          ->
          FStar_Util.for_some
            (fun uu___8_21536  ->
               match uu___8_21536 with
               | FStar_Syntax_Syntax.RecordType uu____21538 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21548 -> true
               | uu____21558 -> false) quals
      | uu____21560 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21570,uu____21571);
            FStar_Syntax_Syntax.sigrng = uu____21572;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21574;
            FStar_Syntax_Syntax.sigattrs = uu____21575;
            FStar_Syntax_Syntax.sigopts = uu____21576;_},uu____21577),uu____21578)
        ->
        FStar_Util.for_some
          (fun uu___9_21637  ->
             match uu___9_21637 with
             | FStar_Syntax_Syntax.Action uu____21639 -> true
             | uu____21641 -> false) quals
    | uu____21643 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21657 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21657
  
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
      let uu____21674 =
        let uu____21675 = FStar_Syntax_Util.un_uinst head1  in
        uu____21675.FStar_Syntax_Syntax.n  in
      match uu____21674 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21681 ->
               true
           | uu____21684 -> false)
      | uu____21686 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21700 = lookup_qname env l  in
      match uu____21700 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____21703),uu____21704) ->
          FStar_Util.for_some
            (fun uu___10_21752  ->
               match uu___10_21752 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____21755 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____21757 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21833 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21851) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21869 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21877 ->
                 FStar_Pervasives_Native.Some true
             | uu____21896 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21899 =
        let uu____21903 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21903 mapper  in
      match uu____21899 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21963 = lookup_qname env lid  in
      match uu____21963 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21967,uu____21968,tps,uu____21970,uu____21971,uu____21972);
              FStar_Syntax_Syntax.sigrng = uu____21973;
              FStar_Syntax_Syntax.sigquals = uu____21974;
              FStar_Syntax_Syntax.sigmeta = uu____21975;
              FStar_Syntax_Syntax.sigattrs = uu____21976;
              FStar_Syntax_Syntax.sigopts = uu____21977;_},uu____21978),uu____21979)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22047 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22093  ->
              match uu____22093 with
              | (d,uu____22102) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____22118 = effect_decl_opt env l  in
      match uu____22118 with
      | FStar_Pervasives_Native.None  ->
          let uu____22133 = name_not_found l  in
          let uu____22139 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22133 uu____22139
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22167 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____22167 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22174  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22188  ->
            fun uu____22189  -> fun e  -> FStar_Util.return_all e))
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
        let uu____22223 = FStar_Ident.lid_equals l1 l2  in
        if uu____22223
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____22242 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22242
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____22261 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22314  ->
                        match uu____22314 with
                        | (m1,m2,uu____22328,uu____22329,uu____22330) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22261 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____22355,uu____22356,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22404 = join_opt env l1 l2  in
        match uu____22404 with
        | FStar_Pervasives_Native.None  ->
            let uu____22425 =
              let uu____22431 =
                let uu____22433 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____22435 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____22433 uu____22435
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22431)  in
            FStar_Errors.raise_error uu____22425 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22478 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22478
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
  'Auu____22498 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22498) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22527 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22553  ->
                match uu____22553 with
                | (d,uu____22560) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22527 with
      | FStar_Pervasives_Native.None  ->
          let uu____22571 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22571
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22586 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22586 with
           | (uu____22597,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22615)::(wp,uu____22617)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22673 -> failwith "Impossible"))
  
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
        | uu____22738 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22751 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22751 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22768 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22768 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____22793 =
                     let uu____22799 =
                       let uu____22801 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22809 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____22820 =
                         let uu____22822 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22822  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22801 uu____22809 uu____22820
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22799)
                      in
                   FStar_Errors.raise_error uu____22793
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22830 =
                     let uu____22841 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22841 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22878  ->
                        fun uu____22879  ->
                          match (uu____22878, uu____22879) with
                          | ((x,uu____22909),(t,uu____22911)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22830
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22942 =
                     let uu___1600_22943 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1600_22943.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1600_22943.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1600_22943.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1600_22943.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22942
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22955 .
    'Auu____22955 ->
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
            let uu____22996 =
              let uu____23003 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____23003)  in
            match uu____22996 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23027 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23029 = FStar_Util.string_of_int given  in
                     let uu____23031 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23027 uu____23029 uu____23031
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23036 = effect_decl_opt env effect_name  in
          match uu____23036 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23058) ->
              let uu____23069 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23069 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23087 =
                       let uu____23090 = get_range env  in
                       let uu____23091 =
                         let uu____23098 =
                           let uu____23099 =
                             let uu____23116 =
                               let uu____23127 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23127 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23116)  in
                           FStar_Syntax_Syntax.Tm_app uu____23099  in
                         FStar_Syntax_Syntax.mk uu____23098  in
                       uu____23091 FStar_Pervasives_Native.None uu____23090
                        in
                     FStar_Pervasives_Native.Some uu____23087)))
  
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
           (fun uu___11_23227  ->
              match uu___11_23227 with
              | FStar_Syntax_Syntax.Reflectable uu____23229 -> true
              | uu____23231 -> false))
  
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
      | uu____23291 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23306 =
        let uu____23307 = FStar_Syntax_Subst.compress t  in
        uu____23307.FStar_Syntax_Syntax.n  in
      match uu____23306 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23311,c) ->
          is_reifiable_comp env c
      | uu____23333 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23353 =
           let uu____23355 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23355  in
         if uu____23353
         then
           let uu____23358 =
             let uu____23364 =
               let uu____23366 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23366
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23364)  in
           let uu____23370 = get_range env  in
           FStar_Errors.raise_error uu____23358 uu____23370
         else ());
        (let uu____23373 = effect_repr_aux true env c u_c  in
         match uu____23373 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1677_23409 = env  in
        {
          solver = (uu___1677_23409.solver);
          range = (uu___1677_23409.range);
          curmodule = (uu___1677_23409.curmodule);
          gamma = (uu___1677_23409.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1677_23409.gamma_cache);
          modules = (uu___1677_23409.modules);
          expected_typ = (uu___1677_23409.expected_typ);
          sigtab = (uu___1677_23409.sigtab);
          attrtab = (uu___1677_23409.attrtab);
          instantiate_imp = (uu___1677_23409.instantiate_imp);
          effects = (uu___1677_23409.effects);
          generalize = (uu___1677_23409.generalize);
          letrecs = (uu___1677_23409.letrecs);
          top_level = (uu___1677_23409.top_level);
          check_uvars = (uu___1677_23409.check_uvars);
          use_eq = (uu___1677_23409.use_eq);
          is_iface = (uu___1677_23409.is_iface);
          admit = (uu___1677_23409.admit);
          lax = (uu___1677_23409.lax);
          lax_universes = (uu___1677_23409.lax_universes);
          phase1 = (uu___1677_23409.phase1);
          failhard = (uu___1677_23409.failhard);
          nosynth = (uu___1677_23409.nosynth);
          uvar_subtyping = (uu___1677_23409.uvar_subtyping);
          tc_term = (uu___1677_23409.tc_term);
          type_of = (uu___1677_23409.type_of);
          universe_of = (uu___1677_23409.universe_of);
          check_type_of = (uu___1677_23409.check_type_of);
          use_bv_sorts = (uu___1677_23409.use_bv_sorts);
          qtbl_name_and_index = (uu___1677_23409.qtbl_name_and_index);
          normalized_eff_names = (uu___1677_23409.normalized_eff_names);
          fv_delta_depths = (uu___1677_23409.fv_delta_depths);
          proof_ns = (uu___1677_23409.proof_ns);
          synth_hook = (uu___1677_23409.synth_hook);
          splice = (uu___1677_23409.splice);
          mpreprocess = (uu___1677_23409.mpreprocess);
          postprocess = (uu___1677_23409.postprocess);
          is_native_tactic = (uu___1677_23409.is_native_tactic);
          identifier_info = (uu___1677_23409.identifier_info);
          tc_hooks = (uu___1677_23409.tc_hooks);
          dsenv = (uu___1677_23409.dsenv);
          nbe = (uu___1677_23409.nbe);
          strict_args_tab = (uu___1677_23409.strict_args_tab);
          erasable_types_tab = (uu___1677_23409.erasable_types_tab)
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
    fun uu____23428  ->
      match uu____23428 with
      | (ed,quals) ->
          let effects =
            let uu___1686_23442 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1686_23442.order);
              joins = (uu___1686_23442.joins);
              polymonadic_binds = (uu___1686_23442.polymonadic_binds)
            }  in
          let uu___1689_23451 = env  in
          {
            solver = (uu___1689_23451.solver);
            range = (uu___1689_23451.range);
            curmodule = (uu___1689_23451.curmodule);
            gamma = (uu___1689_23451.gamma);
            gamma_sig = (uu___1689_23451.gamma_sig);
            gamma_cache = (uu___1689_23451.gamma_cache);
            modules = (uu___1689_23451.modules);
            expected_typ = (uu___1689_23451.expected_typ);
            sigtab = (uu___1689_23451.sigtab);
            attrtab = (uu___1689_23451.attrtab);
            instantiate_imp = (uu___1689_23451.instantiate_imp);
            effects;
            generalize = (uu___1689_23451.generalize);
            letrecs = (uu___1689_23451.letrecs);
            top_level = (uu___1689_23451.top_level);
            check_uvars = (uu___1689_23451.check_uvars);
            use_eq = (uu___1689_23451.use_eq);
            is_iface = (uu___1689_23451.is_iface);
            admit = (uu___1689_23451.admit);
            lax = (uu___1689_23451.lax);
            lax_universes = (uu___1689_23451.lax_universes);
            phase1 = (uu___1689_23451.phase1);
            failhard = (uu___1689_23451.failhard);
            nosynth = (uu___1689_23451.nosynth);
            uvar_subtyping = (uu___1689_23451.uvar_subtyping);
            tc_term = (uu___1689_23451.tc_term);
            type_of = (uu___1689_23451.type_of);
            universe_of = (uu___1689_23451.universe_of);
            check_type_of = (uu___1689_23451.check_type_of);
            use_bv_sorts = (uu___1689_23451.use_bv_sorts);
            qtbl_name_and_index = (uu___1689_23451.qtbl_name_and_index);
            normalized_eff_names = (uu___1689_23451.normalized_eff_names);
            fv_delta_depths = (uu___1689_23451.fv_delta_depths);
            proof_ns = (uu___1689_23451.proof_ns);
            synth_hook = (uu___1689_23451.synth_hook);
            splice = (uu___1689_23451.splice);
            mpreprocess = (uu___1689_23451.mpreprocess);
            postprocess = (uu___1689_23451.postprocess);
            is_native_tactic = (uu___1689_23451.is_native_tactic);
            identifier_info = (uu___1689_23451.identifier_info);
            tc_hooks = (uu___1689_23451.tc_hooks);
            dsenv = (uu___1689_23451.dsenv);
            nbe = (uu___1689_23451.nbe);
            strict_args_tab = (uu___1689_23451.strict_args_tab);
            erasable_types_tab = (uu___1689_23451.erasable_types_tab)
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
        let uu____23480 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____23548  ->
                  match uu____23548 with
                  | (m1,n11,uu____23566,uu____23567) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____23480 with
        | FStar_Pervasives_Native.Some (uu____23592,uu____23593,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____23638 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____23713 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____23713
                  (fun uu____23734  ->
                     match uu____23734 with
                     | (c1,g1) ->
                         let uu____23745 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____23745
                           (fun uu____23766  ->
                              match uu____23766 with
                              | (c2,g2) ->
                                  let uu____23777 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____23777)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____23899 = l1 u t e  in
                              l2 u t uu____23899))
                | uu____23900 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____23968  ->
                    match uu____23968 with
                    | (e,uu____23976) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____23999 =
            match uu____23999 with
            | (i,j) ->
                let uu____24010 = FStar_Ident.lid_equals i j  in
                if uu____24010
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _24017  -> FStar_Pervasives_Native.Some _24017)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24046 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24056 = FStar_Ident.lid_equals i k  in
                        if uu____24056
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24070 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24070
                                  then []
                                  else
                                    (let uu____24077 =
                                       let uu____24086 =
                                         find_edge order1 (i, k)  in
                                       let uu____24089 =
                                         find_edge order1 (k, j)  in
                                       (uu____24086, uu____24089)  in
                                     match uu____24077 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24104 =
                                           compose_edges e1 e2  in
                                         [uu____24104]
                                     | uu____24105 -> [])))))
                 in
              FStar_List.append order1 uu____24046  in
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
                  let uu____24135 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24138 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____24138
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24135
                  then
                    let uu____24145 =
                      let uu____24151 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24151)
                       in
                    let uu____24155 = get_range env  in
                    FStar_Errors.raise_error uu____24145 uu____24155
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____24233 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24233
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24285 =
                                             let uu____24294 =
                                               find_edge order2 (i, k)  in
                                             let uu____24297 =
                                               find_edge order2 (j, k)  in
                                             (uu____24294, uu____24297)  in
                                           match uu____24285 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____24339,uu____24340)
                                                    ->
                                                    let uu____24347 =
                                                      let uu____24354 =
                                                        let uu____24356 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24356
                                                         in
                                                      let uu____24359 =
                                                        let uu____24361 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24361
                                                         in
                                                      (uu____24354,
                                                        uu____24359)
                                                       in
                                                    (match uu____24347 with
                                                     | (true ,true ) ->
                                                         let uu____24378 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____24378
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
                                           | uu____24421 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____24473 =
                                   let uu____24475 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____24475
                                     FStar_Util.is_some
                                    in
                                 if uu____24473
                                 then
                                   let uu____24524 =
                                     let uu____24530 =
                                       let uu____24532 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____24534 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____24536 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____24538 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____24532 uu____24534 uu____24536
                                         uu____24538
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____24530)
                                      in
                                   FStar_Errors.raise_error uu____24524
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1810_24577 = env.effects  in
             {
               decls = (uu___1810_24577.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1810_24577.polymonadic_binds)
             }  in
           let uu___1813_24578 = env  in
           {
             solver = (uu___1813_24578.solver);
             range = (uu___1813_24578.range);
             curmodule = (uu___1813_24578.curmodule);
             gamma = (uu___1813_24578.gamma);
             gamma_sig = (uu___1813_24578.gamma_sig);
             gamma_cache = (uu___1813_24578.gamma_cache);
             modules = (uu___1813_24578.modules);
             expected_typ = (uu___1813_24578.expected_typ);
             sigtab = (uu___1813_24578.sigtab);
             attrtab = (uu___1813_24578.attrtab);
             instantiate_imp = (uu___1813_24578.instantiate_imp);
             effects;
             generalize = (uu___1813_24578.generalize);
             letrecs = (uu___1813_24578.letrecs);
             top_level = (uu___1813_24578.top_level);
             check_uvars = (uu___1813_24578.check_uvars);
             use_eq = (uu___1813_24578.use_eq);
             is_iface = (uu___1813_24578.is_iface);
             admit = (uu___1813_24578.admit);
             lax = (uu___1813_24578.lax);
             lax_universes = (uu___1813_24578.lax_universes);
             phase1 = (uu___1813_24578.phase1);
             failhard = (uu___1813_24578.failhard);
             nosynth = (uu___1813_24578.nosynth);
             uvar_subtyping = (uu___1813_24578.uvar_subtyping);
             tc_term = (uu___1813_24578.tc_term);
             type_of = (uu___1813_24578.type_of);
             universe_of = (uu___1813_24578.universe_of);
             check_type_of = (uu___1813_24578.check_type_of);
             use_bv_sorts = (uu___1813_24578.use_bv_sorts);
             qtbl_name_and_index = (uu___1813_24578.qtbl_name_and_index);
             normalized_eff_names = (uu___1813_24578.normalized_eff_names);
             fv_delta_depths = (uu___1813_24578.fv_delta_depths);
             proof_ns = (uu___1813_24578.proof_ns);
             synth_hook = (uu___1813_24578.synth_hook);
             splice = (uu___1813_24578.splice);
             mpreprocess = (uu___1813_24578.mpreprocess);
             postprocess = (uu___1813_24578.postprocess);
             is_native_tactic = (uu___1813_24578.is_native_tactic);
             identifier_info = (uu___1813_24578.identifier_info);
             tc_hooks = (uu___1813_24578.tc_hooks);
             dsenv = (uu___1813_24578.dsenv);
             nbe = (uu___1813_24578.nbe);
             strict_args_tab = (uu___1813_24578.strict_args_tab);
             erasable_types_tab = (uu___1813_24578.erasable_types_tab)
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
              let uu____24626 = FStar_Ident.string_of_lid m  in
              let uu____24628 = FStar_Ident.string_of_lid n1  in
              let uu____24630 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____24626 uu____24628 uu____24630
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____24639 =
              let uu____24641 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____24641 FStar_Util.is_some  in
            if uu____24639
            then
              let uu____24678 =
                let uu____24684 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____24684)
                 in
              FStar_Errors.raise_error uu____24678 env.range
            else
              (let uu____24690 =
                 let uu____24692 = join_opt env m n1  in
                 FStar_All.pipe_right uu____24692 FStar_Util.is_some  in
               if uu____24690
               then
                 let uu____24717 =
                   let uu____24723 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____24723)
                    in
                 FStar_Errors.raise_error uu____24717 env.range
               else
                 (let uu___1828_24729 = env  in
                  {
                    solver = (uu___1828_24729.solver);
                    range = (uu___1828_24729.range);
                    curmodule = (uu___1828_24729.curmodule);
                    gamma = (uu___1828_24729.gamma);
                    gamma_sig = (uu___1828_24729.gamma_sig);
                    gamma_cache = (uu___1828_24729.gamma_cache);
                    modules = (uu___1828_24729.modules);
                    expected_typ = (uu___1828_24729.expected_typ);
                    sigtab = (uu___1828_24729.sigtab);
                    attrtab = (uu___1828_24729.attrtab);
                    instantiate_imp = (uu___1828_24729.instantiate_imp);
                    effects =
                      (let uu___1830_24731 = env.effects  in
                       {
                         decls = (uu___1830_24731.decls);
                         order = (uu___1830_24731.order);
                         joins = (uu___1830_24731.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1828_24729.generalize);
                    letrecs = (uu___1828_24729.letrecs);
                    top_level = (uu___1828_24729.top_level);
                    check_uvars = (uu___1828_24729.check_uvars);
                    use_eq = (uu___1828_24729.use_eq);
                    is_iface = (uu___1828_24729.is_iface);
                    admit = (uu___1828_24729.admit);
                    lax = (uu___1828_24729.lax);
                    lax_universes = (uu___1828_24729.lax_universes);
                    phase1 = (uu___1828_24729.phase1);
                    failhard = (uu___1828_24729.failhard);
                    nosynth = (uu___1828_24729.nosynth);
                    uvar_subtyping = (uu___1828_24729.uvar_subtyping);
                    tc_term = (uu___1828_24729.tc_term);
                    type_of = (uu___1828_24729.type_of);
                    universe_of = (uu___1828_24729.universe_of);
                    check_type_of = (uu___1828_24729.check_type_of);
                    use_bv_sorts = (uu___1828_24729.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1828_24729.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1828_24729.normalized_eff_names);
                    fv_delta_depths = (uu___1828_24729.fv_delta_depths);
                    proof_ns = (uu___1828_24729.proof_ns);
                    synth_hook = (uu___1828_24729.synth_hook);
                    splice = (uu___1828_24729.splice);
                    mpreprocess = (uu___1828_24729.mpreprocess);
                    postprocess = (uu___1828_24729.postprocess);
                    is_native_tactic = (uu___1828_24729.is_native_tactic);
                    identifier_info = (uu___1828_24729.identifier_info);
                    tc_hooks = (uu___1828_24729.tc_hooks);
                    dsenv = (uu___1828_24729.dsenv);
                    nbe = (uu___1828_24729.nbe);
                    strict_args_tab = (uu___1828_24729.strict_args_tab);
                    erasable_types_tab = (uu___1828_24729.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1834_24803 = env  in
      {
        solver = (uu___1834_24803.solver);
        range = (uu___1834_24803.range);
        curmodule = (uu___1834_24803.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1834_24803.gamma_sig);
        gamma_cache = (uu___1834_24803.gamma_cache);
        modules = (uu___1834_24803.modules);
        expected_typ = (uu___1834_24803.expected_typ);
        sigtab = (uu___1834_24803.sigtab);
        attrtab = (uu___1834_24803.attrtab);
        instantiate_imp = (uu___1834_24803.instantiate_imp);
        effects = (uu___1834_24803.effects);
        generalize = (uu___1834_24803.generalize);
        letrecs = (uu___1834_24803.letrecs);
        top_level = (uu___1834_24803.top_level);
        check_uvars = (uu___1834_24803.check_uvars);
        use_eq = (uu___1834_24803.use_eq);
        is_iface = (uu___1834_24803.is_iface);
        admit = (uu___1834_24803.admit);
        lax = (uu___1834_24803.lax);
        lax_universes = (uu___1834_24803.lax_universes);
        phase1 = (uu___1834_24803.phase1);
        failhard = (uu___1834_24803.failhard);
        nosynth = (uu___1834_24803.nosynth);
        uvar_subtyping = (uu___1834_24803.uvar_subtyping);
        tc_term = (uu___1834_24803.tc_term);
        type_of = (uu___1834_24803.type_of);
        universe_of = (uu___1834_24803.universe_of);
        check_type_of = (uu___1834_24803.check_type_of);
        use_bv_sorts = (uu___1834_24803.use_bv_sorts);
        qtbl_name_and_index = (uu___1834_24803.qtbl_name_and_index);
        normalized_eff_names = (uu___1834_24803.normalized_eff_names);
        fv_delta_depths = (uu___1834_24803.fv_delta_depths);
        proof_ns = (uu___1834_24803.proof_ns);
        synth_hook = (uu___1834_24803.synth_hook);
        splice = (uu___1834_24803.splice);
        mpreprocess = (uu___1834_24803.mpreprocess);
        postprocess = (uu___1834_24803.postprocess);
        is_native_tactic = (uu___1834_24803.is_native_tactic);
        identifier_info = (uu___1834_24803.identifier_info);
        tc_hooks = (uu___1834_24803.tc_hooks);
        dsenv = (uu___1834_24803.dsenv);
        nbe = (uu___1834_24803.nbe);
        strict_args_tab = (uu___1834_24803.strict_args_tab);
        erasable_types_tab = (uu___1834_24803.erasable_types_tab)
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
            (let uu___1847_24861 = env  in
             {
               solver = (uu___1847_24861.solver);
               range = (uu___1847_24861.range);
               curmodule = (uu___1847_24861.curmodule);
               gamma = rest;
               gamma_sig = (uu___1847_24861.gamma_sig);
               gamma_cache = (uu___1847_24861.gamma_cache);
               modules = (uu___1847_24861.modules);
               expected_typ = (uu___1847_24861.expected_typ);
               sigtab = (uu___1847_24861.sigtab);
               attrtab = (uu___1847_24861.attrtab);
               instantiate_imp = (uu___1847_24861.instantiate_imp);
               effects = (uu___1847_24861.effects);
               generalize = (uu___1847_24861.generalize);
               letrecs = (uu___1847_24861.letrecs);
               top_level = (uu___1847_24861.top_level);
               check_uvars = (uu___1847_24861.check_uvars);
               use_eq = (uu___1847_24861.use_eq);
               is_iface = (uu___1847_24861.is_iface);
               admit = (uu___1847_24861.admit);
               lax = (uu___1847_24861.lax);
               lax_universes = (uu___1847_24861.lax_universes);
               phase1 = (uu___1847_24861.phase1);
               failhard = (uu___1847_24861.failhard);
               nosynth = (uu___1847_24861.nosynth);
               uvar_subtyping = (uu___1847_24861.uvar_subtyping);
               tc_term = (uu___1847_24861.tc_term);
               type_of = (uu___1847_24861.type_of);
               universe_of = (uu___1847_24861.universe_of);
               check_type_of = (uu___1847_24861.check_type_of);
               use_bv_sorts = (uu___1847_24861.use_bv_sorts);
               qtbl_name_and_index = (uu___1847_24861.qtbl_name_and_index);
               normalized_eff_names = (uu___1847_24861.normalized_eff_names);
               fv_delta_depths = (uu___1847_24861.fv_delta_depths);
               proof_ns = (uu___1847_24861.proof_ns);
               synth_hook = (uu___1847_24861.synth_hook);
               splice = (uu___1847_24861.splice);
               mpreprocess = (uu___1847_24861.mpreprocess);
               postprocess = (uu___1847_24861.postprocess);
               is_native_tactic = (uu___1847_24861.is_native_tactic);
               identifier_info = (uu___1847_24861.identifier_info);
               tc_hooks = (uu___1847_24861.tc_hooks);
               dsenv = (uu___1847_24861.dsenv);
               nbe = (uu___1847_24861.nbe);
               strict_args_tab = (uu___1847_24861.strict_args_tab);
               erasable_types_tab = (uu___1847_24861.erasable_types_tab)
             }))
    | uu____24862 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____24891  ->
             match uu____24891 with | (x,uu____24899) -> push_bv env1 x) env
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
            let uu___1861_24934 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1861_24934.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1861_24934.FStar_Syntax_Syntax.index);
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
        let uu____25007 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25007 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____25035 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25035)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1882_25051 = env  in
      {
        solver = (uu___1882_25051.solver);
        range = (uu___1882_25051.range);
        curmodule = (uu___1882_25051.curmodule);
        gamma = (uu___1882_25051.gamma);
        gamma_sig = (uu___1882_25051.gamma_sig);
        gamma_cache = (uu___1882_25051.gamma_cache);
        modules = (uu___1882_25051.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1882_25051.sigtab);
        attrtab = (uu___1882_25051.attrtab);
        instantiate_imp = (uu___1882_25051.instantiate_imp);
        effects = (uu___1882_25051.effects);
        generalize = (uu___1882_25051.generalize);
        letrecs = (uu___1882_25051.letrecs);
        top_level = (uu___1882_25051.top_level);
        check_uvars = (uu___1882_25051.check_uvars);
        use_eq = false;
        is_iface = (uu___1882_25051.is_iface);
        admit = (uu___1882_25051.admit);
        lax = (uu___1882_25051.lax);
        lax_universes = (uu___1882_25051.lax_universes);
        phase1 = (uu___1882_25051.phase1);
        failhard = (uu___1882_25051.failhard);
        nosynth = (uu___1882_25051.nosynth);
        uvar_subtyping = (uu___1882_25051.uvar_subtyping);
        tc_term = (uu___1882_25051.tc_term);
        type_of = (uu___1882_25051.type_of);
        universe_of = (uu___1882_25051.universe_of);
        check_type_of = (uu___1882_25051.check_type_of);
        use_bv_sorts = (uu___1882_25051.use_bv_sorts);
        qtbl_name_and_index = (uu___1882_25051.qtbl_name_and_index);
        normalized_eff_names = (uu___1882_25051.normalized_eff_names);
        fv_delta_depths = (uu___1882_25051.fv_delta_depths);
        proof_ns = (uu___1882_25051.proof_ns);
        synth_hook = (uu___1882_25051.synth_hook);
        splice = (uu___1882_25051.splice);
        mpreprocess = (uu___1882_25051.mpreprocess);
        postprocess = (uu___1882_25051.postprocess);
        is_native_tactic = (uu___1882_25051.is_native_tactic);
        identifier_info = (uu___1882_25051.identifier_info);
        tc_hooks = (uu___1882_25051.tc_hooks);
        dsenv = (uu___1882_25051.dsenv);
        nbe = (uu___1882_25051.nbe);
        strict_args_tab = (uu___1882_25051.strict_args_tab);
        erasable_types_tab = (uu___1882_25051.erasable_types_tab)
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
    let uu____25082 = expected_typ env_  in
    ((let uu___1889_25088 = env_  in
      {
        solver = (uu___1889_25088.solver);
        range = (uu___1889_25088.range);
        curmodule = (uu___1889_25088.curmodule);
        gamma = (uu___1889_25088.gamma);
        gamma_sig = (uu___1889_25088.gamma_sig);
        gamma_cache = (uu___1889_25088.gamma_cache);
        modules = (uu___1889_25088.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1889_25088.sigtab);
        attrtab = (uu___1889_25088.attrtab);
        instantiate_imp = (uu___1889_25088.instantiate_imp);
        effects = (uu___1889_25088.effects);
        generalize = (uu___1889_25088.generalize);
        letrecs = (uu___1889_25088.letrecs);
        top_level = (uu___1889_25088.top_level);
        check_uvars = (uu___1889_25088.check_uvars);
        use_eq = false;
        is_iface = (uu___1889_25088.is_iface);
        admit = (uu___1889_25088.admit);
        lax = (uu___1889_25088.lax);
        lax_universes = (uu___1889_25088.lax_universes);
        phase1 = (uu___1889_25088.phase1);
        failhard = (uu___1889_25088.failhard);
        nosynth = (uu___1889_25088.nosynth);
        uvar_subtyping = (uu___1889_25088.uvar_subtyping);
        tc_term = (uu___1889_25088.tc_term);
        type_of = (uu___1889_25088.type_of);
        universe_of = (uu___1889_25088.universe_of);
        check_type_of = (uu___1889_25088.check_type_of);
        use_bv_sorts = (uu___1889_25088.use_bv_sorts);
        qtbl_name_and_index = (uu___1889_25088.qtbl_name_and_index);
        normalized_eff_names = (uu___1889_25088.normalized_eff_names);
        fv_delta_depths = (uu___1889_25088.fv_delta_depths);
        proof_ns = (uu___1889_25088.proof_ns);
        synth_hook = (uu___1889_25088.synth_hook);
        splice = (uu___1889_25088.splice);
        mpreprocess = (uu___1889_25088.mpreprocess);
        postprocess = (uu___1889_25088.postprocess);
        is_native_tactic = (uu___1889_25088.is_native_tactic);
        identifier_info = (uu___1889_25088.identifier_info);
        tc_hooks = (uu___1889_25088.tc_hooks);
        dsenv = (uu___1889_25088.dsenv);
        nbe = (uu___1889_25088.nbe);
        strict_args_tab = (uu___1889_25088.strict_args_tab);
        erasable_types_tab = (uu___1889_25088.erasable_types_tab)
      }), uu____25082)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25100 =
      let uu____25103 = FStar_Ident.id_of_text ""  in [uu____25103]  in
    FStar_Ident.lid_of_ids uu____25100  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____25110 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25110
        then
          let uu____25115 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25115 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1897_25143 = env  in
       {
         solver = (uu___1897_25143.solver);
         range = (uu___1897_25143.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1897_25143.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1897_25143.expected_typ);
         sigtab = (uu___1897_25143.sigtab);
         attrtab = (uu___1897_25143.attrtab);
         instantiate_imp = (uu___1897_25143.instantiate_imp);
         effects = (uu___1897_25143.effects);
         generalize = (uu___1897_25143.generalize);
         letrecs = (uu___1897_25143.letrecs);
         top_level = (uu___1897_25143.top_level);
         check_uvars = (uu___1897_25143.check_uvars);
         use_eq = (uu___1897_25143.use_eq);
         is_iface = (uu___1897_25143.is_iface);
         admit = (uu___1897_25143.admit);
         lax = (uu___1897_25143.lax);
         lax_universes = (uu___1897_25143.lax_universes);
         phase1 = (uu___1897_25143.phase1);
         failhard = (uu___1897_25143.failhard);
         nosynth = (uu___1897_25143.nosynth);
         uvar_subtyping = (uu___1897_25143.uvar_subtyping);
         tc_term = (uu___1897_25143.tc_term);
         type_of = (uu___1897_25143.type_of);
         universe_of = (uu___1897_25143.universe_of);
         check_type_of = (uu___1897_25143.check_type_of);
         use_bv_sorts = (uu___1897_25143.use_bv_sorts);
         qtbl_name_and_index = (uu___1897_25143.qtbl_name_and_index);
         normalized_eff_names = (uu___1897_25143.normalized_eff_names);
         fv_delta_depths = (uu___1897_25143.fv_delta_depths);
         proof_ns = (uu___1897_25143.proof_ns);
         synth_hook = (uu___1897_25143.synth_hook);
         splice = (uu___1897_25143.splice);
         mpreprocess = (uu___1897_25143.mpreprocess);
         postprocess = (uu___1897_25143.postprocess);
         is_native_tactic = (uu___1897_25143.is_native_tactic);
         identifier_info = (uu___1897_25143.identifier_info);
         tc_hooks = (uu___1897_25143.tc_hooks);
         dsenv = (uu___1897_25143.dsenv);
         nbe = (uu___1897_25143.nbe);
         strict_args_tab = (uu___1897_25143.strict_args_tab);
         erasable_types_tab = (uu___1897_25143.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25195)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25199,(uu____25200,t)))::tl1
          ->
          let uu____25221 =
            let uu____25224 = FStar_Syntax_Free.uvars t  in
            ext out uu____25224  in
          aux uu____25221 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25227;
            FStar_Syntax_Syntax.index = uu____25228;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25236 =
            let uu____25239 = FStar_Syntax_Free.uvars t  in
            ext out uu____25239  in
          aux uu____25236 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25297)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25301,(uu____25302,t)))::tl1
          ->
          let uu____25323 =
            let uu____25326 = FStar_Syntax_Free.univs t  in
            ext out uu____25326  in
          aux uu____25323 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25329;
            FStar_Syntax_Syntax.index = uu____25330;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25338 =
            let uu____25341 = FStar_Syntax_Free.univs t  in
            ext out uu____25341  in
          aux uu____25338 tl1
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
          let uu____25403 = FStar_Util.set_add uname out  in
          aux uu____25403 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25406,(uu____25407,t)))::tl1
          ->
          let uu____25428 =
            let uu____25431 = FStar_Syntax_Free.univnames t  in
            ext out uu____25431  in
          aux uu____25428 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25434;
            FStar_Syntax_Syntax.index = uu____25435;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25443 =
            let uu____25446 = FStar_Syntax_Free.univnames t  in
            ext out uu____25446  in
          aux uu____25443 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_25467  ->
            match uu___12_25467 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____25471 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____25484 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____25495 =
      let uu____25504 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____25504
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____25495 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____25552 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_25565  ->
              match uu___13_25565 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____25568 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____25568
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____25574) ->
                  let uu____25591 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____25591))
       in
    FStar_All.pipe_right uu____25552 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_25605  ->
    match uu___14_25605 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____25611 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____25611
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____25634  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____25689) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____25722,uu____25723) -> false  in
      let uu____25737 =
        FStar_List.tryFind
          (fun uu____25759  ->
             match uu____25759 with | (p,uu____25770) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____25737 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____25789,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____25819 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____25819
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2040_25841 = e  in
        {
          solver = (uu___2040_25841.solver);
          range = (uu___2040_25841.range);
          curmodule = (uu___2040_25841.curmodule);
          gamma = (uu___2040_25841.gamma);
          gamma_sig = (uu___2040_25841.gamma_sig);
          gamma_cache = (uu___2040_25841.gamma_cache);
          modules = (uu___2040_25841.modules);
          expected_typ = (uu___2040_25841.expected_typ);
          sigtab = (uu___2040_25841.sigtab);
          attrtab = (uu___2040_25841.attrtab);
          instantiate_imp = (uu___2040_25841.instantiate_imp);
          effects = (uu___2040_25841.effects);
          generalize = (uu___2040_25841.generalize);
          letrecs = (uu___2040_25841.letrecs);
          top_level = (uu___2040_25841.top_level);
          check_uvars = (uu___2040_25841.check_uvars);
          use_eq = (uu___2040_25841.use_eq);
          is_iface = (uu___2040_25841.is_iface);
          admit = (uu___2040_25841.admit);
          lax = (uu___2040_25841.lax);
          lax_universes = (uu___2040_25841.lax_universes);
          phase1 = (uu___2040_25841.phase1);
          failhard = (uu___2040_25841.failhard);
          nosynth = (uu___2040_25841.nosynth);
          uvar_subtyping = (uu___2040_25841.uvar_subtyping);
          tc_term = (uu___2040_25841.tc_term);
          type_of = (uu___2040_25841.type_of);
          universe_of = (uu___2040_25841.universe_of);
          check_type_of = (uu___2040_25841.check_type_of);
          use_bv_sorts = (uu___2040_25841.use_bv_sorts);
          qtbl_name_and_index = (uu___2040_25841.qtbl_name_and_index);
          normalized_eff_names = (uu___2040_25841.normalized_eff_names);
          fv_delta_depths = (uu___2040_25841.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2040_25841.synth_hook);
          splice = (uu___2040_25841.splice);
          mpreprocess = (uu___2040_25841.mpreprocess);
          postprocess = (uu___2040_25841.postprocess);
          is_native_tactic = (uu___2040_25841.is_native_tactic);
          identifier_info = (uu___2040_25841.identifier_info);
          tc_hooks = (uu___2040_25841.tc_hooks);
          dsenv = (uu___2040_25841.dsenv);
          nbe = (uu___2040_25841.nbe);
          strict_args_tab = (uu___2040_25841.strict_args_tab);
          erasable_types_tab = (uu___2040_25841.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2049_25889 = e  in
      {
        solver = (uu___2049_25889.solver);
        range = (uu___2049_25889.range);
        curmodule = (uu___2049_25889.curmodule);
        gamma = (uu___2049_25889.gamma);
        gamma_sig = (uu___2049_25889.gamma_sig);
        gamma_cache = (uu___2049_25889.gamma_cache);
        modules = (uu___2049_25889.modules);
        expected_typ = (uu___2049_25889.expected_typ);
        sigtab = (uu___2049_25889.sigtab);
        attrtab = (uu___2049_25889.attrtab);
        instantiate_imp = (uu___2049_25889.instantiate_imp);
        effects = (uu___2049_25889.effects);
        generalize = (uu___2049_25889.generalize);
        letrecs = (uu___2049_25889.letrecs);
        top_level = (uu___2049_25889.top_level);
        check_uvars = (uu___2049_25889.check_uvars);
        use_eq = (uu___2049_25889.use_eq);
        is_iface = (uu___2049_25889.is_iface);
        admit = (uu___2049_25889.admit);
        lax = (uu___2049_25889.lax);
        lax_universes = (uu___2049_25889.lax_universes);
        phase1 = (uu___2049_25889.phase1);
        failhard = (uu___2049_25889.failhard);
        nosynth = (uu___2049_25889.nosynth);
        uvar_subtyping = (uu___2049_25889.uvar_subtyping);
        tc_term = (uu___2049_25889.tc_term);
        type_of = (uu___2049_25889.type_of);
        universe_of = (uu___2049_25889.universe_of);
        check_type_of = (uu___2049_25889.check_type_of);
        use_bv_sorts = (uu___2049_25889.use_bv_sorts);
        qtbl_name_and_index = (uu___2049_25889.qtbl_name_and_index);
        normalized_eff_names = (uu___2049_25889.normalized_eff_names);
        fv_delta_depths = (uu___2049_25889.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2049_25889.synth_hook);
        splice = (uu___2049_25889.splice);
        mpreprocess = (uu___2049_25889.mpreprocess);
        postprocess = (uu___2049_25889.postprocess);
        is_native_tactic = (uu___2049_25889.is_native_tactic);
        identifier_info = (uu___2049_25889.identifier_info);
        tc_hooks = (uu___2049_25889.tc_hooks);
        dsenv = (uu___2049_25889.dsenv);
        nbe = (uu___2049_25889.nbe);
        strict_args_tab = (uu___2049_25889.strict_args_tab);
        erasable_types_tab = (uu___2049_25889.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____25905 = FStar_Syntax_Free.names t  in
      let uu____25908 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____25905 uu____25908
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25931 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25931
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25941 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25941
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25962 =
      match uu____25962 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25982 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25982)
       in
    let uu____25990 =
      let uu____25994 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25994 FStar_List.rev  in
    FStar_All.pipe_right uu____25990 (FStar_String.concat " ")
  
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
                  (let uu____26062 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26062 with
                   | FStar_Pervasives_Native.Some uu____26066 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26069 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26079;
        FStar_TypeChecker_Common.univ_ineqs = uu____26080;
        FStar_TypeChecker_Common.implicits = uu____26081;_} -> true
    | uu____26091 -> false
  
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
          let uu___2093_26113 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2093_26113.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2093_26113.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2093_26113.FStar_TypeChecker_Common.implicits)
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
          let uu____26152 = FStar_Options.defensive ()  in
          if uu____26152
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26158 =
              let uu____26160 =
                let uu____26162 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26162  in
              Prims.op_Negation uu____26160  in
            (if uu____26158
             then
               let uu____26169 =
                 let uu____26175 =
                   let uu____26177 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26179 =
                     let uu____26181 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26181
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26177 uu____26179
                    in
                 (FStar_Errors.Warning_Defensive, uu____26175)  in
               FStar_Errors.log_issue rng uu____26169
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
          let uu____26221 =
            let uu____26223 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26223  in
          if uu____26221
          then ()
          else
            (let uu____26228 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26228 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26254 =
            let uu____26256 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26256  in
          if uu____26254
          then ()
          else
            (let uu____26261 = bound_vars e  in
             def_check_closed_in rng msg uu____26261 t)
  
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
          let uu___2130_26300 = g  in
          let uu____26301 =
            let uu____26302 =
              let uu____26303 =
                let uu____26310 =
                  let uu____26311 =
                    let uu____26328 =
                      let uu____26339 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____26339]  in
                    (f, uu____26328)  in
                  FStar_Syntax_Syntax.Tm_app uu____26311  in
                FStar_Syntax_Syntax.mk uu____26310  in
              uu____26303 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _26376  -> FStar_TypeChecker_Common.NonTrivial _26376)
              uu____26302
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____26301;
            FStar_TypeChecker_Common.deferred =
              (uu___2130_26300.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2130_26300.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2130_26300.FStar_TypeChecker_Common.implicits)
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
          let uu___2137_26394 = g  in
          let uu____26395 =
            let uu____26396 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26396  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26395;
            FStar_TypeChecker_Common.deferred =
              (uu___2137_26394.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2137_26394.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2137_26394.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2142_26413 = g  in
          let uu____26414 =
            let uu____26415 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____26415  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26414;
            FStar_TypeChecker_Common.deferred =
              (uu___2142_26413.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2142_26413.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2142_26413.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2146_26417 = g  in
          let uu____26418 =
            let uu____26419 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26419  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26418;
            FStar_TypeChecker_Common.deferred =
              (uu___2146_26417.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2146_26417.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2146_26417.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____26426 ->
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
                       let uu____26503 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____26503
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2169_26510 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2169_26510.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2169_26510.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2169_26510.FStar_TypeChecker_Common.implicits)
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
               let uu____26544 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____26544
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
            let uu___2184_26571 = g  in
            let uu____26572 =
              let uu____26573 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____26573  in
            {
              FStar_TypeChecker_Common.guard_f = uu____26572;
              FStar_TypeChecker_Common.deferred =
                (uu___2184_26571.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2184_26571.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2184_26571.FStar_TypeChecker_Common.implicits)
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
              let uu____26631 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26631 with
              | FStar_Pervasives_Native.Some
                  (uu____26656::(tm,uu____26658)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____26722 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____26740 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____26740;
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
                      let uu___2206_26772 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2206_26772.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2206_26772.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2206_26772.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____26826 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____26883  ->
                      fun b  ->
                        match uu____26883 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____26925 =
                              let uu____26938 = reason b  in
                              new_implicit_var_aux uu____26938 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____26925 with
                             | (t,uu____26955,g_t) ->
                                 let uu____26969 =
                                   let uu____26972 =
                                     let uu____26975 =
                                       let uu____26976 =
                                         let uu____26983 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____26983, t)  in
                                       FStar_Syntax_Syntax.NT uu____26976  in
                                     [uu____26975]  in
                                   FStar_List.append substs1 uu____26972  in
                                 let uu____26994 = conj_guard g g_t  in
                                 (uu____26969,
                                   (FStar_List.append uvars1 [t]),
                                   uu____26994))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____26826
              (fun uu____27023  ->
                 match uu____27023 with
                 | (uu____27040,uvars1,g) -> (uvars1, g))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____27056  -> ());
    push = (fun uu____27058  -> ());
    pop = (fun uu____27061  -> ());
    snapshot =
      (fun uu____27064  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____27083  -> fun uu____27084  -> ());
    encode_sig = (fun uu____27099  -> fun uu____27100  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____27106 =
             let uu____27113 = FStar_Options.peek ()  in (e, g, uu____27113)
              in
           [uu____27106]);
    solve = (fun uu____27129  -> fun uu____27130  -> fun uu____27131  -> ());
    finish = (fun uu____27138  -> ());
    refresh = (fun uu____27140  -> ())
  } 