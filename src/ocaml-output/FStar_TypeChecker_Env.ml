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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__use_eq_strict : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> use_eq_strict
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> uvar_subtyping
  
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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> tc_term
  
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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> universe_of
  
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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> proof_ns
  
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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> splice1
  
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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> mpreprocess
  
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
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> dsenv
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> strict_args_tab
  
let (__proj__Mkenv__item__erasable_types_tab :
  env -> Prims.bool FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; use_eq_strict; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        splice = splice1; mpreprocess; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> erasable_types_tab
  
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
           (fun uu___0_13607  ->
              match uu___0_13607 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____13610 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____13610  in
                  let uu____13611 =
                    let uu____13612 = FStar_Syntax_Subst.compress y  in
                    uu____13612.FStar_Syntax_Syntax.n  in
                  (match uu____13611 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____13616 =
                         let uu___321_13617 = y1  in
                         let uu____13618 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___321_13617.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___321_13617.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____13618
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____13616
                   | uu____13621 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___327_13635 = env  in
      let uu____13636 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___327_13635.solver);
        range = (uu___327_13635.range);
        curmodule = (uu___327_13635.curmodule);
        gamma = uu____13636;
        gamma_sig = (uu___327_13635.gamma_sig);
        gamma_cache = (uu___327_13635.gamma_cache);
        modules = (uu___327_13635.modules);
        expected_typ = (uu___327_13635.expected_typ);
        sigtab = (uu___327_13635.sigtab);
        attrtab = (uu___327_13635.attrtab);
        instantiate_imp = (uu___327_13635.instantiate_imp);
        effects = (uu___327_13635.effects);
        generalize = (uu___327_13635.generalize);
        letrecs = (uu___327_13635.letrecs);
        top_level = (uu___327_13635.top_level);
        check_uvars = (uu___327_13635.check_uvars);
        use_eq = (uu___327_13635.use_eq);
        use_eq_strict = (uu___327_13635.use_eq_strict);
        is_iface = (uu___327_13635.is_iface);
        admit = (uu___327_13635.admit);
        lax = (uu___327_13635.lax);
        lax_universes = (uu___327_13635.lax_universes);
        phase1 = (uu___327_13635.phase1);
        failhard = (uu___327_13635.failhard);
        nosynth = (uu___327_13635.nosynth);
        uvar_subtyping = (uu___327_13635.uvar_subtyping);
        tc_term = (uu___327_13635.tc_term);
        type_of = (uu___327_13635.type_of);
        universe_of = (uu___327_13635.universe_of);
        check_type_of = (uu___327_13635.check_type_of);
        use_bv_sorts = (uu___327_13635.use_bv_sorts);
        qtbl_name_and_index = (uu___327_13635.qtbl_name_and_index);
        normalized_eff_names = (uu___327_13635.normalized_eff_names);
        fv_delta_depths = (uu___327_13635.fv_delta_depths);
        proof_ns = (uu___327_13635.proof_ns);
        synth_hook = (uu___327_13635.synth_hook);
        splice = (uu___327_13635.splice);
        mpreprocess = (uu___327_13635.mpreprocess);
        postprocess = (uu___327_13635.postprocess);
        is_native_tactic = (uu___327_13635.is_native_tactic);
        identifier_info = (uu___327_13635.identifier_info);
        tc_hooks = (uu___327_13635.tc_hooks);
        dsenv = (uu___327_13635.dsenv);
        nbe = (uu___327_13635.nbe);
        strict_args_tab = (uu___327_13635.strict_args_tab);
        erasable_types_tab = (uu___327_13635.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____13644  -> fun uu____13645  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___334_13667 = env  in
      {
        solver = (uu___334_13667.solver);
        range = (uu___334_13667.range);
        curmodule = (uu___334_13667.curmodule);
        gamma = (uu___334_13667.gamma);
        gamma_sig = (uu___334_13667.gamma_sig);
        gamma_cache = (uu___334_13667.gamma_cache);
        modules = (uu___334_13667.modules);
        expected_typ = (uu___334_13667.expected_typ);
        sigtab = (uu___334_13667.sigtab);
        attrtab = (uu___334_13667.attrtab);
        instantiate_imp = (uu___334_13667.instantiate_imp);
        effects = (uu___334_13667.effects);
        generalize = (uu___334_13667.generalize);
        letrecs = (uu___334_13667.letrecs);
        top_level = (uu___334_13667.top_level);
        check_uvars = (uu___334_13667.check_uvars);
        use_eq = (uu___334_13667.use_eq);
        use_eq_strict = (uu___334_13667.use_eq_strict);
        is_iface = (uu___334_13667.is_iface);
        admit = (uu___334_13667.admit);
        lax = (uu___334_13667.lax);
        lax_universes = (uu___334_13667.lax_universes);
        phase1 = (uu___334_13667.phase1);
        failhard = (uu___334_13667.failhard);
        nosynth = (uu___334_13667.nosynth);
        uvar_subtyping = (uu___334_13667.uvar_subtyping);
        tc_term = (uu___334_13667.tc_term);
        type_of = (uu___334_13667.type_of);
        universe_of = (uu___334_13667.universe_of);
        check_type_of = (uu___334_13667.check_type_of);
        use_bv_sorts = (uu___334_13667.use_bv_sorts);
        qtbl_name_and_index = (uu___334_13667.qtbl_name_and_index);
        normalized_eff_names = (uu___334_13667.normalized_eff_names);
        fv_delta_depths = (uu___334_13667.fv_delta_depths);
        proof_ns = (uu___334_13667.proof_ns);
        synth_hook = (uu___334_13667.synth_hook);
        splice = (uu___334_13667.splice);
        mpreprocess = (uu___334_13667.mpreprocess);
        postprocess = (uu___334_13667.postprocess);
        is_native_tactic = (uu___334_13667.is_native_tactic);
        identifier_info = (uu___334_13667.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___334_13667.dsenv);
        nbe = (uu___334_13667.nbe);
        strict_args_tab = (uu___334_13667.strict_args_tab);
        erasable_types_tab = (uu___334_13667.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___338_13679 = e  in
      let uu____13680 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___338_13679.solver);
        range = (uu___338_13679.range);
        curmodule = (uu___338_13679.curmodule);
        gamma = (uu___338_13679.gamma);
        gamma_sig = (uu___338_13679.gamma_sig);
        gamma_cache = (uu___338_13679.gamma_cache);
        modules = (uu___338_13679.modules);
        expected_typ = (uu___338_13679.expected_typ);
        sigtab = (uu___338_13679.sigtab);
        attrtab = (uu___338_13679.attrtab);
        instantiate_imp = (uu___338_13679.instantiate_imp);
        effects = (uu___338_13679.effects);
        generalize = (uu___338_13679.generalize);
        letrecs = (uu___338_13679.letrecs);
        top_level = (uu___338_13679.top_level);
        check_uvars = (uu___338_13679.check_uvars);
        use_eq = (uu___338_13679.use_eq);
        use_eq_strict = (uu___338_13679.use_eq_strict);
        is_iface = (uu___338_13679.is_iface);
        admit = (uu___338_13679.admit);
        lax = (uu___338_13679.lax);
        lax_universes = (uu___338_13679.lax_universes);
        phase1 = (uu___338_13679.phase1);
        failhard = (uu___338_13679.failhard);
        nosynth = (uu___338_13679.nosynth);
        uvar_subtyping = (uu___338_13679.uvar_subtyping);
        tc_term = (uu___338_13679.tc_term);
        type_of = (uu___338_13679.type_of);
        universe_of = (uu___338_13679.universe_of);
        check_type_of = (uu___338_13679.check_type_of);
        use_bv_sorts = (uu___338_13679.use_bv_sorts);
        qtbl_name_and_index = (uu___338_13679.qtbl_name_and_index);
        normalized_eff_names = (uu___338_13679.normalized_eff_names);
        fv_delta_depths = (uu___338_13679.fv_delta_depths);
        proof_ns = (uu___338_13679.proof_ns);
        synth_hook = (uu___338_13679.synth_hook);
        splice = (uu___338_13679.splice);
        mpreprocess = (uu___338_13679.mpreprocess);
        postprocess = (uu___338_13679.postprocess);
        is_native_tactic = (uu___338_13679.is_native_tactic);
        identifier_info = (uu___338_13679.identifier_info);
        tc_hooks = (uu___338_13679.tc_hooks);
        dsenv = uu____13680;
        nbe = (uu___338_13679.nbe);
        strict_args_tab = (uu___338_13679.strict_args_tab);
        erasable_types_tab = (uu___338_13679.erasable_types_tab)
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
      | (NoDelta ,uu____13709) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13712,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13714,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13717 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13731 . unit -> 'Auu____13731 FStar_Util.smap =
  fun uu____13738  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13744 . unit -> 'Auu____13744 FStar_Util.smap =
  fun uu____13751  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13889 = new_gamma_cache ()  in
                  let uu____13892 = new_sigtab ()  in
                  let uu____13895 = new_sigtab ()  in
                  let uu____13902 =
                    let uu____13917 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13917, FStar_Pervasives_Native.None)  in
                  let uu____13938 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13942 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13946 = FStar_Options.using_facts_from ()  in
                  let uu____13947 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13950 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13951 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13965 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13889;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13892;
                    attrtab = uu____13895;
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
                    qtbl_name_and_index = uu____13902;
                    normalized_eff_names = uu____13938;
                    fv_delta_depths = uu____13942;
                    proof_ns = uu____13946;
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
                    is_native_tactic = (fun uu____14073  -> false);
                    identifier_info = uu____13947;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13950;
                    nbe = nbe1;
                    strict_args_tab = uu____13951;
                    erasable_types_tab = uu____13965
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
  fun uu____14152  ->
    let uu____14153 = FStar_ST.op_Bang query_indices  in
    match uu____14153 with
    | [] -> failwith "Empty query indices!"
    | uu____14208 ->
        let uu____14218 =
          let uu____14228 =
            let uu____14236 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____14236  in
          let uu____14290 = FStar_ST.op_Bang query_indices  in uu____14228 ::
            uu____14290
           in
        FStar_ST.op_Colon_Equals query_indices uu____14218
  
let (pop_query_indices : unit -> unit) =
  fun uu____14386  ->
    let uu____14387 = FStar_ST.op_Bang query_indices  in
    match uu____14387 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____14514  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____14551  ->
    match uu____14551 with
    | (l,n1) ->
        let uu____14561 = FStar_ST.op_Bang query_indices  in
        (match uu____14561 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____14683 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____14706  ->
    let uu____14707 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____14707
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14775 =
       let uu____14778 = FStar_ST.op_Bang stack  in env :: uu____14778  in
     FStar_ST.op_Colon_Equals stack uu____14775);
    (let uu___409_14827 = env  in
     let uu____14828 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14831 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14834 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14841 =
       let uu____14856 =
         let uu____14860 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14860  in
       let uu____14892 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14856, uu____14892)  in
     let uu____14941 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14944 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14947 =
       let uu____14950 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14950  in
     let uu____14970 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____14983 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___409_14827.solver);
       range = (uu___409_14827.range);
       curmodule = (uu___409_14827.curmodule);
       gamma = (uu___409_14827.gamma);
       gamma_sig = (uu___409_14827.gamma_sig);
       gamma_cache = uu____14828;
       modules = (uu___409_14827.modules);
       expected_typ = (uu___409_14827.expected_typ);
       sigtab = uu____14831;
       attrtab = uu____14834;
       instantiate_imp = (uu___409_14827.instantiate_imp);
       effects = (uu___409_14827.effects);
       generalize = (uu___409_14827.generalize);
       letrecs = (uu___409_14827.letrecs);
       top_level = (uu___409_14827.top_level);
       check_uvars = (uu___409_14827.check_uvars);
       use_eq = (uu___409_14827.use_eq);
       use_eq_strict = (uu___409_14827.use_eq_strict);
       is_iface = (uu___409_14827.is_iface);
       admit = (uu___409_14827.admit);
       lax = (uu___409_14827.lax);
       lax_universes = (uu___409_14827.lax_universes);
       phase1 = (uu___409_14827.phase1);
       failhard = (uu___409_14827.failhard);
       nosynth = (uu___409_14827.nosynth);
       uvar_subtyping = (uu___409_14827.uvar_subtyping);
       tc_term = (uu___409_14827.tc_term);
       type_of = (uu___409_14827.type_of);
       universe_of = (uu___409_14827.universe_of);
       check_type_of = (uu___409_14827.check_type_of);
       use_bv_sorts = (uu___409_14827.use_bv_sorts);
       qtbl_name_and_index = uu____14841;
       normalized_eff_names = uu____14941;
       fv_delta_depths = uu____14944;
       proof_ns = (uu___409_14827.proof_ns);
       synth_hook = (uu___409_14827.synth_hook);
       splice = (uu___409_14827.splice);
       mpreprocess = (uu___409_14827.mpreprocess);
       postprocess = (uu___409_14827.postprocess);
       is_native_tactic = (uu___409_14827.is_native_tactic);
       identifier_info = uu____14947;
       tc_hooks = (uu___409_14827.tc_hooks);
       dsenv = (uu___409_14827.dsenv);
       nbe = (uu___409_14827.nbe);
       strict_args_tab = uu____14970;
       erasable_types_tab = uu____14983
     })
  
let (pop_stack : unit -> env) =
  fun uu____14993  ->
    let uu____14994 = FStar_ST.op_Bang stack  in
    match uu____14994 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____15048 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____15138  ->
           let uu____15139 = snapshot_stack env  in
           match uu____15139 with
           | (stack_depth,env1) ->
               let uu____15173 = snapshot_query_indices ()  in
               (match uu____15173 with
                | (query_indices_depth,()) ->
                    let uu____15206 = (env1.solver).snapshot msg  in
                    (match uu____15206 with
                     | (solver_depth,()) ->
                         let uu____15263 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____15263 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___434_15330 = env1  in
                                 {
                                   solver = (uu___434_15330.solver);
                                   range = (uu___434_15330.range);
                                   curmodule = (uu___434_15330.curmodule);
                                   gamma = (uu___434_15330.gamma);
                                   gamma_sig = (uu___434_15330.gamma_sig);
                                   gamma_cache = (uu___434_15330.gamma_cache);
                                   modules = (uu___434_15330.modules);
                                   expected_typ =
                                     (uu___434_15330.expected_typ);
                                   sigtab = (uu___434_15330.sigtab);
                                   attrtab = (uu___434_15330.attrtab);
                                   instantiate_imp =
                                     (uu___434_15330.instantiate_imp);
                                   effects = (uu___434_15330.effects);
                                   generalize = (uu___434_15330.generalize);
                                   letrecs = (uu___434_15330.letrecs);
                                   top_level = (uu___434_15330.top_level);
                                   check_uvars = (uu___434_15330.check_uvars);
                                   use_eq = (uu___434_15330.use_eq);
                                   use_eq_strict =
                                     (uu___434_15330.use_eq_strict);
                                   is_iface = (uu___434_15330.is_iface);
                                   admit = (uu___434_15330.admit);
                                   lax = (uu___434_15330.lax);
                                   lax_universes =
                                     (uu___434_15330.lax_universes);
                                   phase1 = (uu___434_15330.phase1);
                                   failhard = (uu___434_15330.failhard);
                                   nosynth = (uu___434_15330.nosynth);
                                   uvar_subtyping =
                                     (uu___434_15330.uvar_subtyping);
                                   tc_term = (uu___434_15330.tc_term);
                                   type_of = (uu___434_15330.type_of);
                                   universe_of = (uu___434_15330.universe_of);
                                   check_type_of =
                                     (uu___434_15330.check_type_of);
                                   use_bv_sorts =
                                     (uu___434_15330.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___434_15330.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___434_15330.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___434_15330.fv_delta_depths);
                                   proof_ns = (uu___434_15330.proof_ns);
                                   synth_hook = (uu___434_15330.synth_hook);
                                   splice = (uu___434_15330.splice);
                                   mpreprocess = (uu___434_15330.mpreprocess);
                                   postprocess = (uu___434_15330.postprocess);
                                   is_native_tactic =
                                     (uu___434_15330.is_native_tactic);
                                   identifier_info =
                                     (uu___434_15330.identifier_info);
                                   tc_hooks = (uu___434_15330.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___434_15330.nbe);
                                   strict_args_tab =
                                     (uu___434_15330.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___434_15330.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____15364  ->
             let uu____15365 =
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
             match uu____15365 with
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
                             ((let uu____15545 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____15545
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____15561 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____15561
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____15593,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____15635 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____15665  ->
                  match uu____15665 with
                  | (m,uu____15673) -> FStar_Ident.lid_equals l m))
           in
        (match uu____15635 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___479_15688 = env  in
               {
                 solver = (uu___479_15688.solver);
                 range = (uu___479_15688.range);
                 curmodule = (uu___479_15688.curmodule);
                 gamma = (uu___479_15688.gamma);
                 gamma_sig = (uu___479_15688.gamma_sig);
                 gamma_cache = (uu___479_15688.gamma_cache);
                 modules = (uu___479_15688.modules);
                 expected_typ = (uu___479_15688.expected_typ);
                 sigtab = (uu___479_15688.sigtab);
                 attrtab = (uu___479_15688.attrtab);
                 instantiate_imp = (uu___479_15688.instantiate_imp);
                 effects = (uu___479_15688.effects);
                 generalize = (uu___479_15688.generalize);
                 letrecs = (uu___479_15688.letrecs);
                 top_level = (uu___479_15688.top_level);
                 check_uvars = (uu___479_15688.check_uvars);
                 use_eq = (uu___479_15688.use_eq);
                 use_eq_strict = (uu___479_15688.use_eq_strict);
                 is_iface = (uu___479_15688.is_iface);
                 admit = (uu___479_15688.admit);
                 lax = (uu___479_15688.lax);
                 lax_universes = (uu___479_15688.lax_universes);
                 phase1 = (uu___479_15688.phase1);
                 failhard = (uu___479_15688.failhard);
                 nosynth = (uu___479_15688.nosynth);
                 uvar_subtyping = (uu___479_15688.uvar_subtyping);
                 tc_term = (uu___479_15688.tc_term);
                 type_of = (uu___479_15688.type_of);
                 universe_of = (uu___479_15688.universe_of);
                 check_type_of = (uu___479_15688.check_type_of);
                 use_bv_sorts = (uu___479_15688.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___479_15688.normalized_eff_names);
                 fv_delta_depths = (uu___479_15688.fv_delta_depths);
                 proof_ns = (uu___479_15688.proof_ns);
                 synth_hook = (uu___479_15688.synth_hook);
                 splice = (uu___479_15688.splice);
                 mpreprocess = (uu___479_15688.mpreprocess);
                 postprocess = (uu___479_15688.postprocess);
                 is_native_tactic = (uu___479_15688.is_native_tactic);
                 identifier_info = (uu___479_15688.identifier_info);
                 tc_hooks = (uu___479_15688.tc_hooks);
                 dsenv = (uu___479_15688.dsenv);
                 nbe = (uu___479_15688.nbe);
                 strict_args_tab = (uu___479_15688.strict_args_tab);
                 erasable_types_tab = (uu___479_15688.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____15705,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___488_15721 = env  in
               {
                 solver = (uu___488_15721.solver);
                 range = (uu___488_15721.range);
                 curmodule = (uu___488_15721.curmodule);
                 gamma = (uu___488_15721.gamma);
                 gamma_sig = (uu___488_15721.gamma_sig);
                 gamma_cache = (uu___488_15721.gamma_cache);
                 modules = (uu___488_15721.modules);
                 expected_typ = (uu___488_15721.expected_typ);
                 sigtab = (uu___488_15721.sigtab);
                 attrtab = (uu___488_15721.attrtab);
                 instantiate_imp = (uu___488_15721.instantiate_imp);
                 effects = (uu___488_15721.effects);
                 generalize = (uu___488_15721.generalize);
                 letrecs = (uu___488_15721.letrecs);
                 top_level = (uu___488_15721.top_level);
                 check_uvars = (uu___488_15721.check_uvars);
                 use_eq = (uu___488_15721.use_eq);
                 use_eq_strict = (uu___488_15721.use_eq_strict);
                 is_iface = (uu___488_15721.is_iface);
                 admit = (uu___488_15721.admit);
                 lax = (uu___488_15721.lax);
                 lax_universes = (uu___488_15721.lax_universes);
                 phase1 = (uu___488_15721.phase1);
                 failhard = (uu___488_15721.failhard);
                 nosynth = (uu___488_15721.nosynth);
                 uvar_subtyping = (uu___488_15721.uvar_subtyping);
                 tc_term = (uu___488_15721.tc_term);
                 type_of = (uu___488_15721.type_of);
                 universe_of = (uu___488_15721.universe_of);
                 check_type_of = (uu___488_15721.check_type_of);
                 use_bv_sorts = (uu___488_15721.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___488_15721.normalized_eff_names);
                 fv_delta_depths = (uu___488_15721.fv_delta_depths);
                 proof_ns = (uu___488_15721.proof_ns);
                 synth_hook = (uu___488_15721.synth_hook);
                 splice = (uu___488_15721.splice);
                 mpreprocess = (uu___488_15721.mpreprocess);
                 postprocess = (uu___488_15721.postprocess);
                 is_native_tactic = (uu___488_15721.is_native_tactic);
                 identifier_info = (uu___488_15721.identifier_info);
                 tc_hooks = (uu___488_15721.tc_hooks);
                 dsenv = (uu___488_15721.dsenv);
                 nbe = (uu___488_15721.nbe);
                 strict_args_tab = (uu___488_15721.strict_args_tab);
                 erasable_types_tab = (uu___488_15721.erasable_types_tab)
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
        (let uu___495_15764 = e  in
         {
           solver = (uu___495_15764.solver);
           range = r;
           curmodule = (uu___495_15764.curmodule);
           gamma = (uu___495_15764.gamma);
           gamma_sig = (uu___495_15764.gamma_sig);
           gamma_cache = (uu___495_15764.gamma_cache);
           modules = (uu___495_15764.modules);
           expected_typ = (uu___495_15764.expected_typ);
           sigtab = (uu___495_15764.sigtab);
           attrtab = (uu___495_15764.attrtab);
           instantiate_imp = (uu___495_15764.instantiate_imp);
           effects = (uu___495_15764.effects);
           generalize = (uu___495_15764.generalize);
           letrecs = (uu___495_15764.letrecs);
           top_level = (uu___495_15764.top_level);
           check_uvars = (uu___495_15764.check_uvars);
           use_eq = (uu___495_15764.use_eq);
           use_eq_strict = (uu___495_15764.use_eq_strict);
           is_iface = (uu___495_15764.is_iface);
           admit = (uu___495_15764.admit);
           lax = (uu___495_15764.lax);
           lax_universes = (uu___495_15764.lax_universes);
           phase1 = (uu___495_15764.phase1);
           failhard = (uu___495_15764.failhard);
           nosynth = (uu___495_15764.nosynth);
           uvar_subtyping = (uu___495_15764.uvar_subtyping);
           tc_term = (uu___495_15764.tc_term);
           type_of = (uu___495_15764.type_of);
           universe_of = (uu___495_15764.universe_of);
           check_type_of = (uu___495_15764.check_type_of);
           use_bv_sorts = (uu___495_15764.use_bv_sorts);
           qtbl_name_and_index = (uu___495_15764.qtbl_name_and_index);
           normalized_eff_names = (uu___495_15764.normalized_eff_names);
           fv_delta_depths = (uu___495_15764.fv_delta_depths);
           proof_ns = (uu___495_15764.proof_ns);
           synth_hook = (uu___495_15764.synth_hook);
           splice = (uu___495_15764.splice);
           mpreprocess = (uu___495_15764.mpreprocess);
           postprocess = (uu___495_15764.postprocess);
           is_native_tactic = (uu___495_15764.is_native_tactic);
           identifier_info = (uu___495_15764.identifier_info);
           tc_hooks = (uu___495_15764.tc_hooks);
           dsenv = (uu___495_15764.dsenv);
           nbe = (uu___495_15764.nbe);
           strict_args_tab = (uu___495_15764.strict_args_tab);
           erasable_types_tab = (uu___495_15764.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15784 =
        let uu____15785 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15785 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15784
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15840 =
          let uu____15841 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15841 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15840
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15896 =
          let uu____15897 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15897 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15896
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15952 =
        let uu____15953 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15953 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15952
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___512_16017 = env  in
      {
        solver = (uu___512_16017.solver);
        range = (uu___512_16017.range);
        curmodule = lid;
        gamma = (uu___512_16017.gamma);
        gamma_sig = (uu___512_16017.gamma_sig);
        gamma_cache = (uu___512_16017.gamma_cache);
        modules = (uu___512_16017.modules);
        expected_typ = (uu___512_16017.expected_typ);
        sigtab = (uu___512_16017.sigtab);
        attrtab = (uu___512_16017.attrtab);
        instantiate_imp = (uu___512_16017.instantiate_imp);
        effects = (uu___512_16017.effects);
        generalize = (uu___512_16017.generalize);
        letrecs = (uu___512_16017.letrecs);
        top_level = (uu___512_16017.top_level);
        check_uvars = (uu___512_16017.check_uvars);
        use_eq = (uu___512_16017.use_eq);
        use_eq_strict = (uu___512_16017.use_eq_strict);
        is_iface = (uu___512_16017.is_iface);
        admit = (uu___512_16017.admit);
        lax = (uu___512_16017.lax);
        lax_universes = (uu___512_16017.lax_universes);
        phase1 = (uu___512_16017.phase1);
        failhard = (uu___512_16017.failhard);
        nosynth = (uu___512_16017.nosynth);
        uvar_subtyping = (uu___512_16017.uvar_subtyping);
        tc_term = (uu___512_16017.tc_term);
        type_of = (uu___512_16017.type_of);
        universe_of = (uu___512_16017.universe_of);
        check_type_of = (uu___512_16017.check_type_of);
        use_bv_sorts = (uu___512_16017.use_bv_sorts);
        qtbl_name_and_index = (uu___512_16017.qtbl_name_and_index);
        normalized_eff_names = (uu___512_16017.normalized_eff_names);
        fv_delta_depths = (uu___512_16017.fv_delta_depths);
        proof_ns = (uu___512_16017.proof_ns);
        synth_hook = (uu___512_16017.synth_hook);
        splice = (uu___512_16017.splice);
        mpreprocess = (uu___512_16017.mpreprocess);
        postprocess = (uu___512_16017.postprocess);
        is_native_tactic = (uu___512_16017.is_native_tactic);
        identifier_info = (uu___512_16017.identifier_info);
        tc_hooks = (uu___512_16017.tc_hooks);
        dsenv = (uu___512_16017.dsenv);
        nbe = (uu___512_16017.nbe);
        strict_args_tab = (uu___512_16017.strict_args_tab);
        erasable_types_tab = (uu___512_16017.erasable_types_tab)
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
      let uu____16048 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____16048
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____16061 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____16061)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____16076 =
      let uu____16078 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____16078  in
    (FStar_Errors.Fatal_VariableNotFound, uu____16076)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____16087  ->
    let uu____16088 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____16088
  
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
      | ((formals,t),uu____16188) ->
          let vs = mk_univ_subst formals us  in
          let uu____16212 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____16212)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_16229  ->
    match uu___1_16229 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____16255  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____16275 = inst_tscheme t  in
      match uu____16275 with
      | (us,t1) ->
          let uu____16286 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____16286)
  
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
          let uu____16311 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____16313 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____16311 uu____16313
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
        fun uu____16340  ->
          match uu____16340 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____16354 =
                    let uu____16356 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____16360 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____16364 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____16366 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____16356 uu____16360 uu____16364 uu____16366
                     in
                  failwith uu____16354)
               else ();
               (let uu____16371 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____16371))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____16389 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____16400 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____16411 -> false
  
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
             | ([],uu____16459) -> Maybe
             | (uu____16466,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____16486 -> No  in
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
          let uu____16580 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____16580 with
          | FStar_Pervasives_Native.None  ->
              let uu____16603 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_16647  ->
                     match uu___2_16647 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____16686 = FStar_Ident.lid_equals lid l  in
                         if uu____16686
                         then
                           let uu____16709 =
                             let uu____16728 =
                               let uu____16743 = inst_tscheme t  in
                               FStar_Util.Inl uu____16743  in
                             let uu____16758 = FStar_Ident.range_of_lid l  in
                             (uu____16728, uu____16758)  in
                           FStar_Pervasives_Native.Some uu____16709
                         else FStar_Pervasives_Native.None
                     | uu____16811 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____16603
                (fun uu____16849  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16859  ->
                        match uu___3_16859 with
                        | (uu____16862,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16864);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16865;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16866;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16867;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16868;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____16869;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16891 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16891
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
                                  uu____16943 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16950 -> cache t  in
                            let uu____16951 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16951 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16957 =
                                   let uu____16958 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16958)
                                    in
                                 maybe_cache uu____16957)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____17029 = find_in_sigtab env lid  in
         match uu____17029 with
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
      let uu____17110 = lookup_qname env lid  in
      match uu____17110 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____17131,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____17245 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____17245 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____17290 =
          let uu____17293 = lookup_attr env1 attr  in se1 :: uu____17293  in
        FStar_Util.smap_add (attrtab env1) attr uu____17290  in
      FStar_List.iter
        (fun attr  ->
           let uu____17303 =
             let uu____17304 = FStar_Syntax_Subst.compress attr  in
             uu____17304.FStar_Syntax_Syntax.n  in
           match uu____17303 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____17308 =
                 let uu____17310 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____17310.FStar_Ident.str  in
               add_one1 env se uu____17308
           | uu____17311 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____17334) ->
          add_sigelts env ses
      | uu____17343 ->
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
        (fun uu___4_17381  ->
           match uu___4_17381 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____17399 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____17461,lb::[]),uu____17463) ->
            let uu____17472 =
              let uu____17481 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____17490 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____17481, uu____17490)  in
            FStar_Pervasives_Native.Some uu____17472
        | FStar_Syntax_Syntax.Sig_let ((uu____17503,lbs),uu____17505) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____17537 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____17550 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____17550
                     then
                       let uu____17563 =
                         let uu____17572 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____17581 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____17572, uu____17581)  in
                       FStar_Pervasives_Native.Some uu____17563
                     else FStar_Pervasives_Native.None)
        | uu____17604 -> FStar_Pervasives_Native.None
  
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
                    let uu____17696 =
                      let uu____17698 =
                        let uu____17700 =
                          let uu____17702 =
                            let uu____17704 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____17710 =
                              let uu____17712 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____17712  in
                            Prims.op_Hat uu____17704 uu____17710  in
                          Prims.op_Hat ", expected " uu____17702  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____17700
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____17698
                       in
                    failwith uu____17696
                  else ());
             (let uu____17719 =
                let uu____17728 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____17728, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____17719))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17748,uu____17749) ->
            let uu____17754 =
              let uu____17763 =
                let uu____17768 =
                  let uu____17769 =
                    let uu____17772 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17772  in
                  (us, uu____17769)  in
                inst_ts us_opt uu____17768  in
              (uu____17763, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17754
        | uu____17791 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17880 =
          match uu____17880 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17976,uvs,t,uu____17979,uu____17980,uu____17981);
                      FStar_Syntax_Syntax.sigrng = uu____17982;
                      FStar_Syntax_Syntax.sigquals = uu____17983;
                      FStar_Syntax_Syntax.sigmeta = uu____17984;
                      FStar_Syntax_Syntax.sigattrs = uu____17985;
                      FStar_Syntax_Syntax.sigopts = uu____17986;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18011 =
                     let uu____18020 = inst_tscheme1 (uvs, t)  in
                     (uu____18020, rng)  in
                   FStar_Pervasives_Native.Some uu____18011
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____18044;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____18046;
                      FStar_Syntax_Syntax.sigattrs = uu____18047;
                      FStar_Syntax_Syntax.sigopts = uu____18048;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____18067 =
                     let uu____18069 = in_cur_mod env l  in uu____18069 = Yes
                      in
                   if uu____18067
                   then
                     let uu____18081 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____18081
                      then
                        let uu____18097 =
                          let uu____18106 = inst_tscheme1 (uvs, t)  in
                          (uu____18106, rng)  in
                        FStar_Pervasives_Native.Some uu____18097
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____18139 =
                        let uu____18148 = inst_tscheme1 (uvs, t)  in
                        (uu____18148, rng)  in
                      FStar_Pervasives_Native.Some uu____18139)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18173,uu____18174);
                      FStar_Syntax_Syntax.sigrng = uu____18175;
                      FStar_Syntax_Syntax.sigquals = uu____18176;
                      FStar_Syntax_Syntax.sigmeta = uu____18177;
                      FStar_Syntax_Syntax.sigattrs = uu____18178;
                      FStar_Syntax_Syntax.sigopts = uu____18179;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____18222 =
                          let uu____18231 = inst_tscheme1 (uvs, k)  in
                          (uu____18231, rng)  in
                        FStar_Pervasives_Native.Some uu____18222
                    | uu____18252 ->
                        let uu____18253 =
                          let uu____18262 =
                            let uu____18267 =
                              let uu____18268 =
                                let uu____18271 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18271
                                 in
                              (uvs, uu____18268)  in
                            inst_tscheme1 uu____18267  in
                          (uu____18262, rng)  in
                        FStar_Pervasives_Native.Some uu____18253)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____18294,uu____18295);
                      FStar_Syntax_Syntax.sigrng = uu____18296;
                      FStar_Syntax_Syntax.sigquals = uu____18297;
                      FStar_Syntax_Syntax.sigmeta = uu____18298;
                      FStar_Syntax_Syntax.sigattrs = uu____18299;
                      FStar_Syntax_Syntax.sigopts = uu____18300;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____18344 =
                          let uu____18353 = inst_tscheme_with (uvs, k) us  in
                          (uu____18353, rng)  in
                        FStar_Pervasives_Native.Some uu____18344
                    | uu____18374 ->
                        let uu____18375 =
                          let uu____18384 =
                            let uu____18389 =
                              let uu____18390 =
                                let uu____18393 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____18393
                                 in
                              (uvs, uu____18390)  in
                            inst_tscheme_with uu____18389 us  in
                          (uu____18384, rng)  in
                        FStar_Pervasives_Native.Some uu____18375)
               | FStar_Util.Inr se ->
                   let uu____18429 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____18450;
                          FStar_Syntax_Syntax.sigrng = uu____18451;
                          FStar_Syntax_Syntax.sigquals = uu____18452;
                          FStar_Syntax_Syntax.sigmeta = uu____18453;
                          FStar_Syntax_Syntax.sigattrs = uu____18454;
                          FStar_Syntax_Syntax.sigopts = uu____18455;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____18472 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____18429
                     (FStar_Util.map_option
                        (fun uu____18520  ->
                           match uu____18520 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____18551 =
          let uu____18562 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____18562 mapper  in
        match uu____18551 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____18636 =
              let uu____18647 =
                let uu____18654 =
                  let uu___849_18657 = t  in
                  let uu____18658 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___849_18657.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____18658;
                    FStar_Syntax_Syntax.vars =
                      (uu___849_18657.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____18654)  in
              (uu____18647, r)  in
            FStar_Pervasives_Native.Some uu____18636
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____18707 = lookup_qname env l  in
      match uu____18707 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____18728 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18782 = try_lookup_bv env bv  in
      match uu____18782 with
      | FStar_Pervasives_Native.None  ->
          let uu____18797 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18797 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18813 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18814 =
            let uu____18815 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18815  in
          (uu____18813, uu____18814)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18837 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18837 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18903 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18903  in
          let uu____18904 =
            let uu____18913 =
              let uu____18918 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18918)  in
            (uu____18913, r1)  in
          FStar_Pervasives_Native.Some uu____18904
  
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
        let uu____18953 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18953 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18986,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____19011 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____19011  in
            let uu____19012 =
              let uu____19017 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____19017, r1)  in
            FStar_Pervasives_Native.Some uu____19012
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____19041 = try_lookup_lid env l  in
      match uu____19041 with
      | FStar_Pervasives_Native.None  ->
          let uu____19068 = name_not_found l  in
          let uu____19074 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____19068 uu____19074
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_19117  ->
              match uu___5_19117 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____19121 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19142 = lookup_qname env lid  in
      match uu____19142 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19151,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19154;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19156;
              FStar_Syntax_Syntax.sigattrs = uu____19157;
              FStar_Syntax_Syntax.sigopts = uu____19158;_},FStar_Pervasives_Native.None
            ),uu____19159)
          ->
          let uu____19210 =
            let uu____19217 =
              let uu____19218 =
                let uu____19221 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____19221 t  in
              (uvs, uu____19218)  in
            (uu____19217, q)  in
          FStar_Pervasives_Native.Some uu____19210
      | uu____19234 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19256 = lookup_qname env lid  in
      match uu____19256 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19261,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____19264;
              FStar_Syntax_Syntax.sigquals = uu____19265;
              FStar_Syntax_Syntax.sigmeta = uu____19266;
              FStar_Syntax_Syntax.sigattrs = uu____19267;
              FStar_Syntax_Syntax.sigopts = uu____19268;_},FStar_Pervasives_Native.None
            ),uu____19269)
          ->
          let uu____19320 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19320 (uvs, t)
      | uu____19325 ->
          let uu____19326 = name_not_found lid  in
          let uu____19332 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19326 uu____19332
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____19352 = lookup_qname env lid  in
      match uu____19352 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19357,uvs,t,uu____19360,uu____19361,uu____19362);
              FStar_Syntax_Syntax.sigrng = uu____19363;
              FStar_Syntax_Syntax.sigquals = uu____19364;
              FStar_Syntax_Syntax.sigmeta = uu____19365;
              FStar_Syntax_Syntax.sigattrs = uu____19366;
              FStar_Syntax_Syntax.sigopts = uu____19367;_},FStar_Pervasives_Native.None
            ),uu____19368)
          ->
          let uu____19425 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____19425 (uvs, t)
      | uu____19430 ->
          let uu____19431 = name_not_found lid  in
          let uu____19437 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____19431 uu____19437
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____19460 = lookup_qname env lid  in
      match uu____19460 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19468,uu____19469,uu____19470,uu____19471,uu____19472,dcs);
              FStar_Syntax_Syntax.sigrng = uu____19474;
              FStar_Syntax_Syntax.sigquals = uu____19475;
              FStar_Syntax_Syntax.sigmeta = uu____19476;
              FStar_Syntax_Syntax.sigattrs = uu____19477;
              FStar_Syntax_Syntax.sigopts = uu____19478;_},uu____19479),uu____19480)
          -> (true, dcs)
      | uu____19545 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____19561 = lookup_qname env lid  in
      match uu____19561 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19562,uu____19563,uu____19564,l,uu____19566,uu____19567);
              FStar_Syntax_Syntax.sigrng = uu____19568;
              FStar_Syntax_Syntax.sigquals = uu____19569;
              FStar_Syntax_Syntax.sigmeta = uu____19570;
              FStar_Syntax_Syntax.sigattrs = uu____19571;
              FStar_Syntax_Syntax.sigopts = uu____19572;_},uu____19573),uu____19574)
          -> l
      | uu____19633 ->
          let uu____19634 =
            let uu____19636 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____19636  in
          failwith uu____19634
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19706)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____19763) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19787 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19787
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19822 -> FStar_Pervasives_Native.None)
          | uu____19831 -> FStar_Pervasives_Native.None
  
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
        let uu____19893 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19893
  
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
        let uu____19926 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19926
  
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
             (FStar_Util.Inl uu____19978,uu____19979) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____20028),uu____20029) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____20078 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____20096 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____20106 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____20123 ->
                  let uu____20130 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____20130
              | FStar_Syntax_Syntax.Sig_let ((uu____20131,lbs),uu____20133)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____20149 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____20149
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____20156 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____20164 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____20165 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____20172 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____20173 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____20174 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____20187 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____20188 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____20216 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____20216
           (fun d_opt  ->
              let uu____20229 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____20229
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____20239 =
                   let uu____20242 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____20242  in
                 match uu____20239 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____20243 =
                       let uu____20245 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____20245
                        in
                     failwith uu____20243
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____20250 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____20250
                       then
                         let uu____20253 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____20255 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____20257 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____20253 uu____20255 uu____20257
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
        (FStar_Util.Inr (se,uu____20282),uu____20283) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____20332 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____20354),uu____20355) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____20404 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____20426 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____20426
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20459 = lookup_attrs_of_lid env fv_lid1  in
        match uu____20459 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____20481 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____20490 =
                        let uu____20491 = FStar_Syntax_Util.un_uinst tm  in
                        uu____20491.FStar_Syntax_Syntax.n  in
                      match uu____20490 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____20496 -> false))
               in
            (true, uu____20481)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____20519 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____20519
  
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
          let uu____20591 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____20591.FStar_Ident.str  in
        let uu____20592 = FStar_Util.smap_try_find tab s  in
        match uu____20592 with
        | FStar_Pervasives_Native.None  ->
            let uu____20595 = f ()  in
            (match uu____20595 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____20633 =
        let uu____20634 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____20634 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____20668 =
        let uu____20669 = FStar_Syntax_Util.unrefine t  in
        uu____20669.FStar_Syntax_Syntax.n  in
      match uu____20668 with
      | FStar_Syntax_Syntax.Tm_type uu____20673 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____20677) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____20703) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____20708,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____20730 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____20763 =
        let attrs =
          let uu____20769 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____20769  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____20809 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____20809)
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
      let uu____20854 = lookup_qname env ftv  in
      match uu____20854 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____20858) ->
          let uu____20903 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____20903 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____20924,t),r) ->
               let uu____20939 =
                 let uu____20940 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____20940 t  in
               FStar_Pervasives_Native.Some uu____20939)
      | uu____20941 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____20953 = try_lookup_effect_lid env ftv  in
      match uu____20953 with
      | FStar_Pervasives_Native.None  ->
          let uu____20956 = name_not_found ftv  in
          let uu____20962 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____20956 uu____20962
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
        let uu____20986 = lookup_qname env lid0  in
        match uu____20986 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____20997);
                FStar_Syntax_Syntax.sigrng = uu____20998;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____21000;
                FStar_Syntax_Syntax.sigattrs = uu____21001;
                FStar_Syntax_Syntax.sigopts = uu____21002;_},FStar_Pervasives_Native.None
              ),uu____21003)
            ->
            let lid1 =
              let uu____21059 =
                let uu____21060 = FStar_Ident.range_of_lid lid  in
                let uu____21061 =
                  let uu____21062 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____21062  in
                FStar_Range.set_use_range uu____21060 uu____21061  in
              FStar_Ident.set_lid_range lid uu____21059  in
            let uu____21063 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_21069  ->
                      match uu___6_21069 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____21072 -> false))
               in
            if uu____21063
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____21091 =
                      let uu____21093 =
                        let uu____21095 = get_range env  in
                        FStar_Range.string_of_range uu____21095  in
                      let uu____21096 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____21098 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____21093 uu____21096 uu____21098
                       in
                    failwith uu____21091)
                  in
               match (binders, univs1) with
               | ([],uu____21119) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____21145,uu____21146::uu____21147::uu____21148) ->
                   let uu____21169 =
                     let uu____21171 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____21173 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____21171 uu____21173
                      in
                   failwith uu____21169
               | uu____21184 ->
                   let uu____21199 =
                     let uu____21204 =
                       let uu____21205 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____21205)  in
                     inst_tscheme_with uu____21204 insts  in
                   (match uu____21199 with
                    | (uu____21218,t) ->
                        let t1 =
                          let uu____21221 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____21221 t  in
                        let uu____21222 =
                          let uu____21223 = FStar_Syntax_Subst.compress t1
                             in
                          uu____21223.FStar_Syntax_Syntax.n  in
                        (match uu____21222 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____21258 -> failwith "Impossible")))
        | uu____21266 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____21290 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____21290 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____21303,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____21310 = find1 l2  in
            (match uu____21310 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____21317 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____21317 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____21321 = find1 l  in
            (match uu____21321 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____21326 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____21326
  
let (num_effect_indices :
  env -> FStar_Ident.lident -> FStar_Range.range -> Prims.int) =
  fun env  ->
    fun name  ->
      fun r  ->
        let sig_t =
          let uu____21347 = FStar_All.pipe_right name (lookup_effect_lid env)
             in
          FStar_All.pipe_right uu____21347 FStar_Syntax_Subst.compress  in
        match sig_t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (_a::bs,uu____21353) ->
            FStar_List.length bs
        | uu____21392 ->
            let uu____21393 =
              let uu____21399 =
                let uu____21401 = FStar_Ident.string_of_lid name  in
                let uu____21403 = FStar_Syntax_Print.term_to_string sig_t  in
                FStar_Util.format2 "Signature for %s not an arrow (%s)"
                  uu____21401 uu____21403
                 in
              (FStar_Errors.Fatal_UnexpectedSignatureForMonad, uu____21399)
               in
            FStar_Errors.raise_error uu____21393 r
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____21422 = lookup_qname env l1  in
      match uu____21422 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____21425;
              FStar_Syntax_Syntax.sigrng = uu____21426;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____21428;
              FStar_Syntax_Syntax.sigattrs = uu____21429;
              FStar_Syntax_Syntax.sigopts = uu____21430;_},uu____21431),uu____21432)
          -> q
      | uu____21485 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____21509 =
          let uu____21510 =
            let uu____21512 = FStar_Util.string_of_int i  in
            let uu____21514 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____21512 uu____21514
             in
          failwith uu____21510  in
        let uu____21517 = lookup_datacon env lid  in
        match uu____21517 with
        | (uu____21522,t) ->
            let uu____21524 =
              let uu____21525 = FStar_Syntax_Subst.compress t  in
              uu____21525.FStar_Syntax_Syntax.n  in
            (match uu____21524 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____21529) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____21573 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____21573
                      FStar_Pervasives_Native.fst)
             | uu____21584 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21598 = lookup_qname env l  in
      match uu____21598 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____21600,uu____21601,uu____21602);
              FStar_Syntax_Syntax.sigrng = uu____21603;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21605;
              FStar_Syntax_Syntax.sigattrs = uu____21606;
              FStar_Syntax_Syntax.sigopts = uu____21607;_},uu____21608),uu____21609)
          ->
          FStar_Util.for_some
            (fun uu___7_21664  ->
               match uu___7_21664 with
               | FStar_Syntax_Syntax.Projector uu____21666 -> true
               | uu____21672 -> false) quals
      | uu____21674 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21688 = lookup_qname env lid  in
      match uu____21688 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____21690,uu____21691,uu____21692,uu____21693,uu____21694,uu____21695);
              FStar_Syntax_Syntax.sigrng = uu____21696;
              FStar_Syntax_Syntax.sigquals = uu____21697;
              FStar_Syntax_Syntax.sigmeta = uu____21698;
              FStar_Syntax_Syntax.sigattrs = uu____21699;
              FStar_Syntax_Syntax.sigopts = uu____21700;_},uu____21701),uu____21702)
          -> true
      | uu____21762 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21776 = lookup_qname env lid  in
      match uu____21776 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21778,uu____21779,uu____21780,uu____21781,uu____21782,uu____21783);
              FStar_Syntax_Syntax.sigrng = uu____21784;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____21786;
              FStar_Syntax_Syntax.sigattrs = uu____21787;
              FStar_Syntax_Syntax.sigopts = uu____21788;_},uu____21789),uu____21790)
          ->
          FStar_Util.for_some
            (fun uu___8_21853  ->
               match uu___8_21853 with
               | FStar_Syntax_Syntax.RecordType uu____21855 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____21865 -> true
               | uu____21875 -> false) quals
      | uu____21877 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____21887,uu____21888);
            FStar_Syntax_Syntax.sigrng = uu____21889;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____21891;
            FStar_Syntax_Syntax.sigattrs = uu____21892;
            FStar_Syntax_Syntax.sigopts = uu____21893;_},uu____21894),uu____21895)
        ->
        FStar_Util.for_some
          (fun uu___9_21954  ->
             match uu___9_21954 with
             | FStar_Syntax_Syntax.Action uu____21956 -> true
             | uu____21958 -> false) quals
    | uu____21960 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____21974 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____21974
  
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
      let uu____21991 =
        let uu____21992 = FStar_Syntax_Util.un_uinst head1  in
        uu____21992.FStar_Syntax_Syntax.n  in
      match uu____21991 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____21998 ->
               true
           | uu____22001 -> false)
      | uu____22003 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22017 = lookup_qname env l  in
      match uu____22017 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____22020),uu____22021) ->
          FStar_Util.for_some
            (fun uu___10_22069  ->
               match uu___10_22069 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____22072 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____22074 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____22150 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____22168) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____22186 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____22194 ->
                 FStar_Pervasives_Native.Some true
             | uu____22213 -> FStar_Pervasives_Native.Some false)
         in
      let uu____22216 =
        let uu____22220 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____22220 mapper  in
      match uu____22216 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____22280 = lookup_qname env lid  in
      match uu____22280 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____22284,uu____22285,tps,uu____22287,uu____22288,uu____22289);
              FStar_Syntax_Syntax.sigrng = uu____22290;
              FStar_Syntax_Syntax.sigquals = uu____22291;
              FStar_Syntax_Syntax.sigmeta = uu____22292;
              FStar_Syntax_Syntax.sigattrs = uu____22293;
              FStar_Syntax_Syntax.sigopts = uu____22294;_},uu____22295),uu____22296)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____22364 -> FStar_Pervasives_Native.None
  
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
           (fun uu____22410  ->
              match uu____22410 with
              | (d,uu____22419) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____22435 = effect_decl_opt env l  in
      match uu____22435 with
      | FStar_Pervasives_Native.None  ->
          let uu____22450 = name_not_found l  in
          let uu____22456 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____22450 uu____22456
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____22484 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____22484 FStar_Syntax_Util.is_layered
  
let (identity_mlift : mlift) =
  {
    mlift_wp =
      (fun uu____22491  ->
         fun c  -> (c, FStar_TypeChecker_Common.trivial_guard));
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____22505  ->
            fun uu____22506  -> fun e  -> FStar_Util.return_all e))
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
        let uu____22540 = FStar_Ident.lid_equals l1 l2  in
        if uu____22540
        then
          FStar_Pervasives_Native.Some (l1, identity_mlift, identity_mlift)
        else
          (let uu____22559 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____22559
           then
             FStar_Pervasives_Native.Some
               (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
                 identity_mlift)
           else
             (let uu____22578 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____22631  ->
                        match uu____22631 with
                        | (m1,m2,uu____22645,uu____22646,uu____22647) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____22578 with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some
                  (uu____22672,uu____22673,m3,j1,j2) ->
                  FStar_Pervasives_Native.Some (m3, j1, j2)))
  
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22721 = join_opt env l1 l2  in
        match uu____22721 with
        | FStar_Pervasives_Native.None  ->
            let uu____22742 =
              let uu____22748 =
                let uu____22750 = FStar_Syntax_Print.lid_to_string l1  in
                let uu____22752 = FStar_Syntax_Print.lid_to_string l2  in
                FStar_Util.format2 "Effects %s and %s cannot be composed"
                  uu____22750 uu____22752
                 in
              (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____22748)  in
            FStar_Errors.raise_error uu____22742 env.range
        | FStar_Pervasives_Native.Some t -> t
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____22795 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____22795
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
  'Auu____22815 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____22815) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____22844 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____22870  ->
                match uu____22870 with
                | (d,uu____22877) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____22844 with
      | FStar_Pervasives_Native.None  ->
          let uu____22888 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____22888
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____22903 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____22903 with
           | (uu____22914,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____22932)::(wp,uu____22934)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____22990 -> failwith "Impossible"))
  
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
        | uu____23055 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23068 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23068 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23085 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23085 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23110 =
                     let uu____23116 =
                       let uu____23118 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23126 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23137 =
                         let uu____23139 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23139  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23118 uu____23126 uu____23137
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23116)
                      in
                   FStar_Errors.raise_error uu____23110
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23147 =
                     let uu____23158 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23158 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23195  ->
                        fun uu____23196  ->
                          match (uu____23195, uu____23196) with
                          | ((x,uu____23226),(t,uu____23228)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23147
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23259 =
                     let uu___1603_23260 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1603_23260.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1603_23260.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1603_23260.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1603_23260.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23259
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23272 .
    'Auu____23272 ->
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
            let uu____23313 =
              let uu____23320 = num_effect_indices env eff_name r  in
              ((FStar_List.length args), uu____23320)  in
            match uu____23313 with
            | (given,expected) ->
                if given = expected
                then ()
                else
                  (let message =
                     let uu____23344 = FStar_Ident.string_of_lid eff_name  in
                     let uu____23346 = FStar_Util.string_of_int given  in
                     let uu____23348 = FStar_Util.string_of_int expected  in
                     FStar_Util.format3
                       "Not enough arguments for effect %s, This usually happens when you use a partially applied DM4F effect, like [TAC int] instead of [Tac int] (given:%s, expected:%s)."
                       uu____23344 uu____23346 uu____23348
                      in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                       message) r)
             in
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____23353 = effect_decl_opt env effect_name  in
          match uu____23353 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,uu____23375) ->
              let uu____23386 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              (match uu____23386 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some ts ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let repr = inst_effect_fun_with [u_res] env ed ts  in
                   (check_partial_application effect_name
                      c1.FStar_Syntax_Syntax.effect_args;
                    (let uu____23404 =
                       let uu____23407 = get_range env  in
                       let uu____23408 =
                         let uu____23415 =
                           let uu____23416 =
                             let uu____23433 =
                               let uu____23444 =
                                 FStar_All.pipe_right res_typ
                                   FStar_Syntax_Syntax.as_arg
                                  in
                               uu____23444 ::
                                 (c1.FStar_Syntax_Syntax.effect_args)
                                in
                             (repr, uu____23433)  in
                           FStar_Syntax_Syntax.Tm_app uu____23416  in
                         FStar_Syntax_Syntax.mk uu____23415  in
                       uu____23408 FStar_Pervasives_Native.None uu____23407
                        in
                     FStar_Pervasives_Native.Some uu____23404)))
  
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
           (fun uu___11_23544  ->
              match uu___11_23544 with
              | FStar_Syntax_Syntax.Reflectable uu____23546 -> true
              | uu____23548 -> false))
  
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
      | uu____23608 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23623 =
        let uu____23624 = FStar_Syntax_Subst.compress t  in
        uu____23624.FStar_Syntax_Syntax.n  in
      match uu____23623 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23628,c) ->
          is_reifiable_comp env c
      | uu____23650 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23670 =
           let uu____23672 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23672  in
         if uu____23670
         then
           let uu____23675 =
             let uu____23681 =
               let uu____23683 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23683
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23681)  in
           let uu____23687 = get_range env  in
           FStar_Errors.raise_error uu____23675 uu____23687
         else ());
        (let uu____23690 = effect_repr_aux true env c u_c  in
         match uu____23690 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1680_23726 = env  in
        {
          solver = (uu___1680_23726.solver);
          range = (uu___1680_23726.range);
          curmodule = (uu___1680_23726.curmodule);
          gamma = (uu___1680_23726.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1680_23726.gamma_cache);
          modules = (uu___1680_23726.modules);
          expected_typ = (uu___1680_23726.expected_typ);
          sigtab = (uu___1680_23726.sigtab);
          attrtab = (uu___1680_23726.attrtab);
          instantiate_imp = (uu___1680_23726.instantiate_imp);
          effects = (uu___1680_23726.effects);
          generalize = (uu___1680_23726.generalize);
          letrecs = (uu___1680_23726.letrecs);
          top_level = (uu___1680_23726.top_level);
          check_uvars = (uu___1680_23726.check_uvars);
          use_eq = (uu___1680_23726.use_eq);
          use_eq_strict = (uu___1680_23726.use_eq_strict);
          is_iface = (uu___1680_23726.is_iface);
          admit = (uu___1680_23726.admit);
          lax = (uu___1680_23726.lax);
          lax_universes = (uu___1680_23726.lax_universes);
          phase1 = (uu___1680_23726.phase1);
          failhard = (uu___1680_23726.failhard);
          nosynth = (uu___1680_23726.nosynth);
          uvar_subtyping = (uu___1680_23726.uvar_subtyping);
          tc_term = (uu___1680_23726.tc_term);
          type_of = (uu___1680_23726.type_of);
          universe_of = (uu___1680_23726.universe_of);
          check_type_of = (uu___1680_23726.check_type_of);
          use_bv_sorts = (uu___1680_23726.use_bv_sorts);
          qtbl_name_and_index = (uu___1680_23726.qtbl_name_and_index);
          normalized_eff_names = (uu___1680_23726.normalized_eff_names);
          fv_delta_depths = (uu___1680_23726.fv_delta_depths);
          proof_ns = (uu___1680_23726.proof_ns);
          synth_hook = (uu___1680_23726.synth_hook);
          splice = (uu___1680_23726.splice);
          mpreprocess = (uu___1680_23726.mpreprocess);
          postprocess = (uu___1680_23726.postprocess);
          is_native_tactic = (uu___1680_23726.is_native_tactic);
          identifier_info = (uu___1680_23726.identifier_info);
          tc_hooks = (uu___1680_23726.tc_hooks);
          dsenv = (uu___1680_23726.dsenv);
          nbe = (uu___1680_23726.nbe);
          strict_args_tab = (uu___1680_23726.strict_args_tab);
          erasable_types_tab = (uu___1680_23726.erasable_types_tab)
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
    fun uu____23745  ->
      match uu____23745 with
      | (ed,quals) ->
          let effects =
            let uu___1689_23759 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1689_23759.order);
              joins = (uu___1689_23759.joins);
              polymonadic_binds = (uu___1689_23759.polymonadic_binds)
            }  in
          let uu___1692_23768 = env  in
          {
            solver = (uu___1692_23768.solver);
            range = (uu___1692_23768.range);
            curmodule = (uu___1692_23768.curmodule);
            gamma = (uu___1692_23768.gamma);
            gamma_sig = (uu___1692_23768.gamma_sig);
            gamma_cache = (uu___1692_23768.gamma_cache);
            modules = (uu___1692_23768.modules);
            expected_typ = (uu___1692_23768.expected_typ);
            sigtab = (uu___1692_23768.sigtab);
            attrtab = (uu___1692_23768.attrtab);
            instantiate_imp = (uu___1692_23768.instantiate_imp);
            effects;
            generalize = (uu___1692_23768.generalize);
            letrecs = (uu___1692_23768.letrecs);
            top_level = (uu___1692_23768.top_level);
            check_uvars = (uu___1692_23768.check_uvars);
            use_eq = (uu___1692_23768.use_eq);
            use_eq_strict = (uu___1692_23768.use_eq_strict);
            is_iface = (uu___1692_23768.is_iface);
            admit = (uu___1692_23768.admit);
            lax = (uu___1692_23768.lax);
            lax_universes = (uu___1692_23768.lax_universes);
            phase1 = (uu___1692_23768.phase1);
            failhard = (uu___1692_23768.failhard);
            nosynth = (uu___1692_23768.nosynth);
            uvar_subtyping = (uu___1692_23768.uvar_subtyping);
            tc_term = (uu___1692_23768.tc_term);
            type_of = (uu___1692_23768.type_of);
            universe_of = (uu___1692_23768.universe_of);
            check_type_of = (uu___1692_23768.check_type_of);
            use_bv_sorts = (uu___1692_23768.use_bv_sorts);
            qtbl_name_and_index = (uu___1692_23768.qtbl_name_and_index);
            normalized_eff_names = (uu___1692_23768.normalized_eff_names);
            fv_delta_depths = (uu___1692_23768.fv_delta_depths);
            proof_ns = (uu___1692_23768.proof_ns);
            synth_hook = (uu___1692_23768.synth_hook);
            splice = (uu___1692_23768.splice);
            mpreprocess = (uu___1692_23768.mpreprocess);
            postprocess = (uu___1692_23768.postprocess);
            is_native_tactic = (uu___1692_23768.is_native_tactic);
            identifier_info = (uu___1692_23768.identifier_info);
            tc_hooks = (uu___1692_23768.tc_hooks);
            dsenv = (uu___1692_23768.dsenv);
            nbe = (uu___1692_23768.nbe);
            strict_args_tab = (uu___1692_23768.strict_args_tab);
            erasable_types_tab = (uu___1692_23768.erasable_types_tab)
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
        let uu____23797 =
          FStar_All.pipe_right (env.effects).polymonadic_binds
            (FStar_Util.find_opt
               (fun uu____23865  ->
                  match uu____23865 with
                  | (m1,n11,uu____23883,uu____23884) ->
                      (FStar_Ident.lid_equals m m1) &&
                        (FStar_Ident.lid_equals n1 n11)))
           in
        match uu____23797 with
        | FStar_Pervasives_Native.Some (uu____23909,uu____23910,p,t) ->
            FStar_Pervasives_Native.Some (p, t)
        | uu____23955 -> FStar_Pervasives_Native.None
  
let (update_effect_lattice :
  env -> FStar_Ident.lident -> FStar_Ident.lident -> mlift -> env) =
  fun env  ->
    fun src  ->
      fun tgt  ->
        fun st_mlift  ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp env1 c =
                let uu____24030 =
                  FStar_All.pipe_right c ((e1.mlift).mlift_wp env1)  in
                FStar_All.pipe_right uu____24030
                  (fun uu____24051  ->
                     match uu____24051 with
                     | (c1,g1) ->
                         let uu____24062 =
                           FStar_All.pipe_right c1 ((e2.mlift).mlift_wp env1)
                            in
                         FStar_All.pipe_right uu____24062
                           (fun uu____24083  ->
                              match uu____24083 with
                              | (c2,g2) ->
                                  let uu____24094 =
                                    FStar_TypeChecker_Common.conj_guard g1 g2
                                     in
                                  (c2, uu____24094)))
                 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun e  ->
                              let uu____24216 = l1 u t e  in
                              l2 u t uu____24216))
                | uu____24217 -> FStar_Pervasives_Native.None  in
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
                 (fun uu____24285  ->
                    match uu____24285 with
                    | (e,uu____24293) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____24316 =
            match uu____24316 with
            | (i,j) ->
                let uu____24327 = FStar_Ident.lid_equals i j  in
                if uu____24327
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _24334  -> FStar_Pervasives_Native.Some _24334)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____24363 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____24373 = FStar_Ident.lid_equals i k  in
                        if uu____24373
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____24387 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____24387
                                  then []
                                  else
                                    (let uu____24394 =
                                       let uu____24403 =
                                         find_edge order1 (i, k)  in
                                       let uu____24406 =
                                         find_edge order1 (k, j)  in
                                       (uu____24403, uu____24406)  in
                                     match uu____24394 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____24421 =
                                           compose_edges e1 e2  in
                                         [uu____24421]
                                     | uu____24422 -> [])))))
                 in
              FStar_List.append order1 uu____24363  in
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
                  let uu____24452 =
                    (FStar_Ident.lid_equals edge1.msource
                       FStar_Parser_Const.effect_DIV_lid)
                      &&
                      (let uu____24455 =
                         lookup_effect_quals env edge1.mtarget  in
                       FStar_All.pipe_right uu____24455
                         (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                     in
                  if uu____24452
                  then
                    let uu____24462 =
                      let uu____24468 =
                        FStar_Util.format1
                          "Divergent computations cannot be included in an effect %s marked 'total'"
                          (edge1.mtarget).FStar_Ident.str
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____24468)
                       in
                    let uu____24472 = get_range env  in
                    FStar_Errors.raise_error uu____24462 uu____24472
                  else ()));
          (let joins =
             FStar_All.pipe_right ms
               (FStar_List.collect
                  (fun i  ->
                     FStar_All.pipe_right ms
                       (FStar_List.collect
                          (fun j  ->
                             let join_opt1 =
                               let uu____24550 = FStar_Ident.lid_equals i j
                                  in
                               if uu____24550
                               then
                                 FStar_Pervasives_Native.Some
                                   (i, (id_edge i), (id_edge i))
                               else
                                 FStar_All.pipe_right ms
                                   (FStar_List.fold_left
                                      (fun bopt  ->
                                         fun k  ->
                                           let uu____24602 =
                                             let uu____24611 =
                                               find_edge order2 (i, k)  in
                                             let uu____24614 =
                                               find_edge order2 (j, k)  in
                                             (uu____24611, uu____24614)  in
                                           match uu____24602 with
                                           | (FStar_Pervasives_Native.Some
                                              ik,FStar_Pervasives_Native.Some
                                              jk) ->
                                               (match bopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.Some
                                                      (k, ik, jk)
                                                | FStar_Pervasives_Native.Some
                                                    (ub,uu____24656,uu____24657)
                                                    ->
                                                    let uu____24664 =
                                                      let uu____24671 =
                                                        let uu____24673 =
                                                          find_edge order2
                                                            (k, ub)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24673
                                                         in
                                                      let uu____24676 =
                                                        let uu____24678 =
                                                          find_edge order2
                                                            (ub, k)
                                                           in
                                                        FStar_Util.is_some
                                                          uu____24678
                                                         in
                                                      (uu____24671,
                                                        uu____24676)
                                                       in
                                                    (match uu____24664 with
                                                     | (true ,true ) ->
                                                         let uu____24695 =
                                                           FStar_Ident.lid_equals
                                                             k ub
                                                            in
                                                         if uu____24695
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
                                           | uu____24738 -> bopt)
                                      FStar_Pervasives_Native.None)
                                in
                             match join_opt1 with
                             | FStar_Pervasives_Native.None  -> []
                             | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                 let uu____24790 =
                                   let uu____24792 =
                                     exists_polymonadic_bind env i j  in
                                   FStar_All.pipe_right uu____24792
                                     FStar_Util.is_some
                                    in
                                 if uu____24790
                                 then
                                   let uu____24841 =
                                     let uu____24847 =
                                       let uu____24849 =
                                         FStar_Ident.string_of_lid src  in
                                       let uu____24851 =
                                         FStar_Ident.string_of_lid tgt  in
                                       let uu____24853 =
                                         FStar_Ident.string_of_lid i  in
                                       let uu____24855 =
                                         FStar_Ident.string_of_lid j  in
                                       FStar_Util.format4
                                         "Updating effect lattice with a lift between %s and %s induces a path from %s and %s in the effect lattice, and this conflicts with a polymonadic bind between them"
                                         uu____24849 uu____24851 uu____24853
                                         uu____24855
                                        in
                                     (FStar_Errors.Fatal_PolymonadicBind_conflict,
                                       uu____24847)
                                      in
                                   FStar_Errors.raise_error uu____24841
                                     env.range
                                 else [(i, j, k, (e1.mlift), (e2.mlift))]))))
              in
           let effects =
             let uu___1813_24894 = env.effects  in
             {
               decls = (uu___1813_24894.decls);
               order = order2;
               joins;
               polymonadic_binds = (uu___1813_24894.polymonadic_binds)
             }  in
           let uu___1816_24895 = env  in
           {
             solver = (uu___1816_24895.solver);
             range = (uu___1816_24895.range);
             curmodule = (uu___1816_24895.curmodule);
             gamma = (uu___1816_24895.gamma);
             gamma_sig = (uu___1816_24895.gamma_sig);
             gamma_cache = (uu___1816_24895.gamma_cache);
             modules = (uu___1816_24895.modules);
             expected_typ = (uu___1816_24895.expected_typ);
             sigtab = (uu___1816_24895.sigtab);
             attrtab = (uu___1816_24895.attrtab);
             instantiate_imp = (uu___1816_24895.instantiate_imp);
             effects;
             generalize = (uu___1816_24895.generalize);
             letrecs = (uu___1816_24895.letrecs);
             top_level = (uu___1816_24895.top_level);
             check_uvars = (uu___1816_24895.check_uvars);
             use_eq = (uu___1816_24895.use_eq);
             use_eq_strict = (uu___1816_24895.use_eq_strict);
             is_iface = (uu___1816_24895.is_iface);
             admit = (uu___1816_24895.admit);
             lax = (uu___1816_24895.lax);
             lax_universes = (uu___1816_24895.lax_universes);
             phase1 = (uu___1816_24895.phase1);
             failhard = (uu___1816_24895.failhard);
             nosynth = (uu___1816_24895.nosynth);
             uvar_subtyping = (uu___1816_24895.uvar_subtyping);
             tc_term = (uu___1816_24895.tc_term);
             type_of = (uu___1816_24895.type_of);
             universe_of = (uu___1816_24895.universe_of);
             check_type_of = (uu___1816_24895.check_type_of);
             use_bv_sorts = (uu___1816_24895.use_bv_sorts);
             qtbl_name_and_index = (uu___1816_24895.qtbl_name_and_index);
             normalized_eff_names = (uu___1816_24895.normalized_eff_names);
             fv_delta_depths = (uu___1816_24895.fv_delta_depths);
             proof_ns = (uu___1816_24895.proof_ns);
             synth_hook = (uu___1816_24895.synth_hook);
             splice = (uu___1816_24895.splice);
             mpreprocess = (uu___1816_24895.mpreprocess);
             postprocess = (uu___1816_24895.postprocess);
             is_native_tactic = (uu___1816_24895.is_native_tactic);
             identifier_info = (uu___1816_24895.identifier_info);
             tc_hooks = (uu___1816_24895.tc_hooks);
             dsenv = (uu___1816_24895.dsenv);
             nbe = (uu___1816_24895.nbe);
             strict_args_tab = (uu___1816_24895.strict_args_tab);
             erasable_types_tab = (uu___1816_24895.erasable_types_tab)
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
              let uu____24943 = FStar_Ident.string_of_lid m  in
              let uu____24945 = FStar_Ident.string_of_lid n1  in
              let uu____24947 = FStar_Ident.string_of_lid p  in
              FStar_Util.format4
                "Polymonadic bind ((%s, %s) |> %s) conflicts with an already existing %s"
                uu____24943 uu____24945 uu____24947
                (if poly
                 then "polymonadic bind"
                 else "path in the effect lattice")
               in
            let uu____24956 =
              let uu____24958 = exists_polymonadic_bind env m n1  in
              FStar_All.pipe_right uu____24958 FStar_Util.is_some  in
            if uu____24956
            then
              let uu____24995 =
                let uu____25001 = err_msg true  in
                (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25001)
                 in
              FStar_Errors.raise_error uu____24995 env.range
            else
              (let uu____25007 =
                 let uu____25009 = join_opt env m n1  in
                 FStar_All.pipe_right uu____25009 FStar_Util.is_some  in
               if uu____25007
               then
                 let uu____25034 =
                   let uu____25040 = err_msg false  in
                   (FStar_Errors.Fatal_PolymonadicBind_conflict, uu____25040)
                    in
                 FStar_Errors.raise_error uu____25034 env.range
               else
                 (let uu___1831_25046 = env  in
                  {
                    solver = (uu___1831_25046.solver);
                    range = (uu___1831_25046.range);
                    curmodule = (uu___1831_25046.curmodule);
                    gamma = (uu___1831_25046.gamma);
                    gamma_sig = (uu___1831_25046.gamma_sig);
                    gamma_cache = (uu___1831_25046.gamma_cache);
                    modules = (uu___1831_25046.modules);
                    expected_typ = (uu___1831_25046.expected_typ);
                    sigtab = (uu___1831_25046.sigtab);
                    attrtab = (uu___1831_25046.attrtab);
                    instantiate_imp = (uu___1831_25046.instantiate_imp);
                    effects =
                      (let uu___1833_25048 = env.effects  in
                       {
                         decls = (uu___1833_25048.decls);
                         order = (uu___1833_25048.order);
                         joins = (uu___1833_25048.joins);
                         polymonadic_binds = ((m, n1, p, ty) ::
                           ((env.effects).polymonadic_binds))
                       });
                    generalize = (uu___1831_25046.generalize);
                    letrecs = (uu___1831_25046.letrecs);
                    top_level = (uu___1831_25046.top_level);
                    check_uvars = (uu___1831_25046.check_uvars);
                    use_eq = (uu___1831_25046.use_eq);
                    use_eq_strict = (uu___1831_25046.use_eq_strict);
                    is_iface = (uu___1831_25046.is_iface);
                    admit = (uu___1831_25046.admit);
                    lax = (uu___1831_25046.lax);
                    lax_universes = (uu___1831_25046.lax_universes);
                    phase1 = (uu___1831_25046.phase1);
                    failhard = (uu___1831_25046.failhard);
                    nosynth = (uu___1831_25046.nosynth);
                    uvar_subtyping = (uu___1831_25046.uvar_subtyping);
                    tc_term = (uu___1831_25046.tc_term);
                    type_of = (uu___1831_25046.type_of);
                    universe_of = (uu___1831_25046.universe_of);
                    check_type_of = (uu___1831_25046.check_type_of);
                    use_bv_sorts = (uu___1831_25046.use_bv_sorts);
                    qtbl_name_and_index =
                      (uu___1831_25046.qtbl_name_and_index);
                    normalized_eff_names =
                      (uu___1831_25046.normalized_eff_names);
                    fv_delta_depths = (uu___1831_25046.fv_delta_depths);
                    proof_ns = (uu___1831_25046.proof_ns);
                    synth_hook = (uu___1831_25046.synth_hook);
                    splice = (uu___1831_25046.splice);
                    mpreprocess = (uu___1831_25046.mpreprocess);
                    postprocess = (uu___1831_25046.postprocess);
                    is_native_tactic = (uu___1831_25046.is_native_tactic);
                    identifier_info = (uu___1831_25046.identifier_info);
                    tc_hooks = (uu___1831_25046.tc_hooks);
                    dsenv = (uu___1831_25046.dsenv);
                    nbe = (uu___1831_25046.nbe);
                    strict_args_tab = (uu___1831_25046.strict_args_tab);
                    erasable_types_tab = (uu___1831_25046.erasable_types_tab)
                  }))
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1837_25120 = env  in
      {
        solver = (uu___1837_25120.solver);
        range = (uu___1837_25120.range);
        curmodule = (uu___1837_25120.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1837_25120.gamma_sig);
        gamma_cache = (uu___1837_25120.gamma_cache);
        modules = (uu___1837_25120.modules);
        expected_typ = (uu___1837_25120.expected_typ);
        sigtab = (uu___1837_25120.sigtab);
        attrtab = (uu___1837_25120.attrtab);
        instantiate_imp = (uu___1837_25120.instantiate_imp);
        effects = (uu___1837_25120.effects);
        generalize = (uu___1837_25120.generalize);
        letrecs = (uu___1837_25120.letrecs);
        top_level = (uu___1837_25120.top_level);
        check_uvars = (uu___1837_25120.check_uvars);
        use_eq = (uu___1837_25120.use_eq);
        use_eq_strict = (uu___1837_25120.use_eq_strict);
        is_iface = (uu___1837_25120.is_iface);
        admit = (uu___1837_25120.admit);
        lax = (uu___1837_25120.lax);
        lax_universes = (uu___1837_25120.lax_universes);
        phase1 = (uu___1837_25120.phase1);
        failhard = (uu___1837_25120.failhard);
        nosynth = (uu___1837_25120.nosynth);
        uvar_subtyping = (uu___1837_25120.uvar_subtyping);
        tc_term = (uu___1837_25120.tc_term);
        type_of = (uu___1837_25120.type_of);
        universe_of = (uu___1837_25120.universe_of);
        check_type_of = (uu___1837_25120.check_type_of);
        use_bv_sorts = (uu___1837_25120.use_bv_sorts);
        qtbl_name_and_index = (uu___1837_25120.qtbl_name_and_index);
        normalized_eff_names = (uu___1837_25120.normalized_eff_names);
        fv_delta_depths = (uu___1837_25120.fv_delta_depths);
        proof_ns = (uu___1837_25120.proof_ns);
        synth_hook = (uu___1837_25120.synth_hook);
        splice = (uu___1837_25120.splice);
        mpreprocess = (uu___1837_25120.mpreprocess);
        postprocess = (uu___1837_25120.postprocess);
        is_native_tactic = (uu___1837_25120.is_native_tactic);
        identifier_info = (uu___1837_25120.identifier_info);
        tc_hooks = (uu___1837_25120.tc_hooks);
        dsenv = (uu___1837_25120.dsenv);
        nbe = (uu___1837_25120.nbe);
        strict_args_tab = (uu___1837_25120.strict_args_tab);
        erasable_types_tab = (uu___1837_25120.erasable_types_tab)
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
            (let uu___1850_25178 = env  in
             {
               solver = (uu___1850_25178.solver);
               range = (uu___1850_25178.range);
               curmodule = (uu___1850_25178.curmodule);
               gamma = rest;
               gamma_sig = (uu___1850_25178.gamma_sig);
               gamma_cache = (uu___1850_25178.gamma_cache);
               modules = (uu___1850_25178.modules);
               expected_typ = (uu___1850_25178.expected_typ);
               sigtab = (uu___1850_25178.sigtab);
               attrtab = (uu___1850_25178.attrtab);
               instantiate_imp = (uu___1850_25178.instantiate_imp);
               effects = (uu___1850_25178.effects);
               generalize = (uu___1850_25178.generalize);
               letrecs = (uu___1850_25178.letrecs);
               top_level = (uu___1850_25178.top_level);
               check_uvars = (uu___1850_25178.check_uvars);
               use_eq = (uu___1850_25178.use_eq);
               use_eq_strict = (uu___1850_25178.use_eq_strict);
               is_iface = (uu___1850_25178.is_iface);
               admit = (uu___1850_25178.admit);
               lax = (uu___1850_25178.lax);
               lax_universes = (uu___1850_25178.lax_universes);
               phase1 = (uu___1850_25178.phase1);
               failhard = (uu___1850_25178.failhard);
               nosynth = (uu___1850_25178.nosynth);
               uvar_subtyping = (uu___1850_25178.uvar_subtyping);
               tc_term = (uu___1850_25178.tc_term);
               type_of = (uu___1850_25178.type_of);
               universe_of = (uu___1850_25178.universe_of);
               check_type_of = (uu___1850_25178.check_type_of);
               use_bv_sorts = (uu___1850_25178.use_bv_sorts);
               qtbl_name_and_index = (uu___1850_25178.qtbl_name_and_index);
               normalized_eff_names = (uu___1850_25178.normalized_eff_names);
               fv_delta_depths = (uu___1850_25178.fv_delta_depths);
               proof_ns = (uu___1850_25178.proof_ns);
               synth_hook = (uu___1850_25178.synth_hook);
               splice = (uu___1850_25178.splice);
               mpreprocess = (uu___1850_25178.mpreprocess);
               postprocess = (uu___1850_25178.postprocess);
               is_native_tactic = (uu___1850_25178.is_native_tactic);
               identifier_info = (uu___1850_25178.identifier_info);
               tc_hooks = (uu___1850_25178.tc_hooks);
               dsenv = (uu___1850_25178.dsenv);
               nbe = (uu___1850_25178.nbe);
               strict_args_tab = (uu___1850_25178.strict_args_tab);
               erasable_types_tab = (uu___1850_25178.erasable_types_tab)
             }))
    | uu____25179 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____25208  ->
             match uu____25208 with | (x,uu____25216) -> push_bv env1 x) env
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
            let uu___1864_25251 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1864_25251.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1864_25251.FStar_Syntax_Syntax.index);
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
        let uu____25324 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____25324 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____25352 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____25352)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1885_25368 = env  in
      {
        solver = (uu___1885_25368.solver);
        range = (uu___1885_25368.range);
        curmodule = (uu___1885_25368.curmodule);
        gamma = (uu___1885_25368.gamma);
        gamma_sig = (uu___1885_25368.gamma_sig);
        gamma_cache = (uu___1885_25368.gamma_cache);
        modules = (uu___1885_25368.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1885_25368.sigtab);
        attrtab = (uu___1885_25368.attrtab);
        instantiate_imp = (uu___1885_25368.instantiate_imp);
        effects = (uu___1885_25368.effects);
        generalize = (uu___1885_25368.generalize);
        letrecs = (uu___1885_25368.letrecs);
        top_level = (uu___1885_25368.top_level);
        check_uvars = (uu___1885_25368.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1885_25368.use_eq_strict);
        is_iface = (uu___1885_25368.is_iface);
        admit = (uu___1885_25368.admit);
        lax = (uu___1885_25368.lax);
        lax_universes = (uu___1885_25368.lax_universes);
        phase1 = (uu___1885_25368.phase1);
        failhard = (uu___1885_25368.failhard);
        nosynth = (uu___1885_25368.nosynth);
        uvar_subtyping = (uu___1885_25368.uvar_subtyping);
        tc_term = (uu___1885_25368.tc_term);
        type_of = (uu___1885_25368.type_of);
        universe_of = (uu___1885_25368.universe_of);
        check_type_of = (uu___1885_25368.check_type_of);
        use_bv_sorts = (uu___1885_25368.use_bv_sorts);
        qtbl_name_and_index = (uu___1885_25368.qtbl_name_and_index);
        normalized_eff_names = (uu___1885_25368.normalized_eff_names);
        fv_delta_depths = (uu___1885_25368.fv_delta_depths);
        proof_ns = (uu___1885_25368.proof_ns);
        synth_hook = (uu___1885_25368.synth_hook);
        splice = (uu___1885_25368.splice);
        mpreprocess = (uu___1885_25368.mpreprocess);
        postprocess = (uu___1885_25368.postprocess);
        is_native_tactic = (uu___1885_25368.is_native_tactic);
        identifier_info = (uu___1885_25368.identifier_info);
        tc_hooks = (uu___1885_25368.tc_hooks);
        dsenv = (uu___1885_25368.dsenv);
        nbe = (uu___1885_25368.nbe);
        strict_args_tab = (uu___1885_25368.strict_args_tab);
        erasable_types_tab = (uu___1885_25368.erasable_types_tab)
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
    let uu____25399 = expected_typ env_  in
    ((let uu___1892_25405 = env_  in
      {
        solver = (uu___1892_25405.solver);
        range = (uu___1892_25405.range);
        curmodule = (uu___1892_25405.curmodule);
        gamma = (uu___1892_25405.gamma);
        gamma_sig = (uu___1892_25405.gamma_sig);
        gamma_cache = (uu___1892_25405.gamma_cache);
        modules = (uu___1892_25405.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1892_25405.sigtab);
        attrtab = (uu___1892_25405.attrtab);
        instantiate_imp = (uu___1892_25405.instantiate_imp);
        effects = (uu___1892_25405.effects);
        generalize = (uu___1892_25405.generalize);
        letrecs = (uu___1892_25405.letrecs);
        top_level = (uu___1892_25405.top_level);
        check_uvars = (uu___1892_25405.check_uvars);
        use_eq = false;
        use_eq_strict = (uu___1892_25405.use_eq_strict);
        is_iface = (uu___1892_25405.is_iface);
        admit = (uu___1892_25405.admit);
        lax = (uu___1892_25405.lax);
        lax_universes = (uu___1892_25405.lax_universes);
        phase1 = (uu___1892_25405.phase1);
        failhard = (uu___1892_25405.failhard);
        nosynth = (uu___1892_25405.nosynth);
        uvar_subtyping = (uu___1892_25405.uvar_subtyping);
        tc_term = (uu___1892_25405.tc_term);
        type_of = (uu___1892_25405.type_of);
        universe_of = (uu___1892_25405.universe_of);
        check_type_of = (uu___1892_25405.check_type_of);
        use_bv_sorts = (uu___1892_25405.use_bv_sorts);
        qtbl_name_and_index = (uu___1892_25405.qtbl_name_and_index);
        normalized_eff_names = (uu___1892_25405.normalized_eff_names);
        fv_delta_depths = (uu___1892_25405.fv_delta_depths);
        proof_ns = (uu___1892_25405.proof_ns);
        synth_hook = (uu___1892_25405.synth_hook);
        splice = (uu___1892_25405.splice);
        mpreprocess = (uu___1892_25405.mpreprocess);
        postprocess = (uu___1892_25405.postprocess);
        is_native_tactic = (uu___1892_25405.is_native_tactic);
        identifier_info = (uu___1892_25405.identifier_info);
        tc_hooks = (uu___1892_25405.tc_hooks);
        dsenv = (uu___1892_25405.dsenv);
        nbe = (uu___1892_25405.nbe);
        strict_args_tab = (uu___1892_25405.strict_args_tab);
        erasable_types_tab = (uu___1892_25405.erasable_types_tab)
      }), uu____25399)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____25417 =
      let uu____25420 = FStar_Ident.id_of_text ""  in [uu____25420]  in
    FStar_Ident.lid_of_ids uu____25417  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____25427 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____25427
        then
          let uu____25432 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____25432 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1900_25460 = env  in
       {
         solver = (uu___1900_25460.solver);
         range = (uu___1900_25460.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1900_25460.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1900_25460.expected_typ);
         sigtab = (uu___1900_25460.sigtab);
         attrtab = (uu___1900_25460.attrtab);
         instantiate_imp = (uu___1900_25460.instantiate_imp);
         effects = (uu___1900_25460.effects);
         generalize = (uu___1900_25460.generalize);
         letrecs = (uu___1900_25460.letrecs);
         top_level = (uu___1900_25460.top_level);
         check_uvars = (uu___1900_25460.check_uvars);
         use_eq = (uu___1900_25460.use_eq);
         use_eq_strict = (uu___1900_25460.use_eq_strict);
         is_iface = (uu___1900_25460.is_iface);
         admit = (uu___1900_25460.admit);
         lax = (uu___1900_25460.lax);
         lax_universes = (uu___1900_25460.lax_universes);
         phase1 = (uu___1900_25460.phase1);
         failhard = (uu___1900_25460.failhard);
         nosynth = (uu___1900_25460.nosynth);
         uvar_subtyping = (uu___1900_25460.uvar_subtyping);
         tc_term = (uu___1900_25460.tc_term);
         type_of = (uu___1900_25460.type_of);
         universe_of = (uu___1900_25460.universe_of);
         check_type_of = (uu___1900_25460.check_type_of);
         use_bv_sorts = (uu___1900_25460.use_bv_sorts);
         qtbl_name_and_index = (uu___1900_25460.qtbl_name_and_index);
         normalized_eff_names = (uu___1900_25460.normalized_eff_names);
         fv_delta_depths = (uu___1900_25460.fv_delta_depths);
         proof_ns = (uu___1900_25460.proof_ns);
         synth_hook = (uu___1900_25460.synth_hook);
         splice = (uu___1900_25460.splice);
         mpreprocess = (uu___1900_25460.mpreprocess);
         postprocess = (uu___1900_25460.postprocess);
         is_native_tactic = (uu___1900_25460.is_native_tactic);
         identifier_info = (uu___1900_25460.identifier_info);
         tc_hooks = (uu___1900_25460.tc_hooks);
         dsenv = (uu___1900_25460.dsenv);
         nbe = (uu___1900_25460.nbe);
         strict_args_tab = (uu___1900_25460.strict_args_tab);
         erasable_types_tab = (uu___1900_25460.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25512)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25516,(uu____25517,t)))::tl1
          ->
          let uu____25538 =
            let uu____25541 = FStar_Syntax_Free.uvars t  in
            ext out uu____25541  in
          aux uu____25538 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25544;
            FStar_Syntax_Syntax.index = uu____25545;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25553 =
            let uu____25556 = FStar_Syntax_Free.uvars t  in
            ext out uu____25556  in
          aux uu____25553 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____25614)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25618,(uu____25619,t)))::tl1
          ->
          let uu____25640 =
            let uu____25643 = FStar_Syntax_Free.univs t  in
            ext out uu____25643  in
          aux uu____25640 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25646;
            FStar_Syntax_Syntax.index = uu____25647;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25655 =
            let uu____25658 = FStar_Syntax_Free.univs t  in
            ext out uu____25658  in
          aux uu____25655 tl1
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
          let uu____25720 = FStar_Util.set_add uname out  in
          aux uu____25720 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____25723,(uu____25724,t)))::tl1
          ->
          let uu____25745 =
            let uu____25748 = FStar_Syntax_Free.univnames t  in
            ext out uu____25748  in
          aux uu____25745 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____25751;
            FStar_Syntax_Syntax.index = uu____25752;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____25760 =
            let uu____25763 = FStar_Syntax_Free.univnames t  in
            ext out uu____25763  in
          aux uu____25760 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_25784  ->
            match uu___12_25784 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____25788 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____25801 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____25812 =
      let uu____25821 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____25821
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____25812 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____25869 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_25882  ->
              match uu___13_25882 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____25885 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____25885
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____25891) ->
                  let uu____25908 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____25908))
       in
    FStar_All.pipe_right uu____25869 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_25922  ->
    match uu___14_25922 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____25928 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____25928
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____25951  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____26006) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____26039,uu____26040) -> false  in
      let uu____26054 =
        FStar_List.tryFind
          (fun uu____26076  ->
             match uu____26076 with | (p,uu____26087) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____26054 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____26106,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____26136 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____26136
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2043_26158 = e  in
        {
          solver = (uu___2043_26158.solver);
          range = (uu___2043_26158.range);
          curmodule = (uu___2043_26158.curmodule);
          gamma = (uu___2043_26158.gamma);
          gamma_sig = (uu___2043_26158.gamma_sig);
          gamma_cache = (uu___2043_26158.gamma_cache);
          modules = (uu___2043_26158.modules);
          expected_typ = (uu___2043_26158.expected_typ);
          sigtab = (uu___2043_26158.sigtab);
          attrtab = (uu___2043_26158.attrtab);
          instantiate_imp = (uu___2043_26158.instantiate_imp);
          effects = (uu___2043_26158.effects);
          generalize = (uu___2043_26158.generalize);
          letrecs = (uu___2043_26158.letrecs);
          top_level = (uu___2043_26158.top_level);
          check_uvars = (uu___2043_26158.check_uvars);
          use_eq = (uu___2043_26158.use_eq);
          use_eq_strict = (uu___2043_26158.use_eq_strict);
          is_iface = (uu___2043_26158.is_iface);
          admit = (uu___2043_26158.admit);
          lax = (uu___2043_26158.lax);
          lax_universes = (uu___2043_26158.lax_universes);
          phase1 = (uu___2043_26158.phase1);
          failhard = (uu___2043_26158.failhard);
          nosynth = (uu___2043_26158.nosynth);
          uvar_subtyping = (uu___2043_26158.uvar_subtyping);
          tc_term = (uu___2043_26158.tc_term);
          type_of = (uu___2043_26158.type_of);
          universe_of = (uu___2043_26158.universe_of);
          check_type_of = (uu___2043_26158.check_type_of);
          use_bv_sorts = (uu___2043_26158.use_bv_sorts);
          qtbl_name_and_index = (uu___2043_26158.qtbl_name_and_index);
          normalized_eff_names = (uu___2043_26158.normalized_eff_names);
          fv_delta_depths = (uu___2043_26158.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2043_26158.synth_hook);
          splice = (uu___2043_26158.splice);
          mpreprocess = (uu___2043_26158.mpreprocess);
          postprocess = (uu___2043_26158.postprocess);
          is_native_tactic = (uu___2043_26158.is_native_tactic);
          identifier_info = (uu___2043_26158.identifier_info);
          tc_hooks = (uu___2043_26158.tc_hooks);
          dsenv = (uu___2043_26158.dsenv);
          nbe = (uu___2043_26158.nbe);
          strict_args_tab = (uu___2043_26158.strict_args_tab);
          erasable_types_tab = (uu___2043_26158.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2052_26206 = e  in
      {
        solver = (uu___2052_26206.solver);
        range = (uu___2052_26206.range);
        curmodule = (uu___2052_26206.curmodule);
        gamma = (uu___2052_26206.gamma);
        gamma_sig = (uu___2052_26206.gamma_sig);
        gamma_cache = (uu___2052_26206.gamma_cache);
        modules = (uu___2052_26206.modules);
        expected_typ = (uu___2052_26206.expected_typ);
        sigtab = (uu___2052_26206.sigtab);
        attrtab = (uu___2052_26206.attrtab);
        instantiate_imp = (uu___2052_26206.instantiate_imp);
        effects = (uu___2052_26206.effects);
        generalize = (uu___2052_26206.generalize);
        letrecs = (uu___2052_26206.letrecs);
        top_level = (uu___2052_26206.top_level);
        check_uvars = (uu___2052_26206.check_uvars);
        use_eq = (uu___2052_26206.use_eq);
        use_eq_strict = (uu___2052_26206.use_eq_strict);
        is_iface = (uu___2052_26206.is_iface);
        admit = (uu___2052_26206.admit);
        lax = (uu___2052_26206.lax);
        lax_universes = (uu___2052_26206.lax_universes);
        phase1 = (uu___2052_26206.phase1);
        failhard = (uu___2052_26206.failhard);
        nosynth = (uu___2052_26206.nosynth);
        uvar_subtyping = (uu___2052_26206.uvar_subtyping);
        tc_term = (uu___2052_26206.tc_term);
        type_of = (uu___2052_26206.type_of);
        universe_of = (uu___2052_26206.universe_of);
        check_type_of = (uu___2052_26206.check_type_of);
        use_bv_sorts = (uu___2052_26206.use_bv_sorts);
        qtbl_name_and_index = (uu___2052_26206.qtbl_name_and_index);
        normalized_eff_names = (uu___2052_26206.normalized_eff_names);
        fv_delta_depths = (uu___2052_26206.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2052_26206.synth_hook);
        splice = (uu___2052_26206.splice);
        mpreprocess = (uu___2052_26206.mpreprocess);
        postprocess = (uu___2052_26206.postprocess);
        is_native_tactic = (uu___2052_26206.is_native_tactic);
        identifier_info = (uu___2052_26206.identifier_info);
        tc_hooks = (uu___2052_26206.tc_hooks);
        dsenv = (uu___2052_26206.dsenv);
        nbe = (uu___2052_26206.nbe);
        strict_args_tab = (uu___2052_26206.strict_args_tab);
        erasable_types_tab = (uu___2052_26206.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____26222 = FStar_Syntax_Free.names t  in
      let uu____26225 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____26222 uu____26225
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____26248 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____26248
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____26258 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____26258
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____26279 =
      match uu____26279 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____26299 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____26299)
       in
    let uu____26307 =
      let uu____26311 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____26311 FStar_List.rev  in
    FStar_All.pipe_right uu____26307 (FStar_String.concat " ")
  
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
                  (let uu____26379 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____26379 with
                   | FStar_Pervasives_Native.Some uu____26383 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____26386 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____26396;
        FStar_TypeChecker_Common.univ_ineqs = uu____26397;
        FStar_TypeChecker_Common.implicits = uu____26398;_} -> true
    | uu____26408 -> false
  
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
          let uu___2096_26430 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2096_26430.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2096_26430.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2096_26430.FStar_TypeChecker_Common.implicits)
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
          let uu____26469 = FStar_Options.defensive ()  in
          if uu____26469
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____26475 =
              let uu____26477 =
                let uu____26479 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____26479  in
              Prims.op_Negation uu____26477  in
            (if uu____26475
             then
               let uu____26486 =
                 let uu____26492 =
                   let uu____26494 = FStar_Syntax_Print.term_to_string t  in
                   let uu____26496 =
                     let uu____26498 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____26498
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____26494 uu____26496
                    in
                 (FStar_Errors.Warning_Defensive, uu____26492)  in
               FStar_Errors.log_issue rng uu____26486
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
          let uu____26538 =
            let uu____26540 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26540  in
          if uu____26538
          then ()
          else
            (let uu____26545 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____26545 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____26571 =
            let uu____26573 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____26573  in
          if uu____26571
          then ()
          else
            (let uu____26578 = bound_vars e  in
             def_check_closed_in rng msg uu____26578 t)
  
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
          let uu___2133_26617 = g  in
          let uu____26618 =
            let uu____26619 =
              let uu____26620 =
                let uu____26627 =
                  let uu____26628 =
                    let uu____26645 =
                      let uu____26656 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____26656]  in
                    (f, uu____26645)  in
                  FStar_Syntax_Syntax.Tm_app uu____26628  in
                FStar_Syntax_Syntax.mk uu____26627  in
              uu____26620 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _26693  -> FStar_TypeChecker_Common.NonTrivial _26693)
              uu____26619
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____26618;
            FStar_TypeChecker_Common.deferred =
              (uu___2133_26617.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2133_26617.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2133_26617.FStar_TypeChecker_Common.implicits)
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
          let uu___2140_26711 = g  in
          let uu____26712 =
            let uu____26713 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26713  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26712;
            FStar_TypeChecker_Common.deferred =
              (uu___2140_26711.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2140_26711.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2140_26711.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2145_26730 = g  in
          let uu____26731 =
            let uu____26732 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____26732  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26731;
            FStar_TypeChecker_Common.deferred =
              (uu___2145_26730.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2145_26730.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2145_26730.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2149_26734 = g  in
          let uu____26735 =
            let uu____26736 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____26736  in
          {
            FStar_TypeChecker_Common.guard_f = uu____26735;
            FStar_TypeChecker_Common.deferred =
              (uu___2149_26734.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2149_26734.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2149_26734.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____26743 ->
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
                       let uu____26820 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____26820
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2172_26827 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2172_26827.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2172_26827.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2172_26827.FStar_TypeChecker_Common.implicits)
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
               let uu____26861 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____26861
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
            let uu___2187_26888 = g  in
            let uu____26889 =
              let uu____26890 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____26890  in
            {
              FStar_TypeChecker_Common.guard_f = uu____26889;
              FStar_TypeChecker_Common.deferred =
                (uu___2187_26888.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2187_26888.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2187_26888.FStar_TypeChecker_Common.implicits)
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
              let uu____26948 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____26948 with
              | FStar_Pervasives_Native.Some
                  (uu____26973::(tm,uu____26975)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____27039 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____27057 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____27057;
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
                      let uu___2209_27089 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2209_27089.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2209_27089.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2209_27089.FStar_TypeChecker_Common.univ_ineqs);
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
            let uu____27143 =
              FStar_All.pipe_right bs
                (FStar_List.fold_left
                   (fun uu____27200  ->
                      fun b  ->
                        match uu____27200 with
                        | (substs1,uvars1,g) ->
                            let sort =
                              FStar_Syntax_Subst.subst substs1
                                (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                               in
                            let uu____27242 =
                              let uu____27255 = reason b  in
                              new_implicit_var_aux uu____27255 r env sort
                                FStar_Syntax_Syntax.Allow_untyped
                                FStar_Pervasives_Native.None
                               in
                            (match uu____27242 with
                             | (t,uu____27272,g_t) ->
                                 let uu____27286 =
                                   let uu____27289 =
                                     let uu____27292 =
                                       let uu____27293 =
                                         let uu____27300 =
                                           FStar_All.pipe_right b
                                             FStar_Pervasives_Native.fst
                                            in
                                         (uu____27300, t)  in
                                       FStar_Syntax_Syntax.NT uu____27293  in
                                     [uu____27292]  in
                                   FStar_List.append substs1 uu____27289  in
                                 let uu____27311 = conj_guard g g_t  in
                                 (uu____27286,
                                   (FStar_List.append uvars1 [t]),
                                   uu____27311))) (substs, [], trivial_guard))
               in
            FStar_All.pipe_right uu____27143
              (fun uu____27340  ->
                 match uu____27340 with
                 | (uu____27357,uvars1,g) -> (uvars1, g))
  
let (pure_precondition_for_trivial_post :
  env ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun u  ->
      fun t  ->
        fun wp  ->
          fun r  ->
            let trivial_post =
              let post_ts =
                let uu____27398 =
                  lookup_definition [NoDelta] env
                    FStar_Parser_Const.trivial_pure_post_lid
                   in
                FStar_All.pipe_right uu____27398 FStar_Util.must  in
              let uu____27415 = inst_tscheme_with post_ts [u]  in
              match uu____27415 with
              | (uu____27420,post) ->
                  let uu____27422 =
                    let uu____27427 =
                      let uu____27428 =
                        FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                      [uu____27428]  in
                    FStar_Syntax_Syntax.mk_Tm_app post uu____27427  in
                  uu____27422 FStar_Pervasives_Native.None r
               in
            let uu____27461 =
              let uu____27466 =
                let uu____27467 =
                  FStar_All.pipe_right trivial_post
                    FStar_Syntax_Syntax.as_arg
                   in
                [uu____27467]  in
              FStar_Syntax_Syntax.mk_Tm_app wp uu____27466  in
            uu____27461 FStar_Pervasives_Native.None r
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____27503  -> ());
    push = (fun uu____27505  -> ());
    pop = (fun uu____27508  -> ());
    snapshot =
      (fun uu____27511  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____27530  -> fun uu____27531  -> ());
    encode_sig = (fun uu____27546  -> fun uu____27547  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____27553 =
             let uu____27560 = FStar_Options.peek ()  in (e, g, uu____27560)
              in
           [uu____27553]);
    solve = (fun uu____27576  -> fun uu____27577  -> fun uu____27578  -> ());
    finish = (fun uu____27585  -> ());
    refresh = (fun uu____27587  -> ())
  } 