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
  fun projectee  -> match projectee with | Beta  -> true | uu____110 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____121 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____132 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____144 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____162 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____173 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____184 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____195 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____206 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____217 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____229 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____250 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____277 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____304 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____328 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____339 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____350 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____361 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____372 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____383 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____394 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____405 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____416 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____427 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____438 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____449 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____460 -> false
  
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
      | uu____520 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____546 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____557 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____568 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____580 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_wp; mlift_term;_} -> mlift_term
  
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with | { msource; mtarget; mlift;_} -> mlift
  
type effects =
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
type name_prefix = Prims.string Prims.list
type proof_namespace = (name_prefix * Prims.bool) Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ),(FStar_Syntax_Syntax.sigelt
                                                                *
                                                                FStar_Syntax_Syntax.universes
                                                                FStar_Pervasives_Native.option))
    FStar_Util.either * FStar_Range.range)
type goal = FStar_Syntax_Syntax.term
type env =
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
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t)
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t)
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
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
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list)
    ;
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> curmodule
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> gamma_cache
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> modules
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> expected_typ
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> sigtab
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> attrtab
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> type_of
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> qtbl_name_and_index
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> normalized_eff_names
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> splice1
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> postprocess
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> is_native_tactic
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; instantiate_imp; effects; generalize;
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
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
        letrecs; top_level; check_uvars; use_eq; is_iface; admit = admit1;
        lax = lax1; lax_universes; phase1; failhard; nosynth; uvar_subtyping;
        tc_term; type_of; universe_of; check_type_of; use_bv_sorts;
        qtbl_name_and_index; normalized_eff_names; fv_delta_depths; proof_ns;
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> nbe1
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
        identifier_info; tc_hooks; dsenv; nbe = nbe1; strict_args_tab;
        erasable_types_tab;_} -> strict_args_tab
  
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
        synth_hook; splice = splice1; postprocess; is_native_tactic;
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
  
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> guard_f
  
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list *
      FStar_TypeChecker_Common.univ_ineq Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> univ_ineqs
  
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee  ->
    match projectee with
    | { guard_f; deferred; univ_ineqs; implicits;_} -> implicits
  
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range;_} -> imp_range
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
  
type solver_depth_t = (Prims.int * Prims.int * Prims.int)
type implicits = implicit Prims.list
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
           (fun uu___0_12464  ->
              match uu___0_12464 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12467 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12467  in
                  let uu____12468 =
                    let uu____12469 = FStar_Syntax_Subst.compress y  in
                    uu____12469.FStar_Syntax_Syntax.n  in
                  (match uu____12468 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12473 =
                         let uu___332_12474 = y1  in
                         let uu____12475 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___332_12474.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___332_12474.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12475
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12473
                   | uu____12478 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___338_12492 = env  in
      let uu____12493 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___338_12492.solver);
        range = (uu___338_12492.range);
        curmodule = (uu___338_12492.curmodule);
        gamma = uu____12493;
        gamma_sig = (uu___338_12492.gamma_sig);
        gamma_cache = (uu___338_12492.gamma_cache);
        modules = (uu___338_12492.modules);
        expected_typ = (uu___338_12492.expected_typ);
        sigtab = (uu___338_12492.sigtab);
        attrtab = (uu___338_12492.attrtab);
        instantiate_imp = (uu___338_12492.instantiate_imp);
        effects = (uu___338_12492.effects);
        generalize = (uu___338_12492.generalize);
        letrecs = (uu___338_12492.letrecs);
        top_level = (uu___338_12492.top_level);
        check_uvars = (uu___338_12492.check_uvars);
        use_eq = (uu___338_12492.use_eq);
        is_iface = (uu___338_12492.is_iface);
        admit = (uu___338_12492.admit);
        lax = (uu___338_12492.lax);
        lax_universes = (uu___338_12492.lax_universes);
        phase1 = (uu___338_12492.phase1);
        failhard = (uu___338_12492.failhard);
        nosynth = (uu___338_12492.nosynth);
        uvar_subtyping = (uu___338_12492.uvar_subtyping);
        tc_term = (uu___338_12492.tc_term);
        type_of = (uu___338_12492.type_of);
        universe_of = (uu___338_12492.universe_of);
        check_type_of = (uu___338_12492.check_type_of);
        use_bv_sorts = (uu___338_12492.use_bv_sorts);
        qtbl_name_and_index = (uu___338_12492.qtbl_name_and_index);
        normalized_eff_names = (uu___338_12492.normalized_eff_names);
        fv_delta_depths = (uu___338_12492.fv_delta_depths);
        proof_ns = (uu___338_12492.proof_ns);
        synth_hook = (uu___338_12492.synth_hook);
        splice = (uu___338_12492.splice);
        postprocess = (uu___338_12492.postprocess);
        is_native_tactic = (uu___338_12492.is_native_tactic);
        identifier_info = (uu___338_12492.identifier_info);
        tc_hooks = (uu___338_12492.tc_hooks);
        dsenv = (uu___338_12492.dsenv);
        nbe = (uu___338_12492.nbe);
        strict_args_tab = (uu___338_12492.strict_args_tab);
        erasable_types_tab = (uu___338_12492.erasable_types_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12501  -> fun uu____12502  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___345_12524 = env  in
      {
        solver = (uu___345_12524.solver);
        range = (uu___345_12524.range);
        curmodule = (uu___345_12524.curmodule);
        gamma = (uu___345_12524.gamma);
        gamma_sig = (uu___345_12524.gamma_sig);
        gamma_cache = (uu___345_12524.gamma_cache);
        modules = (uu___345_12524.modules);
        expected_typ = (uu___345_12524.expected_typ);
        sigtab = (uu___345_12524.sigtab);
        attrtab = (uu___345_12524.attrtab);
        instantiate_imp = (uu___345_12524.instantiate_imp);
        effects = (uu___345_12524.effects);
        generalize = (uu___345_12524.generalize);
        letrecs = (uu___345_12524.letrecs);
        top_level = (uu___345_12524.top_level);
        check_uvars = (uu___345_12524.check_uvars);
        use_eq = (uu___345_12524.use_eq);
        is_iface = (uu___345_12524.is_iface);
        admit = (uu___345_12524.admit);
        lax = (uu___345_12524.lax);
        lax_universes = (uu___345_12524.lax_universes);
        phase1 = (uu___345_12524.phase1);
        failhard = (uu___345_12524.failhard);
        nosynth = (uu___345_12524.nosynth);
        uvar_subtyping = (uu___345_12524.uvar_subtyping);
        tc_term = (uu___345_12524.tc_term);
        type_of = (uu___345_12524.type_of);
        universe_of = (uu___345_12524.universe_of);
        check_type_of = (uu___345_12524.check_type_of);
        use_bv_sorts = (uu___345_12524.use_bv_sorts);
        qtbl_name_and_index = (uu___345_12524.qtbl_name_and_index);
        normalized_eff_names = (uu___345_12524.normalized_eff_names);
        fv_delta_depths = (uu___345_12524.fv_delta_depths);
        proof_ns = (uu___345_12524.proof_ns);
        synth_hook = (uu___345_12524.synth_hook);
        splice = (uu___345_12524.splice);
        postprocess = (uu___345_12524.postprocess);
        is_native_tactic = (uu___345_12524.is_native_tactic);
        identifier_info = (uu___345_12524.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___345_12524.dsenv);
        nbe = (uu___345_12524.nbe);
        strict_args_tab = (uu___345_12524.strict_args_tab);
        erasable_types_tab = (uu___345_12524.erasable_types_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___349_12536 = e  in
      let uu____12537 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___349_12536.solver);
        range = (uu___349_12536.range);
        curmodule = (uu___349_12536.curmodule);
        gamma = (uu___349_12536.gamma);
        gamma_sig = (uu___349_12536.gamma_sig);
        gamma_cache = (uu___349_12536.gamma_cache);
        modules = (uu___349_12536.modules);
        expected_typ = (uu___349_12536.expected_typ);
        sigtab = (uu___349_12536.sigtab);
        attrtab = (uu___349_12536.attrtab);
        instantiate_imp = (uu___349_12536.instantiate_imp);
        effects = (uu___349_12536.effects);
        generalize = (uu___349_12536.generalize);
        letrecs = (uu___349_12536.letrecs);
        top_level = (uu___349_12536.top_level);
        check_uvars = (uu___349_12536.check_uvars);
        use_eq = (uu___349_12536.use_eq);
        is_iface = (uu___349_12536.is_iface);
        admit = (uu___349_12536.admit);
        lax = (uu___349_12536.lax);
        lax_universes = (uu___349_12536.lax_universes);
        phase1 = (uu___349_12536.phase1);
        failhard = (uu___349_12536.failhard);
        nosynth = (uu___349_12536.nosynth);
        uvar_subtyping = (uu___349_12536.uvar_subtyping);
        tc_term = (uu___349_12536.tc_term);
        type_of = (uu___349_12536.type_of);
        universe_of = (uu___349_12536.universe_of);
        check_type_of = (uu___349_12536.check_type_of);
        use_bv_sorts = (uu___349_12536.use_bv_sorts);
        qtbl_name_and_index = (uu___349_12536.qtbl_name_and_index);
        normalized_eff_names = (uu___349_12536.normalized_eff_names);
        fv_delta_depths = (uu___349_12536.fv_delta_depths);
        proof_ns = (uu___349_12536.proof_ns);
        synth_hook = (uu___349_12536.synth_hook);
        splice = (uu___349_12536.splice);
        postprocess = (uu___349_12536.postprocess);
        is_native_tactic = (uu___349_12536.is_native_tactic);
        identifier_info = (uu___349_12536.identifier_info);
        tc_hooks = (uu___349_12536.tc_hooks);
        dsenv = uu____12537;
        nbe = (uu___349_12536.nbe);
        strict_args_tab = (uu___349_12536.strict_args_tab);
        erasable_types_tab = (uu___349_12536.erasable_types_tab)
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
      | (NoDelta ,uu____12566) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12569,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12571,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12574 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____12588 . unit -> 'Auu____12588 FStar_Util.smap =
  fun uu____12595  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12601 . unit -> 'Auu____12601 FStar_Util.smap =
  fun uu____12608  -> FStar_Util.smap_create (Prims.of_int (100)) 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))
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
                  let uu____12746 = new_gamma_cache ()  in
                  let uu____12749 = new_sigtab ()  in
                  let uu____12752 = new_sigtab ()  in
                  let uu____12759 =
                    let uu____12774 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____12774, FStar_Pervasives_Native.None)  in
                  let uu____12795 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12799 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____12803 = FStar_Options.using_facts_from ()  in
                  let uu____12804 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12807 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____12808 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____12822 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12746;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12749;
                    attrtab = uu____12752;
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
                    qtbl_name_and_index = uu____12759;
                    normalized_eff_names = uu____12795;
                    fv_delta_depths = uu____12799;
                    proof_ns = uu____12803;
                    synth_hook =
                      (fun e  ->
                         fun g  ->
                           fun tau  -> failwith "no synthesizer available");
                    splice =
                      (fun e  -> fun tau  -> failwith "no splicer available");
                    postprocess =
                      (fun e  ->
                         fun tau  ->
                           fun typ  ->
                             fun tm  -> failwith "no postprocessor available");
                    is_native_tactic = (fun uu____12888  -> false);
                    identifier_info = uu____12804;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12807;
                    nbe = nbe1;
                    strict_args_tab = uu____12808;
                    erasable_types_tab = uu____12822
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
  fun uu____12967  ->
    let uu____12968 = FStar_ST.op_Bang query_indices  in
    match uu____12968 with
    | [] -> failwith "Empty query indices!"
    | uu____13023 ->
        let uu____13033 =
          let uu____13043 =
            let uu____13051 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13051  in
          let uu____13105 = FStar_ST.op_Bang query_indices  in uu____13043 ::
            uu____13105
           in
        FStar_ST.op_Colon_Equals query_indices uu____13033
  
let (pop_query_indices : unit -> unit) =
  fun uu____13201  ->
    let uu____13202 = FStar_ST.op_Bang query_indices  in
    match uu____13202 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13329  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13366  ->
    match uu____13366 with
    | (l,n1) ->
        let uu____13376 = FStar_ST.op_Bang query_indices  in
        (match uu____13376 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13498 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13521  ->
    let uu____13522 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13522
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13590 =
       let uu____13593 = FStar_ST.op_Bang stack  in env :: uu____13593  in
     FStar_ST.op_Colon_Equals stack uu____13590);
    (let uu___417_13642 = env  in
     let uu____13643 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13646 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13649 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13656 =
       let uu____13671 =
         let uu____13675 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13675  in
       let uu____13707 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13671, uu____13707)  in
     let uu____13756 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13759 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13762 =
       let uu____13765 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13765  in
     let uu____13785 = FStar_Util.smap_copy env.strict_args_tab  in
     let uu____13798 = FStar_Util.smap_copy env.erasable_types_tab  in
     {
       solver = (uu___417_13642.solver);
       range = (uu___417_13642.range);
       curmodule = (uu___417_13642.curmodule);
       gamma = (uu___417_13642.gamma);
       gamma_sig = (uu___417_13642.gamma_sig);
       gamma_cache = uu____13643;
       modules = (uu___417_13642.modules);
       expected_typ = (uu___417_13642.expected_typ);
       sigtab = uu____13646;
       attrtab = uu____13649;
       instantiate_imp = (uu___417_13642.instantiate_imp);
       effects = (uu___417_13642.effects);
       generalize = (uu___417_13642.generalize);
       letrecs = (uu___417_13642.letrecs);
       top_level = (uu___417_13642.top_level);
       check_uvars = (uu___417_13642.check_uvars);
       use_eq = (uu___417_13642.use_eq);
       is_iface = (uu___417_13642.is_iface);
       admit = (uu___417_13642.admit);
       lax = (uu___417_13642.lax);
       lax_universes = (uu___417_13642.lax_universes);
       phase1 = (uu___417_13642.phase1);
       failhard = (uu___417_13642.failhard);
       nosynth = (uu___417_13642.nosynth);
       uvar_subtyping = (uu___417_13642.uvar_subtyping);
       tc_term = (uu___417_13642.tc_term);
       type_of = (uu___417_13642.type_of);
       universe_of = (uu___417_13642.universe_of);
       check_type_of = (uu___417_13642.check_type_of);
       use_bv_sorts = (uu___417_13642.use_bv_sorts);
       qtbl_name_and_index = uu____13656;
       normalized_eff_names = uu____13756;
       fv_delta_depths = uu____13759;
       proof_ns = (uu___417_13642.proof_ns);
       synth_hook = (uu___417_13642.synth_hook);
       splice = (uu___417_13642.splice);
       postprocess = (uu___417_13642.postprocess);
       is_native_tactic = (uu___417_13642.is_native_tactic);
       identifier_info = uu____13762;
       tc_hooks = (uu___417_13642.tc_hooks);
       dsenv = (uu___417_13642.dsenv);
       nbe = (uu___417_13642.nbe);
       strict_args_tab = uu____13785;
       erasable_types_tab = uu____13798
     })
  
let (pop_stack : unit -> env) =
  fun uu____13808  ->
    let uu____13809 = FStar_ST.op_Bang stack  in
    match uu____13809 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13863 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13953  ->
           let uu____13954 = snapshot_stack env  in
           match uu____13954 with
           | (stack_depth,env1) ->
               let uu____13988 = snapshot_query_indices ()  in
               (match uu____13988 with
                | (query_indices_depth,()) ->
                    let uu____14021 = (env1.solver).snapshot msg  in
                    (match uu____14021 with
                     | (solver_depth,()) ->
                         let uu____14078 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14078 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___442_14145 = env1  in
                                 {
                                   solver = (uu___442_14145.solver);
                                   range = (uu___442_14145.range);
                                   curmodule = (uu___442_14145.curmodule);
                                   gamma = (uu___442_14145.gamma);
                                   gamma_sig = (uu___442_14145.gamma_sig);
                                   gamma_cache = (uu___442_14145.gamma_cache);
                                   modules = (uu___442_14145.modules);
                                   expected_typ =
                                     (uu___442_14145.expected_typ);
                                   sigtab = (uu___442_14145.sigtab);
                                   attrtab = (uu___442_14145.attrtab);
                                   instantiate_imp =
                                     (uu___442_14145.instantiate_imp);
                                   effects = (uu___442_14145.effects);
                                   generalize = (uu___442_14145.generalize);
                                   letrecs = (uu___442_14145.letrecs);
                                   top_level = (uu___442_14145.top_level);
                                   check_uvars = (uu___442_14145.check_uvars);
                                   use_eq = (uu___442_14145.use_eq);
                                   is_iface = (uu___442_14145.is_iface);
                                   admit = (uu___442_14145.admit);
                                   lax = (uu___442_14145.lax);
                                   lax_universes =
                                     (uu___442_14145.lax_universes);
                                   phase1 = (uu___442_14145.phase1);
                                   failhard = (uu___442_14145.failhard);
                                   nosynth = (uu___442_14145.nosynth);
                                   uvar_subtyping =
                                     (uu___442_14145.uvar_subtyping);
                                   tc_term = (uu___442_14145.tc_term);
                                   type_of = (uu___442_14145.type_of);
                                   universe_of = (uu___442_14145.universe_of);
                                   check_type_of =
                                     (uu___442_14145.check_type_of);
                                   use_bv_sorts =
                                     (uu___442_14145.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___442_14145.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___442_14145.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___442_14145.fv_delta_depths);
                                   proof_ns = (uu___442_14145.proof_ns);
                                   synth_hook = (uu___442_14145.synth_hook);
                                   splice = (uu___442_14145.splice);
                                   postprocess = (uu___442_14145.postprocess);
                                   is_native_tactic =
                                     (uu___442_14145.is_native_tactic);
                                   identifier_info =
                                     (uu___442_14145.identifier_info);
                                   tc_hooks = (uu___442_14145.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___442_14145.nbe);
                                   strict_args_tab =
                                     (uu___442_14145.strict_args_tab);
                                   erasable_types_tab =
                                     (uu___442_14145.erasable_types_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14179  ->
             let uu____14180 =
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
             match uu____14180 with
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
                             ((let uu____14360 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14360
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14376 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14376
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14408,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14450 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14480  ->
                  match uu____14480 with
                  | (m,uu____14488) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14450 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___487_14503 = env  in
               {
                 solver = (uu___487_14503.solver);
                 range = (uu___487_14503.range);
                 curmodule = (uu___487_14503.curmodule);
                 gamma = (uu___487_14503.gamma);
                 gamma_sig = (uu___487_14503.gamma_sig);
                 gamma_cache = (uu___487_14503.gamma_cache);
                 modules = (uu___487_14503.modules);
                 expected_typ = (uu___487_14503.expected_typ);
                 sigtab = (uu___487_14503.sigtab);
                 attrtab = (uu___487_14503.attrtab);
                 instantiate_imp = (uu___487_14503.instantiate_imp);
                 effects = (uu___487_14503.effects);
                 generalize = (uu___487_14503.generalize);
                 letrecs = (uu___487_14503.letrecs);
                 top_level = (uu___487_14503.top_level);
                 check_uvars = (uu___487_14503.check_uvars);
                 use_eq = (uu___487_14503.use_eq);
                 is_iface = (uu___487_14503.is_iface);
                 admit = (uu___487_14503.admit);
                 lax = (uu___487_14503.lax);
                 lax_universes = (uu___487_14503.lax_universes);
                 phase1 = (uu___487_14503.phase1);
                 failhard = (uu___487_14503.failhard);
                 nosynth = (uu___487_14503.nosynth);
                 uvar_subtyping = (uu___487_14503.uvar_subtyping);
                 tc_term = (uu___487_14503.tc_term);
                 type_of = (uu___487_14503.type_of);
                 universe_of = (uu___487_14503.universe_of);
                 check_type_of = (uu___487_14503.check_type_of);
                 use_bv_sorts = (uu___487_14503.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___487_14503.normalized_eff_names);
                 fv_delta_depths = (uu___487_14503.fv_delta_depths);
                 proof_ns = (uu___487_14503.proof_ns);
                 synth_hook = (uu___487_14503.synth_hook);
                 splice = (uu___487_14503.splice);
                 postprocess = (uu___487_14503.postprocess);
                 is_native_tactic = (uu___487_14503.is_native_tactic);
                 identifier_info = (uu___487_14503.identifier_info);
                 tc_hooks = (uu___487_14503.tc_hooks);
                 dsenv = (uu___487_14503.dsenv);
                 nbe = (uu___487_14503.nbe);
                 strict_args_tab = (uu___487_14503.strict_args_tab);
                 erasable_types_tab = (uu___487_14503.erasable_types_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14520,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___496_14536 = env  in
               {
                 solver = (uu___496_14536.solver);
                 range = (uu___496_14536.range);
                 curmodule = (uu___496_14536.curmodule);
                 gamma = (uu___496_14536.gamma);
                 gamma_sig = (uu___496_14536.gamma_sig);
                 gamma_cache = (uu___496_14536.gamma_cache);
                 modules = (uu___496_14536.modules);
                 expected_typ = (uu___496_14536.expected_typ);
                 sigtab = (uu___496_14536.sigtab);
                 attrtab = (uu___496_14536.attrtab);
                 instantiate_imp = (uu___496_14536.instantiate_imp);
                 effects = (uu___496_14536.effects);
                 generalize = (uu___496_14536.generalize);
                 letrecs = (uu___496_14536.letrecs);
                 top_level = (uu___496_14536.top_level);
                 check_uvars = (uu___496_14536.check_uvars);
                 use_eq = (uu___496_14536.use_eq);
                 is_iface = (uu___496_14536.is_iface);
                 admit = (uu___496_14536.admit);
                 lax = (uu___496_14536.lax);
                 lax_universes = (uu___496_14536.lax_universes);
                 phase1 = (uu___496_14536.phase1);
                 failhard = (uu___496_14536.failhard);
                 nosynth = (uu___496_14536.nosynth);
                 uvar_subtyping = (uu___496_14536.uvar_subtyping);
                 tc_term = (uu___496_14536.tc_term);
                 type_of = (uu___496_14536.type_of);
                 universe_of = (uu___496_14536.universe_of);
                 check_type_of = (uu___496_14536.check_type_of);
                 use_bv_sorts = (uu___496_14536.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___496_14536.normalized_eff_names);
                 fv_delta_depths = (uu___496_14536.fv_delta_depths);
                 proof_ns = (uu___496_14536.proof_ns);
                 synth_hook = (uu___496_14536.synth_hook);
                 splice = (uu___496_14536.splice);
                 postprocess = (uu___496_14536.postprocess);
                 is_native_tactic = (uu___496_14536.is_native_tactic);
                 identifier_info = (uu___496_14536.identifier_info);
                 tc_hooks = (uu___496_14536.tc_hooks);
                 dsenv = (uu___496_14536.dsenv);
                 nbe = (uu___496_14536.nbe);
                 strict_args_tab = (uu___496_14536.strict_args_tab);
                 erasable_types_tab = (uu___496_14536.erasable_types_tab)
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
        (let uu___503_14579 = e  in
         {
           solver = (uu___503_14579.solver);
           range = r;
           curmodule = (uu___503_14579.curmodule);
           gamma = (uu___503_14579.gamma);
           gamma_sig = (uu___503_14579.gamma_sig);
           gamma_cache = (uu___503_14579.gamma_cache);
           modules = (uu___503_14579.modules);
           expected_typ = (uu___503_14579.expected_typ);
           sigtab = (uu___503_14579.sigtab);
           attrtab = (uu___503_14579.attrtab);
           instantiate_imp = (uu___503_14579.instantiate_imp);
           effects = (uu___503_14579.effects);
           generalize = (uu___503_14579.generalize);
           letrecs = (uu___503_14579.letrecs);
           top_level = (uu___503_14579.top_level);
           check_uvars = (uu___503_14579.check_uvars);
           use_eq = (uu___503_14579.use_eq);
           is_iface = (uu___503_14579.is_iface);
           admit = (uu___503_14579.admit);
           lax = (uu___503_14579.lax);
           lax_universes = (uu___503_14579.lax_universes);
           phase1 = (uu___503_14579.phase1);
           failhard = (uu___503_14579.failhard);
           nosynth = (uu___503_14579.nosynth);
           uvar_subtyping = (uu___503_14579.uvar_subtyping);
           tc_term = (uu___503_14579.tc_term);
           type_of = (uu___503_14579.type_of);
           universe_of = (uu___503_14579.universe_of);
           check_type_of = (uu___503_14579.check_type_of);
           use_bv_sorts = (uu___503_14579.use_bv_sorts);
           qtbl_name_and_index = (uu___503_14579.qtbl_name_and_index);
           normalized_eff_names = (uu___503_14579.normalized_eff_names);
           fv_delta_depths = (uu___503_14579.fv_delta_depths);
           proof_ns = (uu___503_14579.proof_ns);
           synth_hook = (uu___503_14579.synth_hook);
           splice = (uu___503_14579.splice);
           postprocess = (uu___503_14579.postprocess);
           is_native_tactic = (uu___503_14579.is_native_tactic);
           identifier_info = (uu___503_14579.identifier_info);
           tc_hooks = (uu___503_14579.tc_hooks);
           dsenv = (uu___503_14579.dsenv);
           nbe = (uu___503_14579.nbe);
           strict_args_tab = (uu___503_14579.strict_args_tab);
           erasable_types_tab = (uu___503_14579.erasable_types_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14599 =
        let uu____14600 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14600 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14599
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14655 =
          let uu____14656 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14656 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14655
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14711 =
          let uu____14712 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14712 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14711
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14767 =
        let uu____14768 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14768 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14767
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___520_14832 = env  in
      {
        solver = (uu___520_14832.solver);
        range = (uu___520_14832.range);
        curmodule = lid;
        gamma = (uu___520_14832.gamma);
        gamma_sig = (uu___520_14832.gamma_sig);
        gamma_cache = (uu___520_14832.gamma_cache);
        modules = (uu___520_14832.modules);
        expected_typ = (uu___520_14832.expected_typ);
        sigtab = (uu___520_14832.sigtab);
        attrtab = (uu___520_14832.attrtab);
        instantiate_imp = (uu___520_14832.instantiate_imp);
        effects = (uu___520_14832.effects);
        generalize = (uu___520_14832.generalize);
        letrecs = (uu___520_14832.letrecs);
        top_level = (uu___520_14832.top_level);
        check_uvars = (uu___520_14832.check_uvars);
        use_eq = (uu___520_14832.use_eq);
        is_iface = (uu___520_14832.is_iface);
        admit = (uu___520_14832.admit);
        lax = (uu___520_14832.lax);
        lax_universes = (uu___520_14832.lax_universes);
        phase1 = (uu___520_14832.phase1);
        failhard = (uu___520_14832.failhard);
        nosynth = (uu___520_14832.nosynth);
        uvar_subtyping = (uu___520_14832.uvar_subtyping);
        tc_term = (uu___520_14832.tc_term);
        type_of = (uu___520_14832.type_of);
        universe_of = (uu___520_14832.universe_of);
        check_type_of = (uu___520_14832.check_type_of);
        use_bv_sorts = (uu___520_14832.use_bv_sorts);
        qtbl_name_and_index = (uu___520_14832.qtbl_name_and_index);
        normalized_eff_names = (uu___520_14832.normalized_eff_names);
        fv_delta_depths = (uu___520_14832.fv_delta_depths);
        proof_ns = (uu___520_14832.proof_ns);
        synth_hook = (uu___520_14832.synth_hook);
        splice = (uu___520_14832.splice);
        postprocess = (uu___520_14832.postprocess);
        is_native_tactic = (uu___520_14832.is_native_tactic);
        identifier_info = (uu___520_14832.identifier_info);
        tc_hooks = (uu___520_14832.tc_hooks);
        dsenv = (uu___520_14832.dsenv);
        nbe = (uu___520_14832.nbe);
        strict_args_tab = (uu___520_14832.strict_args_tab);
        erasable_types_tab = (uu___520_14832.erasable_types_tab)
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
      let uu____14863 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14863
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14876 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14876)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14891 =
      let uu____14893 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14893  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14891)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14902  ->
    let uu____14903 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14903
  
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
      | ((formals,t),uu____15003) ->
          let vs = mk_univ_subst formals us  in
          let uu____15027 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15027)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15044  ->
    match uu___1_15044 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15070  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15090 = inst_tscheme t  in
      match uu____15090 with
      | (us,t1) ->
          let uu____15101 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15101)
  
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
          let uu____15126 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15128 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15126 uu____15128
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
        fun uu____15155  ->
          match uu____15155 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15169 =
                    let uu____15171 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15175 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15179 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15181 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15171 uu____15175 uu____15179 uu____15181
                     in
                  failwith uu____15169)
               else ();
               (let uu____15186 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15186))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15204 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15215 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15226 -> false
  
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
             | ([],uu____15274) -> Maybe
             | (uu____15281,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15301 -> No  in
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
          let uu____15395 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15395 with
          | FStar_Pervasives_Native.None  ->
              let uu____15418 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15462  ->
                     match uu___2_15462 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15501 = FStar_Ident.lid_equals lid l  in
                         if uu____15501
                         then
                           let uu____15524 =
                             let uu____15543 =
                               let uu____15558 = inst_tscheme t  in
                               FStar_Util.Inl uu____15558  in
                             let uu____15573 = FStar_Ident.range_of_lid l  in
                             (uu____15543, uu____15573)  in
                           FStar_Pervasives_Native.Some uu____15524
                         else FStar_Pervasives_Native.None
                     | uu____15626 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15418
                (fun uu____15664  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15673  ->
                        match uu___3_15673 with
                        | (uu____15676,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15678);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15679;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15680;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15681;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15682;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15702 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15702
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
                                  uu____15754 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15761 -> cache t  in
                            let uu____15762 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15762 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15768 =
                                   let uu____15769 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15769)
                                    in
                                 maybe_cache uu____15768)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15840 = find_in_sigtab env lid  in
         match uu____15840 with
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
      let uu____15921 = lookup_qname env lid  in
      match uu____15921 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15942,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16056 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16056 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16101 =
          let uu____16104 = lookup_attr env1 attr  in se1 :: uu____16104  in
        FStar_Util.smap_add (attrtab env1) attr uu____16101  in
      FStar_List.iter
        (fun attr  ->
           let uu____16114 =
             let uu____16115 = FStar_Syntax_Subst.compress attr  in
             uu____16115.FStar_Syntax_Syntax.n  in
           match uu____16114 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16119 =
                 let uu____16121 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16121.FStar_Ident.str  in
               add_one1 env se uu____16119
           | uu____16122 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16145) ->
          add_sigelts env ses
      | uu____16154 ->
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
        (fun uu___4_16192  ->
           match uu___4_16192 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16210 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16272,lb::[]),uu____16274) ->
            let uu____16283 =
              let uu____16292 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16301 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16292, uu____16301)  in
            FStar_Pervasives_Native.Some uu____16283
        | FStar_Syntax_Syntax.Sig_let ((uu____16314,lbs),uu____16316) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16348 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16361 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16361
                     then
                       let uu____16374 =
                         let uu____16383 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16392 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16383, uu____16392)  in
                       FStar_Pervasives_Native.Some uu____16374
                     else FStar_Pervasives_Native.None)
        | uu____16415 -> FStar_Pervasives_Native.None
  
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
                    let uu____16507 =
                      let uu____16509 =
                        let uu____16511 =
                          let uu____16513 =
                            let uu____16515 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16521 =
                              let uu____16523 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16523  in
                            Prims.op_Hat uu____16515 uu____16521  in
                          Prims.op_Hat ", expected " uu____16513  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16511
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16509
                       in
                    failwith uu____16507
                  else ());
             (let uu____16530 =
                let uu____16539 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16539, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16530))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16559,uu____16560) ->
            let uu____16565 =
              let uu____16574 =
                let uu____16579 =
                  let uu____16580 =
                    let uu____16583 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16583  in
                  (us, uu____16580)  in
                inst_ts us_opt uu____16579  in
              (uu____16574, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16565
        | uu____16602 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16691 =
          match uu____16691 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16787,uvs,t,uu____16790,uu____16791,uu____16792);
                      FStar_Syntax_Syntax.sigrng = uu____16793;
                      FStar_Syntax_Syntax.sigquals = uu____16794;
                      FStar_Syntax_Syntax.sigmeta = uu____16795;
                      FStar_Syntax_Syntax.sigattrs = uu____16796;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16819 =
                     let uu____16828 = inst_tscheme1 (uvs, t)  in
                     (uu____16828, rng)  in
                   FStar_Pervasives_Native.Some uu____16819
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16852;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16854;
                      FStar_Syntax_Syntax.sigattrs = uu____16855;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16872 =
                     let uu____16874 = in_cur_mod env l  in uu____16874 = Yes
                      in
                   if uu____16872
                   then
                     let uu____16886 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16886
                      then
                        let uu____16902 =
                          let uu____16911 = inst_tscheme1 (uvs, t)  in
                          (uu____16911, rng)  in
                        FStar_Pervasives_Native.Some uu____16902
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16944 =
                        let uu____16953 = inst_tscheme1 (uvs, t)  in
                        (uu____16953, rng)  in
                      FStar_Pervasives_Native.Some uu____16944)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16978,uu____16979);
                      FStar_Syntax_Syntax.sigrng = uu____16980;
                      FStar_Syntax_Syntax.sigquals = uu____16981;
                      FStar_Syntax_Syntax.sigmeta = uu____16982;
                      FStar_Syntax_Syntax.sigattrs = uu____16983;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17024 =
                          let uu____17033 = inst_tscheme1 (uvs, k)  in
                          (uu____17033, rng)  in
                        FStar_Pervasives_Native.Some uu____17024
                    | uu____17054 ->
                        let uu____17055 =
                          let uu____17064 =
                            let uu____17069 =
                              let uu____17070 =
                                let uu____17073 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17073
                                 in
                              (uvs, uu____17070)  in
                            inst_tscheme1 uu____17069  in
                          (uu____17064, rng)  in
                        FStar_Pervasives_Native.Some uu____17055)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17096,uu____17097);
                      FStar_Syntax_Syntax.sigrng = uu____17098;
                      FStar_Syntax_Syntax.sigquals = uu____17099;
                      FStar_Syntax_Syntax.sigmeta = uu____17100;
                      FStar_Syntax_Syntax.sigattrs = uu____17101;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17143 =
                          let uu____17152 = inst_tscheme_with (uvs, k) us  in
                          (uu____17152, rng)  in
                        FStar_Pervasives_Native.Some uu____17143
                    | uu____17173 ->
                        let uu____17174 =
                          let uu____17183 =
                            let uu____17188 =
                              let uu____17189 =
                                let uu____17192 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17192
                                 in
                              (uvs, uu____17189)  in
                            inst_tscheme_with uu____17188 us  in
                          (uu____17183, rng)  in
                        FStar_Pervasives_Native.Some uu____17174)
               | FStar_Util.Inr se ->
                   let uu____17228 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17249;
                          FStar_Syntax_Syntax.sigrng = uu____17250;
                          FStar_Syntax_Syntax.sigquals = uu____17251;
                          FStar_Syntax_Syntax.sigmeta = uu____17252;
                          FStar_Syntax_Syntax.sigattrs = uu____17253;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17268 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17228
                     (FStar_Util.map_option
                        (fun uu____17316  ->
                           match uu____17316 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17347 =
          let uu____17358 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17358 mapper  in
        match uu____17347 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17432 =
              let uu____17443 =
                let uu____17450 =
                  let uu___851_17453 = t  in
                  let uu____17454 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___851_17453.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17454;
                    FStar_Syntax_Syntax.vars =
                      (uu___851_17453.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17450)  in
              (uu____17443, r)  in
            FStar_Pervasives_Native.Some uu____17432
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17503 = lookup_qname env l  in
      match uu____17503 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17524 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17578 = try_lookup_bv env bv  in
      match uu____17578 with
      | FStar_Pervasives_Native.None  ->
          let uu____17593 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17593 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17609 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17610 =
            let uu____17611 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17611  in
          (uu____17609, uu____17610)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17633 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17633 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17699 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17699  in
          let uu____17700 =
            let uu____17709 =
              let uu____17714 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17714)  in
            (uu____17709, r1)  in
          FStar_Pervasives_Native.Some uu____17700
  
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
        let uu____17749 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17749 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17782,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17807 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17807  in
            let uu____17808 =
              let uu____17813 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17813, r1)  in
            FStar_Pervasives_Native.Some uu____17808
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17837 = try_lookup_lid env l  in
      match uu____17837 with
      | FStar_Pervasives_Native.None  ->
          let uu____17864 = name_not_found l  in
          let uu____17870 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17864 uu____17870
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17913  ->
              match uu___5_17913 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17917 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17938 = lookup_qname env lid  in
      match uu____17938 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17947,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17950;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17952;
              FStar_Syntax_Syntax.sigattrs = uu____17953;_},FStar_Pervasives_Native.None
            ),uu____17954)
          ->
          let uu____18003 =
            let uu____18010 =
              let uu____18011 =
                let uu____18014 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18014 t  in
              (uvs, uu____18011)  in
            (uu____18010, q)  in
          FStar_Pervasives_Native.Some uu____18003
      | uu____18027 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18049 = lookup_qname env lid  in
      match uu____18049 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18054,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18057;
              FStar_Syntax_Syntax.sigquals = uu____18058;
              FStar_Syntax_Syntax.sigmeta = uu____18059;
              FStar_Syntax_Syntax.sigattrs = uu____18060;_},FStar_Pervasives_Native.None
            ),uu____18061)
          ->
          let uu____18110 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18110 (uvs, t)
      | uu____18115 ->
          let uu____18116 = name_not_found lid  in
          let uu____18122 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18116 uu____18122
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18142 = lookup_qname env lid  in
      match uu____18142 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18147,uvs,t,uu____18150,uu____18151,uu____18152);
              FStar_Syntax_Syntax.sigrng = uu____18153;
              FStar_Syntax_Syntax.sigquals = uu____18154;
              FStar_Syntax_Syntax.sigmeta = uu____18155;
              FStar_Syntax_Syntax.sigattrs = uu____18156;_},FStar_Pervasives_Native.None
            ),uu____18157)
          ->
          let uu____18212 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18212 (uvs, t)
      | uu____18217 ->
          let uu____18218 = name_not_found lid  in
          let uu____18224 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18218 uu____18224
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18247 = lookup_qname env lid  in
      match uu____18247 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18255,uu____18256,uu____18257,uu____18258,uu____18259,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18261;
              FStar_Syntax_Syntax.sigquals = uu____18262;
              FStar_Syntax_Syntax.sigmeta = uu____18263;
              FStar_Syntax_Syntax.sigattrs = uu____18264;_},uu____18265),uu____18266)
          -> (true, dcs)
      | uu____18329 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18345 = lookup_qname env lid  in
      match uu____18345 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18346,uu____18347,uu____18348,l,uu____18350,uu____18351);
              FStar_Syntax_Syntax.sigrng = uu____18352;
              FStar_Syntax_Syntax.sigquals = uu____18353;
              FStar_Syntax_Syntax.sigmeta = uu____18354;
              FStar_Syntax_Syntax.sigattrs = uu____18355;_},uu____18356),uu____18357)
          -> l
      | uu____18414 ->
          let uu____18415 =
            let uu____18417 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18417  in
          failwith uu____18415
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18487)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18544) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18568 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18568
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18603 -> FStar_Pervasives_Native.None)
          | uu____18612 -> FStar_Pervasives_Native.None
  
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
        let uu____18674 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18674
  
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
        let uu____18707 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18707
  
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
             (FStar_Util.Inl uu____18759,uu____18760) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18809),uu____18810) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18859 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18877 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18887 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18904 ->
                  let uu____18911 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18911
              | FStar_Syntax_Syntax.Sig_let ((uu____18912,lbs),uu____18914)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18930 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18930
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18937 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18945 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18946 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18953 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18954 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18955 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18956 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18969 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18987 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18987
           (fun d_opt  ->
              let uu____19000 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19000
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19010 =
                   let uu____19013 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19013  in
                 match uu____19010 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19014 =
                       let uu____19016 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19016
                        in
                     failwith uu____19014
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19021 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19021
                       then
                         let uu____19024 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19026 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19028 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19024 uu____19026 uu____19028
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
        (FStar_Util.Inr (se,uu____19053),uu____19054) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19103 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19125),uu____19126) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19175 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19197 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19197
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19230 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19230 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19252 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19261 =
                        let uu____19262 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19262.FStar_Syntax_Syntax.n  in
                      match uu____19261 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19267 -> false))
               in
            (true, uu____19252)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19290 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19290
  
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
          let uu____19362 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19362.FStar_Ident.str  in
        let uu____19363 = FStar_Util.smap_try_find tab s  in
        match uu____19363 with
        | FStar_Pervasives_Native.None  ->
            let uu____19366 = f ()  in
            (match uu____19366 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____19404 =
        let uu____19405 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____19405 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19439 =
        let uu____19440 = FStar_Syntax_Util.unrefine t  in
        uu____19440.FStar_Syntax_Syntax.n  in
      match uu____19439 with
      | FStar_Syntax_Syntax.Tm_type uu____19444 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____19448) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____19474) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____19479,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____19501 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____19534 =
        let attrs =
          let uu____19540 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____19540  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____19580 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____19580)
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
      let uu____19625 = lookup_qname env ftv  in
      match uu____19625 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19629) ->
          let uu____19674 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19674 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19695,t),r) ->
               let uu____19710 =
                 let uu____19711 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19711 t  in
               FStar_Pervasives_Native.Some uu____19710)
      | uu____19712 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19724 = try_lookup_effect_lid env ftv  in
      match uu____19724 with
      | FStar_Pervasives_Native.None  ->
          let uu____19727 = name_not_found ftv  in
          let uu____19733 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19727 uu____19733
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
        let uu____19757 = lookup_qname env lid0  in
        match uu____19757 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19768);
                FStar_Syntax_Syntax.sigrng = uu____19769;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19771;
                FStar_Syntax_Syntax.sigattrs = uu____19772;_},FStar_Pervasives_Native.None
              ),uu____19773)
            ->
            let lid1 =
              let uu____19827 =
                let uu____19828 = FStar_Ident.range_of_lid lid  in
                let uu____19829 =
                  let uu____19830 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19830  in
                FStar_Range.set_use_range uu____19828 uu____19829  in
              FStar_Ident.set_lid_range lid uu____19827  in
            let uu____19831 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19837  ->
                      match uu___6_19837 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19840 -> false))
               in
            if uu____19831
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19859 =
                      let uu____19861 =
                        let uu____19863 = get_range env  in
                        FStar_Range.string_of_range uu____19863  in
                      let uu____19864 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19866 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19861 uu____19864 uu____19866
                       in
                    failwith uu____19859)
                  in
               match (binders, univs1) with
               | ([],uu____19887) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19913,uu____19914::uu____19915::uu____19916) ->
                   let uu____19937 =
                     let uu____19939 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19941 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19939 uu____19941
                      in
                   failwith uu____19937
               | uu____19952 ->
                   let uu____19967 =
                     let uu____19972 =
                       let uu____19973 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19973)  in
                     inst_tscheme_with uu____19972 insts  in
                   (match uu____19967 with
                    | (uu____19986,t) ->
                        let t1 =
                          let uu____19989 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19989 t  in
                        let uu____19990 =
                          let uu____19991 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19991.FStar_Syntax_Syntax.n  in
                        (match uu____19990 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20026 -> failwith "Impossible")))
        | uu____20034 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20058 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20058 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20071,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20078 = find1 l2  in
            (match uu____20078 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20085 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20085 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20089 = find1 l  in
            (match uu____20089 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20094 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20094
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20109 = lookup_qname env l1  in
      match uu____20109 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20112;
              FStar_Syntax_Syntax.sigrng = uu____20113;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20115;
              FStar_Syntax_Syntax.sigattrs = uu____20116;_},uu____20117),uu____20118)
          -> q
      | uu____20169 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20193 =
          let uu____20194 =
            let uu____20196 = FStar_Util.string_of_int i  in
            let uu____20198 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20196 uu____20198
             in
          failwith uu____20194  in
        let uu____20201 = lookup_datacon env lid  in
        match uu____20201 with
        | (uu____20206,t) ->
            let uu____20208 =
              let uu____20209 = FStar_Syntax_Subst.compress t  in
              uu____20209.FStar_Syntax_Syntax.n  in
            (match uu____20208 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20213) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20257 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20257
                      FStar_Pervasives_Native.fst)
             | uu____20268 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20282 = lookup_qname env l  in
      match uu____20282 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20284,uu____20285,uu____20286);
              FStar_Syntax_Syntax.sigrng = uu____20287;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20289;
              FStar_Syntax_Syntax.sigattrs = uu____20290;_},uu____20291),uu____20292)
          ->
          FStar_Util.for_some
            (fun uu___7_20345  ->
               match uu___7_20345 with
               | FStar_Syntax_Syntax.Projector uu____20347 -> true
               | uu____20353 -> false) quals
      | uu____20355 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20369 = lookup_qname env lid  in
      match uu____20369 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20371,uu____20372,uu____20373,uu____20374,uu____20375,uu____20376);
              FStar_Syntax_Syntax.sigrng = uu____20377;
              FStar_Syntax_Syntax.sigquals = uu____20378;
              FStar_Syntax_Syntax.sigmeta = uu____20379;
              FStar_Syntax_Syntax.sigattrs = uu____20380;_},uu____20381),uu____20382)
          -> true
      | uu____20440 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20454 = lookup_qname env lid  in
      match uu____20454 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20456,uu____20457,uu____20458,uu____20459,uu____20460,uu____20461);
              FStar_Syntax_Syntax.sigrng = uu____20462;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20464;
              FStar_Syntax_Syntax.sigattrs = uu____20465;_},uu____20466),uu____20467)
          ->
          FStar_Util.for_some
            (fun uu___8_20528  ->
               match uu___8_20528 with
               | FStar_Syntax_Syntax.RecordType uu____20530 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20540 -> true
               | uu____20550 -> false) quals
      | uu____20552 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20562,uu____20563);
            FStar_Syntax_Syntax.sigrng = uu____20564;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20566;
            FStar_Syntax_Syntax.sigattrs = uu____20567;_},uu____20568),uu____20569)
        ->
        FStar_Util.for_some
          (fun uu___9_20626  ->
             match uu___9_20626 with
             | FStar_Syntax_Syntax.Action uu____20628 -> true
             | uu____20630 -> false) quals
    | uu____20632 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20646 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20646
  
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
      let uu____20663 =
        let uu____20664 = FStar_Syntax_Util.un_uinst head1  in
        uu____20664.FStar_Syntax_Syntax.n  in
      match uu____20663 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20670 ->
               true
           | uu____20673 -> false)
      | uu____20675 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20689 = lookup_qname env l  in
      match uu____20689 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20692),uu____20693) ->
          FStar_Util.for_some
            (fun uu___10_20741  ->
               match uu___10_20741 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20744 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20746 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20822 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20840) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20858 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20866 ->
                 FStar_Pervasives_Native.Some true
             | uu____20885 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20888 =
        let uu____20892 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20892 mapper  in
      match uu____20888 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20952 = lookup_qname env lid  in
      match uu____20952 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20956,uu____20957,tps,uu____20959,uu____20960,uu____20961);
              FStar_Syntax_Syntax.sigrng = uu____20962;
              FStar_Syntax_Syntax.sigquals = uu____20963;
              FStar_Syntax_Syntax.sigmeta = uu____20964;
              FStar_Syntax_Syntax.sigattrs = uu____20965;_},uu____20966),uu____20967)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21033 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21079  ->
              match uu____21079 with
              | (d,uu____21088) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21104 = effect_decl_opt env l  in
      match uu____21104 with
      | FStar_Pervasives_Native.None  ->
          let uu____21119 = name_not_found l  in
          let uu____21125 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21119 uu____21125
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21148  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21167  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> (FStar_Ident.lident * mlift * mlift))
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21199 = FStar_Ident.lid_equals l1 l2  in
        if uu____21199
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21210 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21210
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21221 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21274  ->
                        match uu____21274 with
                        | (m1,m2,uu____21288,uu____21289,uu____21290) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21221 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21307 =
                    let uu____21313 =
                      let uu____21315 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21317 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21315
                        uu____21317
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21313)
                     in
                  FStar_Errors.raise_error uu____21307 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21327,uu____21328,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21362 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21362
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
  'Auu____21382 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21382) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21411 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21437  ->
                match uu____21437 with
                | (d,uu____21444) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21411 with
      | FStar_Pervasives_Native.None  ->
          let uu____21455 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21455
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21470 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21470 with
           | (uu____21481,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21499)::(wp,uu____21501)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21557 -> failwith "Impossible"))
  
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
        | uu____21622 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21635 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21635 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21652 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21652 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21677 =
                     let uu____21683 =
                       let uu____21685 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____21693 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____21704 =
                         let uu____21706 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____21706  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21685 uu____21693 uu____21704
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21683)
                      in
                   FStar_Errors.raise_error uu____21677
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____21714 =
                     let uu____21725 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____21725 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____21762  ->
                        fun uu____21763  ->
                          match (uu____21762, uu____21763) with
                          | ((x,uu____21793),(t,uu____21795)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21714
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____21826 =
                     let uu___1576_21827 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1576_21827.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1576_21827.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1576_21827.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1576_21827.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____21826
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____21839 .
    'Auu____21839 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____21869 = effect_decl_opt env effect_name  in
          match uu____21869 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____21912 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____21935 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____21974 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____21974
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____21979 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____21979
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____21990 =
                     let uu____21993 = get_range env  in
                     let uu____21994 =
                       let uu____22001 =
                         let uu____22002 =
                           let uu____22019 =
                             let uu____22030 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22030; wp]  in
                           (repr, uu____22019)  in
                         FStar_Syntax_Syntax.Tm_app uu____22002  in
                       FStar_Syntax_Syntax.mk uu____22001  in
                     uu____21994 FStar_Pervasives_Native.None uu____21993  in
                   FStar_Pervasives_Native.Some uu____21990)
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let effect_lid1 = norm_eff_name env effect_lid  in
      let quals = lookup_effect_quals env effect_lid1  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
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
      | uu____22174 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22189 =
        let uu____22190 = FStar_Syntax_Subst.compress t  in
        uu____22190.FStar_Syntax_Syntax.n  in
      match uu____22189 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22194,c) ->
          is_reifiable_comp env c
      | uu____22216 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22236 =
           let uu____22238 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22238  in
         if uu____22236
         then
           let uu____22241 =
             let uu____22247 =
               let uu____22249 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22249
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22247)  in
           let uu____22253 = get_range env  in
           FStar_Errors.raise_error uu____22241 uu____22253
         else ());
        (let uu____22256 = effect_repr_aux true env c u_c  in
         match uu____22256 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1641_22292 = env  in
        {
          solver = (uu___1641_22292.solver);
          range = (uu___1641_22292.range);
          curmodule = (uu___1641_22292.curmodule);
          gamma = (uu___1641_22292.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1641_22292.gamma_cache);
          modules = (uu___1641_22292.modules);
          expected_typ = (uu___1641_22292.expected_typ);
          sigtab = (uu___1641_22292.sigtab);
          attrtab = (uu___1641_22292.attrtab);
          instantiate_imp = (uu___1641_22292.instantiate_imp);
          effects = (uu___1641_22292.effects);
          generalize = (uu___1641_22292.generalize);
          letrecs = (uu___1641_22292.letrecs);
          top_level = (uu___1641_22292.top_level);
          check_uvars = (uu___1641_22292.check_uvars);
          use_eq = (uu___1641_22292.use_eq);
          is_iface = (uu___1641_22292.is_iface);
          admit = (uu___1641_22292.admit);
          lax = (uu___1641_22292.lax);
          lax_universes = (uu___1641_22292.lax_universes);
          phase1 = (uu___1641_22292.phase1);
          failhard = (uu___1641_22292.failhard);
          nosynth = (uu___1641_22292.nosynth);
          uvar_subtyping = (uu___1641_22292.uvar_subtyping);
          tc_term = (uu___1641_22292.tc_term);
          type_of = (uu___1641_22292.type_of);
          universe_of = (uu___1641_22292.universe_of);
          check_type_of = (uu___1641_22292.check_type_of);
          use_bv_sorts = (uu___1641_22292.use_bv_sorts);
          qtbl_name_and_index = (uu___1641_22292.qtbl_name_and_index);
          normalized_eff_names = (uu___1641_22292.normalized_eff_names);
          fv_delta_depths = (uu___1641_22292.fv_delta_depths);
          proof_ns = (uu___1641_22292.proof_ns);
          synth_hook = (uu___1641_22292.synth_hook);
          splice = (uu___1641_22292.splice);
          postprocess = (uu___1641_22292.postprocess);
          is_native_tactic = (uu___1641_22292.is_native_tactic);
          identifier_info = (uu___1641_22292.identifier_info);
          tc_hooks = (uu___1641_22292.tc_hooks);
          dsenv = (uu___1641_22292.dsenv);
          nbe = (uu___1641_22292.nbe);
          strict_args_tab = (uu___1641_22292.strict_args_tab);
          erasable_types_tab = (uu___1641_22292.erasable_types_tab)
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
    fun uu____22311  ->
      match uu____22311 with
      | (ed,quals) ->
          let effects =
            let uu___1650_22325 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1650_22325.order);
              joins = (uu___1650_22325.joins)
            }  in
          let uu___1653_22334 = env  in
          {
            solver = (uu___1653_22334.solver);
            range = (uu___1653_22334.range);
            curmodule = (uu___1653_22334.curmodule);
            gamma = (uu___1653_22334.gamma);
            gamma_sig = (uu___1653_22334.gamma_sig);
            gamma_cache = (uu___1653_22334.gamma_cache);
            modules = (uu___1653_22334.modules);
            expected_typ = (uu___1653_22334.expected_typ);
            sigtab = (uu___1653_22334.sigtab);
            attrtab = (uu___1653_22334.attrtab);
            instantiate_imp = (uu___1653_22334.instantiate_imp);
            effects;
            generalize = (uu___1653_22334.generalize);
            letrecs = (uu___1653_22334.letrecs);
            top_level = (uu___1653_22334.top_level);
            check_uvars = (uu___1653_22334.check_uvars);
            use_eq = (uu___1653_22334.use_eq);
            is_iface = (uu___1653_22334.is_iface);
            admit = (uu___1653_22334.admit);
            lax = (uu___1653_22334.lax);
            lax_universes = (uu___1653_22334.lax_universes);
            phase1 = (uu___1653_22334.phase1);
            failhard = (uu___1653_22334.failhard);
            nosynth = (uu___1653_22334.nosynth);
            uvar_subtyping = (uu___1653_22334.uvar_subtyping);
            tc_term = (uu___1653_22334.tc_term);
            type_of = (uu___1653_22334.type_of);
            universe_of = (uu___1653_22334.universe_of);
            check_type_of = (uu___1653_22334.check_type_of);
            use_bv_sorts = (uu___1653_22334.use_bv_sorts);
            qtbl_name_and_index = (uu___1653_22334.qtbl_name_and_index);
            normalized_eff_names = (uu___1653_22334.normalized_eff_names);
            fv_delta_depths = (uu___1653_22334.fv_delta_depths);
            proof_ns = (uu___1653_22334.proof_ns);
            synth_hook = (uu___1653_22334.synth_hook);
            splice = (uu___1653_22334.splice);
            postprocess = (uu___1653_22334.postprocess);
            is_native_tactic = (uu___1653_22334.is_native_tactic);
            identifier_info = (uu___1653_22334.identifier_info);
            tc_hooks = (uu___1653_22334.tc_hooks);
            dsenv = (uu___1653_22334.dsenv);
            nbe = (uu___1653_22334.nbe);
            strict_args_tab = (uu___1653_22334.strict_args_tab);
            erasable_types_tab = (uu___1653_22334.erasable_types_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____22374 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____22374  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____22532 = (e1.mlift).mlift_wp u t wp  in
                            let uu____22533 = l1 u t wp e  in
                            l2 u t uu____22532 uu____22533))
            | uu____22534 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____22606 = inst_tscheme_with lift_t [u]  in
        match uu____22606 with
        | (uu____22613,lift_t1) ->
            let uu____22615 =
              let uu____22622 =
                let uu____22623 =
                  let uu____22640 =
                    let uu____22651 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22660 =
                      let uu____22671 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____22671]  in
                    uu____22651 :: uu____22660  in
                  (lift_t1, uu____22640)  in
                FStar_Syntax_Syntax.Tm_app uu____22623  in
              FStar_Syntax_Syntax.mk uu____22622  in
            uu____22615 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____22781 = inst_tscheme_with lift_t [u]  in
        match uu____22781 with
        | (uu____22788,lift_t1) ->
            let uu____22790 =
              let uu____22797 =
                let uu____22798 =
                  let uu____22815 =
                    let uu____22826 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22835 =
                      let uu____22846 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____22855 =
                        let uu____22866 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____22866]  in
                      uu____22846 :: uu____22855  in
                    uu____22826 :: uu____22835  in
                  (lift_t1, uu____22815)  in
                FStar_Syntax_Syntax.Tm_app uu____22798  in
              FStar_Syntax_Syntax.mk uu____22797  in
            uu____22790 FStar_Pervasives_Native.None
              e.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_term =
        FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term  in
      let edge =
        {
          msource = (sub1.FStar_Syntax_Syntax.source);
          mtarget = (sub1.FStar_Syntax_Syntax.target);
          mlift = { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
        }  in
      let id_edge l =
        {
          msource = (sub1.FStar_Syntax_Syntax.source);
          mtarget = (sub1.FStar_Syntax_Syntax.target);
          mlift = identity_mlift
        }  in
      let print_mlift l =
        let bogus_term s =
          let uu____22968 =
            let uu____22969 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____22969
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____22968  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____22978 =
          let uu____22980 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____22980  in
        let uu____22981 =
          let uu____22983 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____23011 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____23011)
             in
          FStar_Util.dflt "none" uu____22983  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22978 uu____22981
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____23040  ->
                match uu____23040 with
                | (e,uu____23048) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____23071 =
        match uu____23071 with
        | (i,j) ->
            let uu____23082 = FStar_Ident.lid_equals i j  in
            if uu____23082
            then
              FStar_All.pipe_right (id_edge i)
                (fun _23089  -> FStar_Pervasives_Native.Some _23089)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____23118 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____23128 = FStar_Ident.lid_equals i k  in
                    if uu____23128
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____23142 = FStar_Ident.lid_equals j k
                                 in
                              if uu____23142
                              then []
                              else
                                (let uu____23149 =
                                   let uu____23158 = find_edge order1 (i, k)
                                      in
                                   let uu____23161 = find_edge order1 (k, j)
                                      in
                                   (uu____23158, uu____23161)  in
                                 match uu____23149 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____23176 = compose_edges e1 e2
                                        in
                                     [uu____23176]
                                 | uu____23177 -> [])))))
             in
          FStar_List.append order1 uu____23118  in
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
              let uu____23207 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____23210 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____23210
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____23207
              then
                let uu____23217 =
                  let uu____23223 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____23223)
                   in
                let uu____23227 = get_range env  in
                FStar_Errors.raise_error uu____23217 uu____23227
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____23305 = FStar_Ident.lid_equals i j  in
                           if uu____23305
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____23357 =
                                         let uu____23366 =
                                           find_edge order2 (i, k)  in
                                         let uu____23369 =
                                           find_edge order2 (j, k)  in
                                         (uu____23366, uu____23369)  in
                                       match uu____23357 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____23411,uu____23412)
                                                ->
                                                let uu____23419 =
                                                  let uu____23426 =
                                                    let uu____23428 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23428
                                                     in
                                                  let uu____23431 =
                                                    let uu____23433 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23433
                                                     in
                                                  (uu____23426, uu____23431)
                                                   in
                                                (match uu____23419 with
                                                 | (true ,true ) ->
                                                     let uu____23450 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____23450
                                                     then
                                                       (FStar_Errors.log_issue
                                                          FStar_Range.dummyRange
                                                          (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                            "Looking multiple times at the same upper bound candidate");
                                                        bopt)
                                                     else
                                                       failwith
                                                         "Found a cycle in the lattice"
                                                 | (false ,false ) -> bopt
                                                 | (true ,false ) ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | (false ,true ) -> bopt))
                                       | uu____23493 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1780_23566 = env.effects  in
         { decls = (uu___1780_23566.decls); order = order2; joins }  in
       let uu___1783_23567 = env  in
       {
         solver = (uu___1783_23567.solver);
         range = (uu___1783_23567.range);
         curmodule = (uu___1783_23567.curmodule);
         gamma = (uu___1783_23567.gamma);
         gamma_sig = (uu___1783_23567.gamma_sig);
         gamma_cache = (uu___1783_23567.gamma_cache);
         modules = (uu___1783_23567.modules);
         expected_typ = (uu___1783_23567.expected_typ);
         sigtab = (uu___1783_23567.sigtab);
         attrtab = (uu___1783_23567.attrtab);
         instantiate_imp = (uu___1783_23567.instantiate_imp);
         effects;
         generalize = (uu___1783_23567.generalize);
         letrecs = (uu___1783_23567.letrecs);
         top_level = (uu___1783_23567.top_level);
         check_uvars = (uu___1783_23567.check_uvars);
         use_eq = (uu___1783_23567.use_eq);
         is_iface = (uu___1783_23567.is_iface);
         admit = (uu___1783_23567.admit);
         lax = (uu___1783_23567.lax);
         lax_universes = (uu___1783_23567.lax_universes);
         phase1 = (uu___1783_23567.phase1);
         failhard = (uu___1783_23567.failhard);
         nosynth = (uu___1783_23567.nosynth);
         uvar_subtyping = (uu___1783_23567.uvar_subtyping);
         tc_term = (uu___1783_23567.tc_term);
         type_of = (uu___1783_23567.type_of);
         universe_of = (uu___1783_23567.universe_of);
         check_type_of = (uu___1783_23567.check_type_of);
         use_bv_sorts = (uu___1783_23567.use_bv_sorts);
         qtbl_name_and_index = (uu___1783_23567.qtbl_name_and_index);
         normalized_eff_names = (uu___1783_23567.normalized_eff_names);
         fv_delta_depths = (uu___1783_23567.fv_delta_depths);
         proof_ns = (uu___1783_23567.proof_ns);
         synth_hook = (uu___1783_23567.synth_hook);
         splice = (uu___1783_23567.splice);
         postprocess = (uu___1783_23567.postprocess);
         is_native_tactic = (uu___1783_23567.is_native_tactic);
         identifier_info = (uu___1783_23567.identifier_info);
         tc_hooks = (uu___1783_23567.tc_hooks);
         dsenv = (uu___1783_23567.dsenv);
         nbe = (uu___1783_23567.nbe);
         strict_args_tab = (uu___1783_23567.strict_args_tab);
         erasable_types_tab = (uu___1783_23567.erasable_types_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1787_23579 = env  in
      {
        solver = (uu___1787_23579.solver);
        range = (uu___1787_23579.range);
        curmodule = (uu___1787_23579.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1787_23579.gamma_sig);
        gamma_cache = (uu___1787_23579.gamma_cache);
        modules = (uu___1787_23579.modules);
        expected_typ = (uu___1787_23579.expected_typ);
        sigtab = (uu___1787_23579.sigtab);
        attrtab = (uu___1787_23579.attrtab);
        instantiate_imp = (uu___1787_23579.instantiate_imp);
        effects = (uu___1787_23579.effects);
        generalize = (uu___1787_23579.generalize);
        letrecs = (uu___1787_23579.letrecs);
        top_level = (uu___1787_23579.top_level);
        check_uvars = (uu___1787_23579.check_uvars);
        use_eq = (uu___1787_23579.use_eq);
        is_iface = (uu___1787_23579.is_iface);
        admit = (uu___1787_23579.admit);
        lax = (uu___1787_23579.lax);
        lax_universes = (uu___1787_23579.lax_universes);
        phase1 = (uu___1787_23579.phase1);
        failhard = (uu___1787_23579.failhard);
        nosynth = (uu___1787_23579.nosynth);
        uvar_subtyping = (uu___1787_23579.uvar_subtyping);
        tc_term = (uu___1787_23579.tc_term);
        type_of = (uu___1787_23579.type_of);
        universe_of = (uu___1787_23579.universe_of);
        check_type_of = (uu___1787_23579.check_type_of);
        use_bv_sorts = (uu___1787_23579.use_bv_sorts);
        qtbl_name_and_index = (uu___1787_23579.qtbl_name_and_index);
        normalized_eff_names = (uu___1787_23579.normalized_eff_names);
        fv_delta_depths = (uu___1787_23579.fv_delta_depths);
        proof_ns = (uu___1787_23579.proof_ns);
        synth_hook = (uu___1787_23579.synth_hook);
        splice = (uu___1787_23579.splice);
        postprocess = (uu___1787_23579.postprocess);
        is_native_tactic = (uu___1787_23579.is_native_tactic);
        identifier_info = (uu___1787_23579.identifier_info);
        tc_hooks = (uu___1787_23579.tc_hooks);
        dsenv = (uu___1787_23579.dsenv);
        nbe = (uu___1787_23579.nbe);
        strict_args_tab = (uu___1787_23579.strict_args_tab);
        erasable_types_tab = (uu___1787_23579.erasable_types_tab)
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
            (let uu___1800_23637 = env  in
             {
               solver = (uu___1800_23637.solver);
               range = (uu___1800_23637.range);
               curmodule = (uu___1800_23637.curmodule);
               gamma = rest;
               gamma_sig = (uu___1800_23637.gamma_sig);
               gamma_cache = (uu___1800_23637.gamma_cache);
               modules = (uu___1800_23637.modules);
               expected_typ = (uu___1800_23637.expected_typ);
               sigtab = (uu___1800_23637.sigtab);
               attrtab = (uu___1800_23637.attrtab);
               instantiate_imp = (uu___1800_23637.instantiate_imp);
               effects = (uu___1800_23637.effects);
               generalize = (uu___1800_23637.generalize);
               letrecs = (uu___1800_23637.letrecs);
               top_level = (uu___1800_23637.top_level);
               check_uvars = (uu___1800_23637.check_uvars);
               use_eq = (uu___1800_23637.use_eq);
               is_iface = (uu___1800_23637.is_iface);
               admit = (uu___1800_23637.admit);
               lax = (uu___1800_23637.lax);
               lax_universes = (uu___1800_23637.lax_universes);
               phase1 = (uu___1800_23637.phase1);
               failhard = (uu___1800_23637.failhard);
               nosynth = (uu___1800_23637.nosynth);
               uvar_subtyping = (uu___1800_23637.uvar_subtyping);
               tc_term = (uu___1800_23637.tc_term);
               type_of = (uu___1800_23637.type_of);
               universe_of = (uu___1800_23637.universe_of);
               check_type_of = (uu___1800_23637.check_type_of);
               use_bv_sorts = (uu___1800_23637.use_bv_sorts);
               qtbl_name_and_index = (uu___1800_23637.qtbl_name_and_index);
               normalized_eff_names = (uu___1800_23637.normalized_eff_names);
               fv_delta_depths = (uu___1800_23637.fv_delta_depths);
               proof_ns = (uu___1800_23637.proof_ns);
               synth_hook = (uu___1800_23637.synth_hook);
               splice = (uu___1800_23637.splice);
               postprocess = (uu___1800_23637.postprocess);
               is_native_tactic = (uu___1800_23637.is_native_tactic);
               identifier_info = (uu___1800_23637.identifier_info);
               tc_hooks = (uu___1800_23637.tc_hooks);
               dsenv = (uu___1800_23637.dsenv);
               nbe = (uu___1800_23637.nbe);
               strict_args_tab = (uu___1800_23637.strict_args_tab);
               erasable_types_tab = (uu___1800_23637.erasable_types_tab)
             }))
    | uu____23638 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23667  ->
             match uu____23667 with | (x,uu____23675) -> push_bv env1 x) env
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
            let uu___1814_23710 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1814_23710.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1814_23710.FStar_Syntax_Syntax.index);
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
        let uu____23783 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23783 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23811 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23811)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1835_23827 = env  in
      {
        solver = (uu___1835_23827.solver);
        range = (uu___1835_23827.range);
        curmodule = (uu___1835_23827.curmodule);
        gamma = (uu___1835_23827.gamma);
        gamma_sig = (uu___1835_23827.gamma_sig);
        gamma_cache = (uu___1835_23827.gamma_cache);
        modules = (uu___1835_23827.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1835_23827.sigtab);
        attrtab = (uu___1835_23827.attrtab);
        instantiate_imp = (uu___1835_23827.instantiate_imp);
        effects = (uu___1835_23827.effects);
        generalize = (uu___1835_23827.generalize);
        letrecs = (uu___1835_23827.letrecs);
        top_level = (uu___1835_23827.top_level);
        check_uvars = (uu___1835_23827.check_uvars);
        use_eq = false;
        is_iface = (uu___1835_23827.is_iface);
        admit = (uu___1835_23827.admit);
        lax = (uu___1835_23827.lax);
        lax_universes = (uu___1835_23827.lax_universes);
        phase1 = (uu___1835_23827.phase1);
        failhard = (uu___1835_23827.failhard);
        nosynth = (uu___1835_23827.nosynth);
        uvar_subtyping = (uu___1835_23827.uvar_subtyping);
        tc_term = (uu___1835_23827.tc_term);
        type_of = (uu___1835_23827.type_of);
        universe_of = (uu___1835_23827.universe_of);
        check_type_of = (uu___1835_23827.check_type_of);
        use_bv_sorts = (uu___1835_23827.use_bv_sorts);
        qtbl_name_and_index = (uu___1835_23827.qtbl_name_and_index);
        normalized_eff_names = (uu___1835_23827.normalized_eff_names);
        fv_delta_depths = (uu___1835_23827.fv_delta_depths);
        proof_ns = (uu___1835_23827.proof_ns);
        synth_hook = (uu___1835_23827.synth_hook);
        splice = (uu___1835_23827.splice);
        postprocess = (uu___1835_23827.postprocess);
        is_native_tactic = (uu___1835_23827.is_native_tactic);
        identifier_info = (uu___1835_23827.identifier_info);
        tc_hooks = (uu___1835_23827.tc_hooks);
        dsenv = (uu___1835_23827.dsenv);
        nbe = (uu___1835_23827.nbe);
        strict_args_tab = (uu___1835_23827.strict_args_tab);
        erasable_types_tab = (uu___1835_23827.erasable_types_tab)
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
    let uu____23858 = expected_typ env_  in
    ((let uu___1842_23864 = env_  in
      {
        solver = (uu___1842_23864.solver);
        range = (uu___1842_23864.range);
        curmodule = (uu___1842_23864.curmodule);
        gamma = (uu___1842_23864.gamma);
        gamma_sig = (uu___1842_23864.gamma_sig);
        gamma_cache = (uu___1842_23864.gamma_cache);
        modules = (uu___1842_23864.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1842_23864.sigtab);
        attrtab = (uu___1842_23864.attrtab);
        instantiate_imp = (uu___1842_23864.instantiate_imp);
        effects = (uu___1842_23864.effects);
        generalize = (uu___1842_23864.generalize);
        letrecs = (uu___1842_23864.letrecs);
        top_level = (uu___1842_23864.top_level);
        check_uvars = (uu___1842_23864.check_uvars);
        use_eq = false;
        is_iface = (uu___1842_23864.is_iface);
        admit = (uu___1842_23864.admit);
        lax = (uu___1842_23864.lax);
        lax_universes = (uu___1842_23864.lax_universes);
        phase1 = (uu___1842_23864.phase1);
        failhard = (uu___1842_23864.failhard);
        nosynth = (uu___1842_23864.nosynth);
        uvar_subtyping = (uu___1842_23864.uvar_subtyping);
        tc_term = (uu___1842_23864.tc_term);
        type_of = (uu___1842_23864.type_of);
        universe_of = (uu___1842_23864.universe_of);
        check_type_of = (uu___1842_23864.check_type_of);
        use_bv_sorts = (uu___1842_23864.use_bv_sorts);
        qtbl_name_and_index = (uu___1842_23864.qtbl_name_and_index);
        normalized_eff_names = (uu___1842_23864.normalized_eff_names);
        fv_delta_depths = (uu___1842_23864.fv_delta_depths);
        proof_ns = (uu___1842_23864.proof_ns);
        synth_hook = (uu___1842_23864.synth_hook);
        splice = (uu___1842_23864.splice);
        postprocess = (uu___1842_23864.postprocess);
        is_native_tactic = (uu___1842_23864.is_native_tactic);
        identifier_info = (uu___1842_23864.identifier_info);
        tc_hooks = (uu___1842_23864.tc_hooks);
        dsenv = (uu___1842_23864.dsenv);
        nbe = (uu___1842_23864.nbe);
        strict_args_tab = (uu___1842_23864.strict_args_tab);
        erasable_types_tab = (uu___1842_23864.erasable_types_tab)
      }), uu____23858)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23876 =
      let uu____23879 = FStar_Ident.id_of_text ""  in [uu____23879]  in
    FStar_Ident.lid_of_ids uu____23876  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23886 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23886
        then
          let uu____23891 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23891 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1850_23919 = env  in
       {
         solver = (uu___1850_23919.solver);
         range = (uu___1850_23919.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1850_23919.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1850_23919.expected_typ);
         sigtab = (uu___1850_23919.sigtab);
         attrtab = (uu___1850_23919.attrtab);
         instantiate_imp = (uu___1850_23919.instantiate_imp);
         effects = (uu___1850_23919.effects);
         generalize = (uu___1850_23919.generalize);
         letrecs = (uu___1850_23919.letrecs);
         top_level = (uu___1850_23919.top_level);
         check_uvars = (uu___1850_23919.check_uvars);
         use_eq = (uu___1850_23919.use_eq);
         is_iface = (uu___1850_23919.is_iface);
         admit = (uu___1850_23919.admit);
         lax = (uu___1850_23919.lax);
         lax_universes = (uu___1850_23919.lax_universes);
         phase1 = (uu___1850_23919.phase1);
         failhard = (uu___1850_23919.failhard);
         nosynth = (uu___1850_23919.nosynth);
         uvar_subtyping = (uu___1850_23919.uvar_subtyping);
         tc_term = (uu___1850_23919.tc_term);
         type_of = (uu___1850_23919.type_of);
         universe_of = (uu___1850_23919.universe_of);
         check_type_of = (uu___1850_23919.check_type_of);
         use_bv_sorts = (uu___1850_23919.use_bv_sorts);
         qtbl_name_and_index = (uu___1850_23919.qtbl_name_and_index);
         normalized_eff_names = (uu___1850_23919.normalized_eff_names);
         fv_delta_depths = (uu___1850_23919.fv_delta_depths);
         proof_ns = (uu___1850_23919.proof_ns);
         synth_hook = (uu___1850_23919.synth_hook);
         splice = (uu___1850_23919.splice);
         postprocess = (uu___1850_23919.postprocess);
         is_native_tactic = (uu___1850_23919.is_native_tactic);
         identifier_info = (uu___1850_23919.identifier_info);
         tc_hooks = (uu___1850_23919.tc_hooks);
         dsenv = (uu___1850_23919.dsenv);
         nbe = (uu___1850_23919.nbe);
         strict_args_tab = (uu___1850_23919.strict_args_tab);
         erasable_types_tab = (uu___1850_23919.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23971)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23975,(uu____23976,t)))::tl1
          ->
          let uu____23997 =
            let uu____24000 = FStar_Syntax_Free.uvars t  in
            ext out uu____24000  in
          aux uu____23997 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24003;
            FStar_Syntax_Syntax.index = uu____24004;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24012 =
            let uu____24015 = FStar_Syntax_Free.uvars t  in
            ext out uu____24015  in
          aux uu____24012 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24073)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24077,(uu____24078,t)))::tl1
          ->
          let uu____24099 =
            let uu____24102 = FStar_Syntax_Free.univs t  in
            ext out uu____24102  in
          aux uu____24099 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24105;
            FStar_Syntax_Syntax.index = uu____24106;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24114 =
            let uu____24117 = FStar_Syntax_Free.univs t  in
            ext out uu____24117  in
          aux uu____24114 tl1
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
          let uu____24179 = FStar_Util.set_add uname out  in
          aux uu____24179 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24182,(uu____24183,t)))::tl1
          ->
          let uu____24204 =
            let uu____24207 = FStar_Syntax_Free.univnames t  in
            ext out uu____24207  in
          aux uu____24204 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24210;
            FStar_Syntax_Syntax.index = uu____24211;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24219 =
            let uu____24222 = FStar_Syntax_Free.univnames t  in
            ext out uu____24222  in
          aux uu____24219 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24243  ->
            match uu___11_24243 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24247 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24260 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24271 =
      let uu____24280 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24280
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24271 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24328 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24341  ->
              match uu___12_24341 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24344 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24344
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24350) ->
                  let uu____24367 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24367))
       in
    FStar_All.pipe_right uu____24328 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24381  ->
    match uu___13_24381 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24387 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24387
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24410  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24465) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24498,uu____24499) -> false  in
      let uu____24513 =
        FStar_List.tryFind
          (fun uu____24535  ->
             match uu____24535 with | (p,uu____24546) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24513 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24565,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24595 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24595
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1993_24617 = e  in
        {
          solver = (uu___1993_24617.solver);
          range = (uu___1993_24617.range);
          curmodule = (uu___1993_24617.curmodule);
          gamma = (uu___1993_24617.gamma);
          gamma_sig = (uu___1993_24617.gamma_sig);
          gamma_cache = (uu___1993_24617.gamma_cache);
          modules = (uu___1993_24617.modules);
          expected_typ = (uu___1993_24617.expected_typ);
          sigtab = (uu___1993_24617.sigtab);
          attrtab = (uu___1993_24617.attrtab);
          instantiate_imp = (uu___1993_24617.instantiate_imp);
          effects = (uu___1993_24617.effects);
          generalize = (uu___1993_24617.generalize);
          letrecs = (uu___1993_24617.letrecs);
          top_level = (uu___1993_24617.top_level);
          check_uvars = (uu___1993_24617.check_uvars);
          use_eq = (uu___1993_24617.use_eq);
          is_iface = (uu___1993_24617.is_iface);
          admit = (uu___1993_24617.admit);
          lax = (uu___1993_24617.lax);
          lax_universes = (uu___1993_24617.lax_universes);
          phase1 = (uu___1993_24617.phase1);
          failhard = (uu___1993_24617.failhard);
          nosynth = (uu___1993_24617.nosynth);
          uvar_subtyping = (uu___1993_24617.uvar_subtyping);
          tc_term = (uu___1993_24617.tc_term);
          type_of = (uu___1993_24617.type_of);
          universe_of = (uu___1993_24617.universe_of);
          check_type_of = (uu___1993_24617.check_type_of);
          use_bv_sorts = (uu___1993_24617.use_bv_sorts);
          qtbl_name_and_index = (uu___1993_24617.qtbl_name_and_index);
          normalized_eff_names = (uu___1993_24617.normalized_eff_names);
          fv_delta_depths = (uu___1993_24617.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1993_24617.synth_hook);
          splice = (uu___1993_24617.splice);
          postprocess = (uu___1993_24617.postprocess);
          is_native_tactic = (uu___1993_24617.is_native_tactic);
          identifier_info = (uu___1993_24617.identifier_info);
          tc_hooks = (uu___1993_24617.tc_hooks);
          dsenv = (uu___1993_24617.dsenv);
          nbe = (uu___1993_24617.nbe);
          strict_args_tab = (uu___1993_24617.strict_args_tab);
          erasable_types_tab = (uu___1993_24617.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2002_24665 = e  in
      {
        solver = (uu___2002_24665.solver);
        range = (uu___2002_24665.range);
        curmodule = (uu___2002_24665.curmodule);
        gamma = (uu___2002_24665.gamma);
        gamma_sig = (uu___2002_24665.gamma_sig);
        gamma_cache = (uu___2002_24665.gamma_cache);
        modules = (uu___2002_24665.modules);
        expected_typ = (uu___2002_24665.expected_typ);
        sigtab = (uu___2002_24665.sigtab);
        attrtab = (uu___2002_24665.attrtab);
        instantiate_imp = (uu___2002_24665.instantiate_imp);
        effects = (uu___2002_24665.effects);
        generalize = (uu___2002_24665.generalize);
        letrecs = (uu___2002_24665.letrecs);
        top_level = (uu___2002_24665.top_level);
        check_uvars = (uu___2002_24665.check_uvars);
        use_eq = (uu___2002_24665.use_eq);
        is_iface = (uu___2002_24665.is_iface);
        admit = (uu___2002_24665.admit);
        lax = (uu___2002_24665.lax);
        lax_universes = (uu___2002_24665.lax_universes);
        phase1 = (uu___2002_24665.phase1);
        failhard = (uu___2002_24665.failhard);
        nosynth = (uu___2002_24665.nosynth);
        uvar_subtyping = (uu___2002_24665.uvar_subtyping);
        tc_term = (uu___2002_24665.tc_term);
        type_of = (uu___2002_24665.type_of);
        universe_of = (uu___2002_24665.universe_of);
        check_type_of = (uu___2002_24665.check_type_of);
        use_bv_sorts = (uu___2002_24665.use_bv_sorts);
        qtbl_name_and_index = (uu___2002_24665.qtbl_name_and_index);
        normalized_eff_names = (uu___2002_24665.normalized_eff_names);
        fv_delta_depths = (uu___2002_24665.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2002_24665.synth_hook);
        splice = (uu___2002_24665.splice);
        postprocess = (uu___2002_24665.postprocess);
        is_native_tactic = (uu___2002_24665.is_native_tactic);
        identifier_info = (uu___2002_24665.identifier_info);
        tc_hooks = (uu___2002_24665.tc_hooks);
        dsenv = (uu___2002_24665.dsenv);
        nbe = (uu___2002_24665.nbe);
        strict_args_tab = (uu___2002_24665.strict_args_tab);
        erasable_types_tab = (uu___2002_24665.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24681 = FStar_Syntax_Free.names t  in
      let uu____24684 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24681 uu____24684
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24707 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24707
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24717 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24717
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24738 =
      match uu____24738 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24758 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24758)
       in
    let uu____24766 =
      let uu____24770 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24770 FStar_List.rev  in
    FStar_All.pipe_right uu____24766 (FStar_String.concat " ")
  
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g  ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
  
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.guard_f 
let (is_trivial : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = [];
        univ_ineqs = ([],[]); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp  ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____24840 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24840 with
                   | FStar_Pervasives_Native.Some uu____24844 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24847 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24857;
        univ_ineqs = uu____24858; implicits = uu____24859;_} -> true
    | uu____24871 -> false
  
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs  ->
    fun g  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___2046_24902 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2046_24902.deferred);
            univ_ineqs = (uu___2046_24902.univ_ineqs);
            implicits = (uu___2046_24902.implicits)
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
          let uu____24941 = FStar_Options.defensive ()  in
          if uu____24941
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24947 =
              let uu____24949 =
                let uu____24951 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24951  in
              Prims.op_Negation uu____24949  in
            (if uu____24947
             then
               let uu____24958 =
                 let uu____24964 =
                   let uu____24966 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24968 =
                     let uu____24970 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24970
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24966 uu____24968
                    in
                 (FStar_Errors.Warning_Defensive, uu____24964)  in
               FStar_Errors.log_issue rng uu____24958
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
          let uu____25010 =
            let uu____25012 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25012  in
          if uu____25010
          then ()
          else
            (let uu____25017 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25017 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25043 =
            let uu____25045 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25045  in
          if uu____25043
          then ()
          else
            (let uu____25050 = bound_vars e  in
             def_check_closed_in rng msg uu____25050 t)
  
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng  ->
    fun msg  ->
      fun env  ->
        fun g  ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial  -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
  
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g  ->
    fun e  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2083_25089 = g  in
          let uu____25090 =
            let uu____25091 =
              let uu____25092 =
                let uu____25099 =
                  let uu____25100 =
                    let uu____25117 =
                      let uu____25128 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25128]  in
                    (f, uu____25117)  in
                  FStar_Syntax_Syntax.Tm_app uu____25100  in
                FStar_Syntax_Syntax.mk uu____25099  in
              uu____25092 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25165  -> FStar_TypeChecker_Common.NonTrivial _25165)
              uu____25091
             in
          {
            guard_f = uu____25090;
            deferred = (uu___2083_25089.deferred);
            univ_ineqs = (uu___2083_25089.univ_ineqs);
            implicits = (uu___2083_25089.implicits)
          }
  
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2090_25183 = g  in
          let uu____25184 =
            let uu____25185 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25185  in
          {
            guard_f = uu____25184;
            deferred = (uu___2090_25183.deferred);
            univ_ineqs = (uu___2090_25183.univ_ineqs);
            implicits = (uu___2090_25183.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2095_25202 = g  in
          let uu____25203 =
            let uu____25204 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25204  in
          {
            guard_f = uu____25203;
            deferred = (uu___2095_25202.deferred);
            univ_ineqs = (uu___2095_25202.univ_ineqs);
            implicits = (uu___2095_25202.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2099_25206 = g  in
          let uu____25207 =
            let uu____25208 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25208  in
          {
            guard_f = uu____25207;
            deferred = (uu___2099_25206.deferred);
            univ_ineqs = (uu___2099_25206.univ_ineqs);
            implicits = (uu___2099_25206.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25215 ->
        failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____25232 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25232
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25239 =
      let uu____25240 = FStar_Syntax_Util.unmeta t  in
      uu____25240.FStar_Syntax_Syntax.n  in
    match uu____25239 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25244 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____25287 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25287;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
  
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs  -> FStar_List.fold_left conj_guard trivial_guard gs 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____25382 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25382
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2154_25389 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2154_25389.deferred);
              univ_ineqs = (uu___2154_25389.univ_ineqs);
              implicits = (uu___2154_25389.implicits)
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
               let uu____25423 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25423
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
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___2169_25450 = g  in
            let uu____25451 =
              let uu____25452 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25452  in
            {
              guard_f = uu____25451;
              deferred = (uu___2169_25450.deferred);
              univ_ineqs = (uu___2169_25450.univ_ineqs);
              implicits = (uu___2169_25450.implicits)
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
              let uu____25510 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25510 with
              | FStar_Pervasives_Native.Some
                  (uu____25535::(tm,uu____25537)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25601 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25619 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25619;
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
                        imp_reason = reason;
                        imp_uvar = ctx_uvar;
                        imp_tm = t;
                        imp_range = r
                      }  in
                    let g =
                      let uu___2191_25651 = trivial_guard  in
                      {
                        guard_f = (uu___2191_25651.guard_f);
                        deferred = (uu___2191_25651.deferred);
                        univ_ineqs = (uu___2191_25651.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25669  -> ());
    push = (fun uu____25671  -> ());
    pop = (fun uu____25674  -> ());
    snapshot =
      (fun uu____25677  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25696  -> fun uu____25697  -> ());
    encode_sig = (fun uu____25712  -> fun uu____25713  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25719 =
             let uu____25726 = FStar_Options.peek ()  in (e, g, uu____25726)
              in
           [uu____25719]);
    solve = (fun uu____25742  -> fun uu____25743  -> fun uu____25744  -> ());
    finish = (fun uu____25751  -> ());
    refresh = (fun uu____25753  -> ())
  } 