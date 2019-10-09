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
                     (fun uu___3_15674  ->
                        match uu___3_15674 with
                        | (uu____15677,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15679);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15680;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15681;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15682;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15683;
                                         FStar_Syntax_Syntax.sigopts =
                                           uu____15684;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15706 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15706
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
                                  uu____15758 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15765 -> cache t  in
                            let uu____15766 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15766 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15772 =
                                   let uu____15773 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15773)
                                    in
                                 maybe_cache uu____15772)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15844 = find_in_sigtab env lid  in
         match uu____15844 with
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
      let uu____15925 = lookup_qname env lid  in
      match uu____15925 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15946,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16060 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16060 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16105 =
          let uu____16108 = lookup_attr env1 attr  in se1 :: uu____16108  in
        FStar_Util.smap_add (attrtab env1) attr uu____16105  in
      FStar_List.iter
        (fun attr  ->
           let uu____16118 =
             let uu____16119 = FStar_Syntax_Subst.compress attr  in
             uu____16119.FStar_Syntax_Syntax.n  in
           match uu____16118 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16123 =
                 let uu____16125 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16125.FStar_Ident.str  in
               add_one1 env se uu____16123
           | uu____16126 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16149) ->
          add_sigelts env ses
      | uu____16158 ->
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
        (fun uu___4_16196  ->
           match uu___4_16196 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16214 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16276,lb::[]),uu____16278) ->
            let uu____16287 =
              let uu____16296 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16305 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16296, uu____16305)  in
            FStar_Pervasives_Native.Some uu____16287
        | FStar_Syntax_Syntax.Sig_let ((uu____16318,lbs),uu____16320) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16352 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16365 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16365
                     then
                       let uu____16378 =
                         let uu____16387 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16396 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16387, uu____16396)  in
                       FStar_Pervasives_Native.Some uu____16378
                     else FStar_Pervasives_Native.None)
        | uu____16419 -> FStar_Pervasives_Native.None
  
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
                    let uu____16511 =
                      let uu____16513 =
                        let uu____16515 =
                          let uu____16517 =
                            let uu____16519 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16525 =
                              let uu____16527 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16527  in
                            Prims.op_Hat uu____16519 uu____16525  in
                          Prims.op_Hat ", expected " uu____16517  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16515
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16513
                       in
                    failwith uu____16511
                  else ());
             (let uu____16534 =
                let uu____16543 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16543, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16534))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____16563,uu____16564) ->
            let uu____16569 =
              let uu____16578 =
                let uu____16583 =
                  let uu____16584 =
                    let uu____16587 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____16587  in
                  (us, uu____16584)  in
                inst_ts us_opt uu____16583  in
              (uu____16578, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____16569
        | uu____16606 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16695 =
          match uu____16695 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16791,uvs,t,uu____16794,uu____16795,uu____16796);
                      FStar_Syntax_Syntax.sigrng = uu____16797;
                      FStar_Syntax_Syntax.sigquals = uu____16798;
                      FStar_Syntax_Syntax.sigmeta = uu____16799;
                      FStar_Syntax_Syntax.sigattrs = uu____16800;
                      FStar_Syntax_Syntax.sigopts = uu____16801;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16826 =
                     let uu____16835 = inst_tscheme1 (uvs, t)  in
                     (uu____16835, rng)  in
                   FStar_Pervasives_Native.Some uu____16826
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16859;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16861;
                      FStar_Syntax_Syntax.sigattrs = uu____16862;
                      FStar_Syntax_Syntax.sigopts = uu____16863;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16882 =
                     let uu____16884 = in_cur_mod env l  in uu____16884 = Yes
                      in
                   if uu____16882
                   then
                     let uu____16896 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16896
                      then
                        let uu____16912 =
                          let uu____16921 = inst_tscheme1 (uvs, t)  in
                          (uu____16921, rng)  in
                        FStar_Pervasives_Native.Some uu____16912
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16954 =
                        let uu____16963 = inst_tscheme1 (uvs, t)  in
                        (uu____16963, rng)  in
                      FStar_Pervasives_Native.Some uu____16954)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16988,uu____16989);
                      FStar_Syntax_Syntax.sigrng = uu____16990;
                      FStar_Syntax_Syntax.sigquals = uu____16991;
                      FStar_Syntax_Syntax.sigmeta = uu____16992;
                      FStar_Syntax_Syntax.sigattrs = uu____16993;
                      FStar_Syntax_Syntax.sigopts = uu____16994;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17037 =
                          let uu____17046 = inst_tscheme1 (uvs, k)  in
                          (uu____17046, rng)  in
                        FStar_Pervasives_Native.Some uu____17037
                    | uu____17067 ->
                        let uu____17068 =
                          let uu____17077 =
                            let uu____17082 =
                              let uu____17083 =
                                let uu____17086 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17086
                                 in
                              (uvs, uu____17083)  in
                            inst_tscheme1 uu____17082  in
                          (uu____17077, rng)  in
                        FStar_Pervasives_Native.Some uu____17068)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17109,uu____17110);
                      FStar_Syntax_Syntax.sigrng = uu____17111;
                      FStar_Syntax_Syntax.sigquals = uu____17112;
                      FStar_Syntax_Syntax.sigmeta = uu____17113;
                      FStar_Syntax_Syntax.sigattrs = uu____17114;
                      FStar_Syntax_Syntax.sigopts = uu____17115;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17159 =
                          let uu____17168 = inst_tscheme_with (uvs, k) us  in
                          (uu____17168, rng)  in
                        FStar_Pervasives_Native.Some uu____17159
                    | uu____17189 ->
                        let uu____17190 =
                          let uu____17199 =
                            let uu____17204 =
                              let uu____17205 =
                                let uu____17208 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17208
                                 in
                              (uvs, uu____17205)  in
                            inst_tscheme_with uu____17204 us  in
                          (uu____17199, rng)  in
                        FStar_Pervasives_Native.Some uu____17190)
               | FStar_Util.Inr se ->
                   let uu____17244 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17265;
                          FStar_Syntax_Syntax.sigrng = uu____17266;
                          FStar_Syntax_Syntax.sigquals = uu____17267;
                          FStar_Syntax_Syntax.sigmeta = uu____17268;
                          FStar_Syntax_Syntax.sigattrs = uu____17269;
                          FStar_Syntax_Syntax.sigopts = uu____17270;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17287 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17244
                     (FStar_Util.map_option
                        (fun uu____17335  ->
                           match uu____17335 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17366 =
          let uu____17377 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17377 mapper  in
        match uu____17366 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17451 =
              let uu____17462 =
                let uu____17469 =
                  let uu___857_17472 = t  in
                  let uu____17473 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___857_17472.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17473;
                    FStar_Syntax_Syntax.vars =
                      (uu___857_17472.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17469)  in
              (uu____17462, r)  in
            FStar_Pervasives_Native.Some uu____17451
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17522 = lookup_qname env l  in
      match uu____17522 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17543 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17597 = try_lookup_bv env bv  in
      match uu____17597 with
      | FStar_Pervasives_Native.None  ->
          let uu____17612 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17612 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17628 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17629 =
            let uu____17630 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17630  in
          (uu____17628, uu____17629)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17652 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17652 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17718 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17718  in
          let uu____17719 =
            let uu____17728 =
              let uu____17733 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17733)  in
            (uu____17728, r1)  in
          FStar_Pervasives_Native.Some uu____17719
  
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
        let uu____17768 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17768 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17801,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17826 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17826  in
            let uu____17827 =
              let uu____17832 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17832, r1)  in
            FStar_Pervasives_Native.Some uu____17827
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17856 = try_lookup_lid env l  in
      match uu____17856 with
      | FStar_Pervasives_Native.None  ->
          let uu____17883 = name_not_found l  in
          let uu____17889 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17883 uu____17889
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17932  ->
              match uu___5_17932 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17936 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17957 = lookup_qname env lid  in
      match uu____17957 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17966,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17969;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17971;
              FStar_Syntax_Syntax.sigattrs = uu____17972;
              FStar_Syntax_Syntax.sigopts = uu____17973;_},FStar_Pervasives_Native.None
            ),uu____17974)
          ->
          let uu____18025 =
            let uu____18032 =
              let uu____18033 =
                let uu____18036 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18036 t  in
              (uvs, uu____18033)  in
            (uu____18032, q)  in
          FStar_Pervasives_Native.Some uu____18025
      | uu____18049 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18071 = lookup_qname env lid  in
      match uu____18071 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18076,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18079;
              FStar_Syntax_Syntax.sigquals = uu____18080;
              FStar_Syntax_Syntax.sigmeta = uu____18081;
              FStar_Syntax_Syntax.sigattrs = uu____18082;
              FStar_Syntax_Syntax.sigopts = uu____18083;_},FStar_Pervasives_Native.None
            ),uu____18084)
          ->
          let uu____18135 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18135 (uvs, t)
      | uu____18140 ->
          let uu____18141 = name_not_found lid  in
          let uu____18147 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18141 uu____18147
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18167 = lookup_qname env lid  in
      match uu____18167 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18172,uvs,t,uu____18175,uu____18176,uu____18177);
              FStar_Syntax_Syntax.sigrng = uu____18178;
              FStar_Syntax_Syntax.sigquals = uu____18179;
              FStar_Syntax_Syntax.sigmeta = uu____18180;
              FStar_Syntax_Syntax.sigattrs = uu____18181;
              FStar_Syntax_Syntax.sigopts = uu____18182;_},FStar_Pervasives_Native.None
            ),uu____18183)
          ->
          let uu____18240 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18240 (uvs, t)
      | uu____18245 ->
          let uu____18246 = name_not_found lid  in
          let uu____18252 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18246 uu____18252
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18275 = lookup_qname env lid  in
      match uu____18275 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18283,uu____18284,uu____18285,uu____18286,uu____18287,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18289;
              FStar_Syntax_Syntax.sigquals = uu____18290;
              FStar_Syntax_Syntax.sigmeta = uu____18291;
              FStar_Syntax_Syntax.sigattrs = uu____18292;
              FStar_Syntax_Syntax.sigopts = uu____18293;_},uu____18294),uu____18295)
          -> (true, dcs)
      | uu____18360 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18376 = lookup_qname env lid  in
      match uu____18376 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18377,uu____18378,uu____18379,l,uu____18381,uu____18382);
              FStar_Syntax_Syntax.sigrng = uu____18383;
              FStar_Syntax_Syntax.sigquals = uu____18384;
              FStar_Syntax_Syntax.sigmeta = uu____18385;
              FStar_Syntax_Syntax.sigattrs = uu____18386;
              FStar_Syntax_Syntax.sigopts = uu____18387;_},uu____18388),uu____18389)
          -> l
      | uu____18448 ->
          let uu____18449 =
            let uu____18451 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18451  in
          failwith uu____18449
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18521)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18578) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18602 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18602
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18637 -> FStar_Pervasives_Native.None)
          | uu____18646 -> FStar_Pervasives_Native.None
  
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
        let uu____18708 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18708
  
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
        let uu____18741 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18741
  
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
             (FStar_Util.Inl uu____18793,uu____18794) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18843),uu____18844) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18893 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____18911 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____18921 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18938 ->
                  let uu____18945 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18945
              | FStar_Syntax_Syntax.Sig_let ((uu____18946,lbs),uu____18948)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18964 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18964
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18971 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____18979 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18980 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18987 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18988 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18989 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18990 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19003 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19021 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19021
           (fun d_opt  ->
              let uu____19034 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19034
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19044 =
                   let uu____19047 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19047  in
                 match uu____19044 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19048 =
                       let uu____19050 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19050
                        in
                     failwith uu____19048
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19055 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19055
                       then
                         let uu____19058 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19060 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19062 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19058 uu____19060 uu____19062
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
        (FStar_Util.Inr (se,uu____19087),uu____19088) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19137 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19159),uu____19160) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19209 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19231 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19231
  
let (fv_exists_and_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lident -> (Prims.bool * Prims.bool))
  =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19264 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19264 with
        | FStar_Pervasives_Native.None  -> (false, false)
        | FStar_Pervasives_Native.Some attrs ->
            let uu____19286 =
              FStar_All.pipe_right attrs
                (FStar_Util.for_some
                   (fun tm  ->
                      let uu____19295 =
                        let uu____19296 = FStar_Syntax_Util.un_uinst tm  in
                        uu____19296.FStar_Syntax_Syntax.n  in
                      match uu____19295 with
                      | FStar_Syntax_Syntax.Tm_fvar fv ->
                          FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                      | uu____19301 -> false))
               in
            (true, uu____19286)
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19324 = fv_exists_and_has_attr env fv_lid1 attr_lid  in
        FStar_Pervasives_Native.snd uu____19324
  
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
          let uu____19396 = FStar_Syntax_Syntax.lid_of_fv fv  in
          uu____19396.FStar_Ident.str  in
        let uu____19397 = FStar_Util.smap_try_find tab s  in
        match uu____19397 with
        | FStar_Pervasives_Native.None  ->
            let uu____19400 = f ()  in
            (match uu____19400 with
             | (should_cache,res) ->
                 (if should_cache then FStar_Util.smap_add tab s res else ();
                  res))
        | FStar_Pervasives_Native.Some r -> r
  
let (type_is_erasable : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun env  ->
    fun fv  ->
      let f uu____19438 =
        let uu____19439 =
          fv_exists_and_has_attr env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
            FStar_Parser_Const.erasable_attr
           in
        match uu____19439 with | (ex,erasable1) -> (ex, erasable1)  in
      cache_in_fv_tab env.erasable_types_tab fv f
  
let rec (non_informative : env -> FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____19473 =
        let uu____19474 = FStar_Syntax_Util.unrefine t  in
        uu____19474.FStar_Syntax_Syntax.n  in
      match uu____19473 with
      | FStar_Syntax_Syntax.Tm_type uu____19478 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid))
            || (type_is_erasable env fv)
      | FStar_Syntax_Syntax.Tm_app (head1,uu____19482) ->
          non_informative env head1
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____19508) ->
          non_informative env t1
      | FStar_Syntax_Syntax.Tm_arrow (uu____19513,c) ->
          (FStar_Syntax_Util.is_pure_or_ghost_comp c) &&
            (non_informative env (FStar_Syntax_Util.comp_result c))
      | uu____19535 -> false
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let f uu____19568 =
        let attrs =
          let uu____19574 = FStar_Syntax_Syntax.lid_of_fv fv  in
          lookup_attrs_of_lid env uu____19574  in
        match attrs with
        | FStar_Pervasives_Native.None  ->
            (false, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some attrs1 ->
            let res =
              FStar_Util.find_map attrs1
                (fun x  ->
                   let uu____19614 =
                     FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                       FStar_Parser_Const.strict_on_arguments_attr
                      in
                   FStar_Pervasives_Native.fst uu____19614)
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
      let uu____19659 = lookup_qname env ftv  in
      match uu____19659 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19663) ->
          let uu____19708 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19708 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19729,t),r) ->
               let uu____19744 =
                 let uu____19745 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19745 t  in
               FStar_Pervasives_Native.Some uu____19744)
      | uu____19746 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19758 = try_lookup_effect_lid env ftv  in
      match uu____19758 with
      | FStar_Pervasives_Native.None  ->
          let uu____19761 = name_not_found ftv  in
          let uu____19767 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19761 uu____19767
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
        let uu____19791 = lookup_qname env lid0  in
        match uu____19791 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19802);
                FStar_Syntax_Syntax.sigrng = uu____19803;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19805;
                FStar_Syntax_Syntax.sigattrs = uu____19806;
                FStar_Syntax_Syntax.sigopts = uu____19807;_},FStar_Pervasives_Native.None
              ),uu____19808)
            ->
            let lid1 =
              let uu____19864 =
                let uu____19865 = FStar_Ident.range_of_lid lid  in
                let uu____19866 =
                  let uu____19867 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19867  in
                FStar_Range.set_use_range uu____19865 uu____19866  in
              FStar_Ident.set_lid_range lid uu____19864  in
            let uu____19868 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19874  ->
                      match uu___6_19874 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19877 -> false))
               in
            if uu____19868
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19896 =
                      let uu____19898 =
                        let uu____19900 = get_range env  in
                        FStar_Range.string_of_range uu____19900  in
                      let uu____19901 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19903 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19898 uu____19901 uu____19903
                       in
                    failwith uu____19896)
                  in
               match (binders, univs1) with
               | ([],uu____19924) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19950,uu____19951::uu____19952::uu____19953) ->
                   let uu____19974 =
                     let uu____19976 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19978 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19976 uu____19978
                      in
                   failwith uu____19974
               | uu____19989 ->
                   let uu____20004 =
                     let uu____20009 =
                       let uu____20010 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20010)  in
                     inst_tscheme_with uu____20009 insts  in
                   (match uu____20004 with
                    | (uu____20023,t) ->
                        let t1 =
                          let uu____20026 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20026 t  in
                        let uu____20027 =
                          let uu____20028 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20028.FStar_Syntax_Syntax.n  in
                        (match uu____20027 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20063 -> failwith "Impossible")))
        | uu____20071 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20095 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20095 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20108,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20115 = find1 l2  in
            (match uu____20115 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20122 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20122 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20126 = find1 l  in
            (match uu____20126 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20131 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20131
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20146 = lookup_qname env l1  in
      match uu____20146 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20149;
              FStar_Syntax_Syntax.sigrng = uu____20150;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20152;
              FStar_Syntax_Syntax.sigattrs = uu____20153;
              FStar_Syntax_Syntax.sigopts = uu____20154;_},uu____20155),uu____20156)
          -> q
      | uu____20209 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20233 =
          let uu____20234 =
            let uu____20236 = FStar_Util.string_of_int i  in
            let uu____20238 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20236 uu____20238
             in
          failwith uu____20234  in
        let uu____20241 = lookup_datacon env lid  in
        match uu____20241 with
        | (uu____20246,t) ->
            let uu____20248 =
              let uu____20249 = FStar_Syntax_Subst.compress t  in
              uu____20249.FStar_Syntax_Syntax.n  in
            (match uu____20248 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20253) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20297 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20297
                      FStar_Pervasives_Native.fst)
             | uu____20308 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20322 = lookup_qname env l  in
      match uu____20322 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20324,uu____20325,uu____20326);
              FStar_Syntax_Syntax.sigrng = uu____20327;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20329;
              FStar_Syntax_Syntax.sigattrs = uu____20330;
              FStar_Syntax_Syntax.sigopts = uu____20331;_},uu____20332),uu____20333)
          ->
          FStar_Util.for_some
            (fun uu___7_20388  ->
               match uu___7_20388 with
               | FStar_Syntax_Syntax.Projector uu____20390 -> true
               | uu____20396 -> false) quals
      | uu____20398 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20412 = lookup_qname env lid  in
      match uu____20412 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20414,uu____20415,uu____20416,uu____20417,uu____20418,uu____20419);
              FStar_Syntax_Syntax.sigrng = uu____20420;
              FStar_Syntax_Syntax.sigquals = uu____20421;
              FStar_Syntax_Syntax.sigmeta = uu____20422;
              FStar_Syntax_Syntax.sigattrs = uu____20423;
              FStar_Syntax_Syntax.sigopts = uu____20424;_},uu____20425),uu____20426)
          -> true
      | uu____20486 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20500 = lookup_qname env lid  in
      match uu____20500 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20502,uu____20503,uu____20504,uu____20505,uu____20506,uu____20507);
              FStar_Syntax_Syntax.sigrng = uu____20508;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20510;
              FStar_Syntax_Syntax.sigattrs = uu____20511;
              FStar_Syntax_Syntax.sigopts = uu____20512;_},uu____20513),uu____20514)
          ->
          FStar_Util.for_some
            (fun uu___8_20577  ->
               match uu___8_20577 with
               | FStar_Syntax_Syntax.RecordType uu____20579 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20589 -> true
               | uu____20599 -> false) quals
      | uu____20601 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20611,uu____20612);
            FStar_Syntax_Syntax.sigrng = uu____20613;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20615;
            FStar_Syntax_Syntax.sigattrs = uu____20616;
            FStar_Syntax_Syntax.sigopts = uu____20617;_},uu____20618),uu____20619)
        ->
        FStar_Util.for_some
          (fun uu___9_20678  ->
             match uu___9_20678 with
             | FStar_Syntax_Syntax.Action uu____20680 -> true
             | uu____20682 -> false) quals
    | uu____20684 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20698 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20698
  
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
      let uu____20715 =
        let uu____20716 = FStar_Syntax_Util.un_uinst head1  in
        uu____20716.FStar_Syntax_Syntax.n  in
      match uu____20715 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20722 ->
               true
           | uu____20725 -> false)
      | uu____20727 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20741 = lookup_qname env l  in
      match uu____20741 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20744),uu____20745) ->
          FStar_Util.for_some
            (fun uu___10_20793  ->
               match uu___10_20793 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20796 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20798 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20874 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20892) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20910 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20918 ->
                 FStar_Pervasives_Native.Some true
             | uu____20937 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20940 =
        let uu____20944 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20944 mapper  in
      match uu____20940 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21004 = lookup_qname env lid  in
      match uu____21004 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21008,uu____21009,tps,uu____21011,uu____21012,uu____21013);
              FStar_Syntax_Syntax.sigrng = uu____21014;
              FStar_Syntax_Syntax.sigquals = uu____21015;
              FStar_Syntax_Syntax.sigmeta = uu____21016;
              FStar_Syntax_Syntax.sigattrs = uu____21017;
              FStar_Syntax_Syntax.sigopts = uu____21018;_},uu____21019),uu____21020)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21088 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21134  ->
              match uu____21134 with
              | (d,uu____21143) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21159 = effect_decl_opt env l  in
      match uu____21159 with
      | FStar_Pervasives_Native.None  ->
          let uu____21174 = name_not_found l  in
          let uu____21180 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21174 uu____21180
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____21203  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21222  ->
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
        let uu____21254 = FStar_Ident.lid_equals l1 l2  in
        if uu____21254
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21265 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21265
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21276 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21329  ->
                        match uu____21329 with
                        | (m1,m2,uu____21343,uu____21344,uu____21345) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21276 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21362 =
                    let uu____21368 =
                      let uu____21370 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21372 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21370
                        uu____21372
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21368)
                     in
                  FStar_Errors.raise_error uu____21362 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21382,uu____21383,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21417 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21417
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
  'Auu____21437 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21437) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21466 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21492  ->
                match uu____21492 with
                | (d,uu____21499) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21466 with
      | FStar_Pervasives_Native.None  ->
          let uu____21510 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21510
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21525 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21525 with
           | (uu____21536,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21554)::(wp,uu____21556)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21612 -> failwith "Impossible"))
  
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
        | uu____21677 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21690 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21690 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21707 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21707 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____21732 =
                     let uu____21738 =
                       let uu____21740 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____21748 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____21759 =
                         let uu____21761 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____21761  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____21740 uu____21748 uu____21759
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____21738)
                      in
                   FStar_Errors.raise_error uu____21732
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____21769 =
                     let uu____21780 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____21780 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____21817  ->
                        fun uu____21818  ->
                          match (uu____21817, uu____21818) with
                          | ((x,uu____21848),(t,uu____21850)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____21769
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____21881 =
                     let uu___1594_21882 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1594_21882.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1594_21882.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1594_21882.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1594_21882.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____21881
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____21894 .
    'Auu____21894 ->
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
          let uu____21924 = effect_decl_opt env effect_name  in
          match uu____21924 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____21967 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____21990 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22029 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22029
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22034 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22034
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____22045 =
                     let uu____22048 = get_range env  in
                     let uu____22049 =
                       let uu____22056 =
                         let uu____22057 =
                           let uu____22074 =
                             let uu____22085 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22085; wp]  in
                           (repr, uu____22074)  in
                         FStar_Syntax_Syntax.Tm_app uu____22057  in
                       FStar_Syntax_Syntax.mk uu____22056  in
                     uu____22049 FStar_Pervasives_Native.None uu____22048  in
                   FStar_Pervasives_Native.Some uu____22045)
  
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
      | uu____22229 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22244 =
        let uu____22245 = FStar_Syntax_Subst.compress t  in
        uu____22245.FStar_Syntax_Syntax.n  in
      match uu____22244 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22249,c) ->
          is_reifiable_comp env c
      | uu____22271 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22291 =
           let uu____22293 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22293  in
         if uu____22291
         then
           let uu____22296 =
             let uu____22302 =
               let uu____22304 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22304
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22302)  in
           let uu____22308 = get_range env  in
           FStar_Errors.raise_error uu____22296 uu____22308
         else ());
        (let uu____22311 = effect_repr_aux true env c u_c  in
         match uu____22311 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1659_22347 = env  in
        {
          solver = (uu___1659_22347.solver);
          range = (uu___1659_22347.range);
          curmodule = (uu___1659_22347.curmodule);
          gamma = (uu___1659_22347.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1659_22347.gamma_cache);
          modules = (uu___1659_22347.modules);
          expected_typ = (uu___1659_22347.expected_typ);
          sigtab = (uu___1659_22347.sigtab);
          attrtab = (uu___1659_22347.attrtab);
          instantiate_imp = (uu___1659_22347.instantiate_imp);
          effects = (uu___1659_22347.effects);
          generalize = (uu___1659_22347.generalize);
          letrecs = (uu___1659_22347.letrecs);
          top_level = (uu___1659_22347.top_level);
          check_uvars = (uu___1659_22347.check_uvars);
          use_eq = (uu___1659_22347.use_eq);
          is_iface = (uu___1659_22347.is_iface);
          admit = (uu___1659_22347.admit);
          lax = (uu___1659_22347.lax);
          lax_universes = (uu___1659_22347.lax_universes);
          phase1 = (uu___1659_22347.phase1);
          failhard = (uu___1659_22347.failhard);
          nosynth = (uu___1659_22347.nosynth);
          uvar_subtyping = (uu___1659_22347.uvar_subtyping);
          tc_term = (uu___1659_22347.tc_term);
          type_of = (uu___1659_22347.type_of);
          universe_of = (uu___1659_22347.universe_of);
          check_type_of = (uu___1659_22347.check_type_of);
          use_bv_sorts = (uu___1659_22347.use_bv_sorts);
          qtbl_name_and_index = (uu___1659_22347.qtbl_name_and_index);
          normalized_eff_names = (uu___1659_22347.normalized_eff_names);
          fv_delta_depths = (uu___1659_22347.fv_delta_depths);
          proof_ns = (uu___1659_22347.proof_ns);
          synth_hook = (uu___1659_22347.synth_hook);
          splice = (uu___1659_22347.splice);
          postprocess = (uu___1659_22347.postprocess);
          is_native_tactic = (uu___1659_22347.is_native_tactic);
          identifier_info = (uu___1659_22347.identifier_info);
          tc_hooks = (uu___1659_22347.tc_hooks);
          dsenv = (uu___1659_22347.dsenv);
          nbe = (uu___1659_22347.nbe);
          strict_args_tab = (uu___1659_22347.strict_args_tab);
          erasable_types_tab = (uu___1659_22347.erasable_types_tab)
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
    fun uu____22366  ->
      match uu____22366 with
      | (ed,quals) ->
          let effects =
            let uu___1668_22380 = env.effects  in
            {
              decls = ((ed, quals) :: ((env.effects).decls));
              order = (uu___1668_22380.order);
              joins = (uu___1668_22380.joins)
            }  in
          let uu___1671_22389 = env  in
          {
            solver = (uu___1671_22389.solver);
            range = (uu___1671_22389.range);
            curmodule = (uu___1671_22389.curmodule);
            gamma = (uu___1671_22389.gamma);
            gamma_sig = (uu___1671_22389.gamma_sig);
            gamma_cache = (uu___1671_22389.gamma_cache);
            modules = (uu___1671_22389.modules);
            expected_typ = (uu___1671_22389.expected_typ);
            sigtab = (uu___1671_22389.sigtab);
            attrtab = (uu___1671_22389.attrtab);
            instantiate_imp = (uu___1671_22389.instantiate_imp);
            effects;
            generalize = (uu___1671_22389.generalize);
            letrecs = (uu___1671_22389.letrecs);
            top_level = (uu___1671_22389.top_level);
            check_uvars = (uu___1671_22389.check_uvars);
            use_eq = (uu___1671_22389.use_eq);
            is_iface = (uu___1671_22389.is_iface);
            admit = (uu___1671_22389.admit);
            lax = (uu___1671_22389.lax);
            lax_universes = (uu___1671_22389.lax_universes);
            phase1 = (uu___1671_22389.phase1);
            failhard = (uu___1671_22389.failhard);
            nosynth = (uu___1671_22389.nosynth);
            uvar_subtyping = (uu___1671_22389.uvar_subtyping);
            tc_term = (uu___1671_22389.tc_term);
            type_of = (uu___1671_22389.type_of);
            universe_of = (uu___1671_22389.universe_of);
            check_type_of = (uu___1671_22389.check_type_of);
            use_bv_sorts = (uu___1671_22389.use_bv_sorts);
            qtbl_name_and_index = (uu___1671_22389.qtbl_name_and_index);
            normalized_eff_names = (uu___1671_22389.normalized_eff_names);
            fv_delta_depths = (uu___1671_22389.fv_delta_depths);
            proof_ns = (uu___1671_22389.proof_ns);
            synth_hook = (uu___1671_22389.synth_hook);
            splice = (uu___1671_22389.splice);
            postprocess = (uu___1671_22389.postprocess);
            is_native_tactic = (uu___1671_22389.is_native_tactic);
            identifier_info = (uu___1671_22389.identifier_info);
            tc_hooks = (uu___1671_22389.tc_hooks);
            dsenv = (uu___1671_22389.dsenv);
            nbe = (uu___1671_22389.nbe);
            strict_args_tab = (uu___1671_22389.strict_args_tab);
            erasable_types_tab = (uu___1671_22389.erasable_types_tab)
          }
  
let (update_effect_lattice : env -> FStar_Syntax_Syntax.sub_eff -> env) =
  fun env  ->
    fun sub1  ->
      let compose_edges e1 e2 =
        let composed_lift =
          let mlift_wp u r wp1 =
            let uu____22429 = (e1.mlift).mlift_wp u r wp1  in
            (e2.mlift).mlift_wp u r uu____22429  in
          let mlift_term =
            match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
            | (FStar_Pervasives_Native.Some l1,FStar_Pervasives_Native.Some
               l2) ->
                FStar_Pervasives_Native.Some
                  ((fun u  ->
                      fun t  ->
                        fun wp  ->
                          fun e  ->
                            let uu____22587 = (e1.mlift).mlift_wp u t wp  in
                            let uu____22588 = l1 u t wp e  in
                            l2 u t uu____22587 uu____22588))
            | uu____22589 -> FStar_Pervasives_Native.None  in
          { mlift_wp; mlift_term }  in
        {
          msource = (e1.msource);
          mtarget = (e2.mtarget);
          mlift = composed_lift
        }  in
      let mk_mlift_wp lift_t u r wp1 =
        let uu____22661 = inst_tscheme_with lift_t [u]  in
        match uu____22661 with
        | (uu____22668,lift_t1) ->
            let uu____22670 =
              let uu____22677 =
                let uu____22678 =
                  let uu____22695 =
                    let uu____22706 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22715 =
                      let uu____22726 = FStar_Syntax_Syntax.as_arg wp1  in
                      [uu____22726]  in
                    uu____22706 :: uu____22715  in
                  (lift_t1, uu____22695)  in
                FStar_Syntax_Syntax.Tm_app uu____22678  in
              FStar_Syntax_Syntax.mk uu____22677  in
            uu____22670 FStar_Pervasives_Native.None
              wp1.FStar_Syntax_Syntax.pos
         in
      let sub_mlift_wp =
        match sub1.FStar_Syntax_Syntax.lift_wp with
        | FStar_Pervasives_Native.Some sub_lift_wp -> mk_mlift_wp sub_lift_wp
        | FStar_Pervasives_Native.None  ->
            failwith "sub effect should've been elaborated at this stage"
         in
      let mk_mlift_term lift_t u r wp1 e =
        let uu____22836 = inst_tscheme_with lift_t [u]  in
        match uu____22836 with
        | (uu____22843,lift_t1) ->
            let uu____22845 =
              let uu____22852 =
                let uu____22853 =
                  let uu____22870 =
                    let uu____22881 = FStar_Syntax_Syntax.as_arg r  in
                    let uu____22890 =
                      let uu____22901 = FStar_Syntax_Syntax.as_arg wp1  in
                      let uu____22910 =
                        let uu____22921 = FStar_Syntax_Syntax.as_arg e  in
                        [uu____22921]  in
                      uu____22901 :: uu____22910  in
                    uu____22881 :: uu____22890  in
                  (lift_t1, uu____22870)  in
                FStar_Syntax_Syntax.Tm_app uu____22853  in
              FStar_Syntax_Syntax.mk uu____22852  in
            uu____22845 FStar_Pervasives_Native.None
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
          let uu____23023 =
            let uu____23024 =
              FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
            FStar_Syntax_Syntax.lid_as_fv uu____23024
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____23023  in
        let arg = bogus_term "ARG"  in
        let wp = bogus_term "WP"  in
        let e = bogus_term "COMP"  in
        let uu____23033 =
          let uu____23035 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
          FStar_Syntax_Print.term_to_string uu____23035  in
        let uu____23036 =
          let uu____23038 =
            FStar_Util.map_opt l.mlift_term
              (fun l1  ->
                 let uu____23066 = l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                 FStar_Syntax_Print.term_to_string uu____23066)
             in
          FStar_Util.dflt "none" uu____23038  in
        FStar_Util.format2 "{ wp : %s ; term : %s }" uu____23033 uu____23036
         in
      let order = edge :: ((env.effects).order)  in
      let ms =
        FStar_All.pipe_right (env.effects).decls
          (FStar_List.map
             (fun uu____23095  ->
                match uu____23095 with
                | (e,uu____23103) -> e.FStar_Syntax_Syntax.mname))
         in
      let find_edge order1 uu____23126 =
        match uu____23126 with
        | (i,j) ->
            let uu____23137 = FStar_Ident.lid_equals i j  in
            if uu____23137
            then
              FStar_All.pipe_right (id_edge i)
                (fun _23144  -> FStar_Pervasives_Native.Some _23144)
            else
              FStar_All.pipe_right order1
                (FStar_Util.find_opt
                   (fun e  ->
                      (FStar_Ident.lid_equals e.msource i) &&
                        (FStar_Ident.lid_equals e.mtarget j)))
         in
      let order1 =
        let fold_fun order1 k =
          let uu____23173 =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    let uu____23183 = FStar_Ident.lid_equals i k  in
                    if uu____23183
                    then []
                    else
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let uu____23197 = FStar_Ident.lid_equals j k
                                 in
                              if uu____23197
                              then []
                              else
                                (let uu____23204 =
                                   let uu____23213 = find_edge order1 (i, k)
                                      in
                                   let uu____23216 = find_edge order1 (k, j)
                                      in
                                   (uu____23213, uu____23216)  in
                                 match uu____23204 with
                                 | (FStar_Pervasives_Native.Some
                                    e1,FStar_Pervasives_Native.Some e2) ->
                                     let uu____23231 = compose_edges e1 e2
                                        in
                                     [uu____23231]
                                 | uu____23232 -> [])))))
             in
          FStar_List.append order1 uu____23173  in
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
              let uu____23262 =
                (FStar_Ident.lid_equals edge1.msource
                   FStar_Parser_Const.effect_DIV_lid)
                  &&
                  (let uu____23265 = lookup_effect_quals env edge1.mtarget
                      in
                   FStar_All.pipe_right uu____23265
                     (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                 in
              if uu____23262
              then
                let uu____23272 =
                  let uu____23278 =
                    FStar_Util.format1
                      "Divergent computations cannot be included in an effect %s marked 'total'"
                      (edge1.mtarget).FStar_Ident.str
                     in
                  (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                    uu____23278)
                   in
                let uu____23282 = get_range env  in
                FStar_Errors.raise_error uu____23272 uu____23282
              else ()));
      (let joins =
         FStar_All.pipe_right ms
           (FStar_List.collect
              (fun i  ->
                 FStar_All.pipe_right ms
                   (FStar_List.collect
                      (fun j  ->
                         let join_opt =
                           let uu____23360 = FStar_Ident.lid_equals i j  in
                           if uu____23360
                           then
                             FStar_Pervasives_Native.Some
                               (i, (id_edge i), (id_edge i))
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.fold_left
                                  (fun bopt  ->
                                     fun k  ->
                                       let uu____23412 =
                                         let uu____23421 =
                                           find_edge order2 (i, k)  in
                                         let uu____23424 =
                                           find_edge order2 (j, k)  in
                                         (uu____23421, uu____23424)  in
                                       match uu____23412 with
                                       | (FStar_Pervasives_Native.Some
                                          ik,FStar_Pervasives_Native.Some jk)
                                           ->
                                           (match bopt with
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                FStar_Pervasives_Native.Some
                                                  (k, ik, jk)
                                            | FStar_Pervasives_Native.Some
                                                (ub,uu____23466,uu____23467)
                                                ->
                                                let uu____23474 =
                                                  let uu____23481 =
                                                    let uu____23483 =
                                                      find_edge order2
                                                        (k, ub)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23483
                                                     in
                                                  let uu____23486 =
                                                    let uu____23488 =
                                                      find_edge order2
                                                        (ub, k)
                                                       in
                                                    FStar_Util.is_some
                                                      uu____23488
                                                     in
                                                  (uu____23481, uu____23486)
                                                   in
                                                (match uu____23474 with
                                                 | (true ,true ) ->
                                                     let uu____23505 =
                                                       FStar_Ident.lid_equals
                                                         k ub
                                                        in
                                                     if uu____23505
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
                                       | uu____23548 -> bopt)
                                  FStar_Pervasives_Native.None)
                            in
                         match join_opt with
                         | FStar_Pervasives_Native.None  -> []
                         | FStar_Pervasives_Native.Some (k,e1,e2) ->
                             [(i, j, k, (e1.mlift), (e2.mlift))]))))
          in
       let effects =
         let uu___1798_23621 = env.effects  in
         { decls = (uu___1798_23621.decls); order = order2; joins }  in
       let uu___1801_23622 = env  in
       {
         solver = (uu___1801_23622.solver);
         range = (uu___1801_23622.range);
         curmodule = (uu___1801_23622.curmodule);
         gamma = (uu___1801_23622.gamma);
         gamma_sig = (uu___1801_23622.gamma_sig);
         gamma_cache = (uu___1801_23622.gamma_cache);
         modules = (uu___1801_23622.modules);
         expected_typ = (uu___1801_23622.expected_typ);
         sigtab = (uu___1801_23622.sigtab);
         attrtab = (uu___1801_23622.attrtab);
         instantiate_imp = (uu___1801_23622.instantiate_imp);
         effects;
         generalize = (uu___1801_23622.generalize);
         letrecs = (uu___1801_23622.letrecs);
         top_level = (uu___1801_23622.top_level);
         check_uvars = (uu___1801_23622.check_uvars);
         use_eq = (uu___1801_23622.use_eq);
         is_iface = (uu___1801_23622.is_iface);
         admit = (uu___1801_23622.admit);
         lax = (uu___1801_23622.lax);
         lax_universes = (uu___1801_23622.lax_universes);
         phase1 = (uu___1801_23622.phase1);
         failhard = (uu___1801_23622.failhard);
         nosynth = (uu___1801_23622.nosynth);
         uvar_subtyping = (uu___1801_23622.uvar_subtyping);
         tc_term = (uu___1801_23622.tc_term);
         type_of = (uu___1801_23622.type_of);
         universe_of = (uu___1801_23622.universe_of);
         check_type_of = (uu___1801_23622.check_type_of);
         use_bv_sorts = (uu___1801_23622.use_bv_sorts);
         qtbl_name_and_index = (uu___1801_23622.qtbl_name_and_index);
         normalized_eff_names = (uu___1801_23622.normalized_eff_names);
         fv_delta_depths = (uu___1801_23622.fv_delta_depths);
         proof_ns = (uu___1801_23622.proof_ns);
         synth_hook = (uu___1801_23622.synth_hook);
         splice = (uu___1801_23622.splice);
         postprocess = (uu___1801_23622.postprocess);
         is_native_tactic = (uu___1801_23622.is_native_tactic);
         identifier_info = (uu___1801_23622.identifier_info);
         tc_hooks = (uu___1801_23622.tc_hooks);
         dsenv = (uu___1801_23622.dsenv);
         nbe = (uu___1801_23622.nbe);
         strict_args_tab = (uu___1801_23622.strict_args_tab);
         erasable_types_tab = (uu___1801_23622.erasable_types_tab)
       })
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1805_23634 = env  in
      {
        solver = (uu___1805_23634.solver);
        range = (uu___1805_23634.range);
        curmodule = (uu___1805_23634.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1805_23634.gamma_sig);
        gamma_cache = (uu___1805_23634.gamma_cache);
        modules = (uu___1805_23634.modules);
        expected_typ = (uu___1805_23634.expected_typ);
        sigtab = (uu___1805_23634.sigtab);
        attrtab = (uu___1805_23634.attrtab);
        instantiate_imp = (uu___1805_23634.instantiate_imp);
        effects = (uu___1805_23634.effects);
        generalize = (uu___1805_23634.generalize);
        letrecs = (uu___1805_23634.letrecs);
        top_level = (uu___1805_23634.top_level);
        check_uvars = (uu___1805_23634.check_uvars);
        use_eq = (uu___1805_23634.use_eq);
        is_iface = (uu___1805_23634.is_iface);
        admit = (uu___1805_23634.admit);
        lax = (uu___1805_23634.lax);
        lax_universes = (uu___1805_23634.lax_universes);
        phase1 = (uu___1805_23634.phase1);
        failhard = (uu___1805_23634.failhard);
        nosynth = (uu___1805_23634.nosynth);
        uvar_subtyping = (uu___1805_23634.uvar_subtyping);
        tc_term = (uu___1805_23634.tc_term);
        type_of = (uu___1805_23634.type_of);
        universe_of = (uu___1805_23634.universe_of);
        check_type_of = (uu___1805_23634.check_type_of);
        use_bv_sorts = (uu___1805_23634.use_bv_sorts);
        qtbl_name_and_index = (uu___1805_23634.qtbl_name_and_index);
        normalized_eff_names = (uu___1805_23634.normalized_eff_names);
        fv_delta_depths = (uu___1805_23634.fv_delta_depths);
        proof_ns = (uu___1805_23634.proof_ns);
        synth_hook = (uu___1805_23634.synth_hook);
        splice = (uu___1805_23634.splice);
        postprocess = (uu___1805_23634.postprocess);
        is_native_tactic = (uu___1805_23634.is_native_tactic);
        identifier_info = (uu___1805_23634.identifier_info);
        tc_hooks = (uu___1805_23634.tc_hooks);
        dsenv = (uu___1805_23634.dsenv);
        nbe = (uu___1805_23634.nbe);
        strict_args_tab = (uu___1805_23634.strict_args_tab);
        erasable_types_tab = (uu___1805_23634.erasable_types_tab)
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
            (let uu___1818_23692 = env  in
             {
               solver = (uu___1818_23692.solver);
               range = (uu___1818_23692.range);
               curmodule = (uu___1818_23692.curmodule);
               gamma = rest;
               gamma_sig = (uu___1818_23692.gamma_sig);
               gamma_cache = (uu___1818_23692.gamma_cache);
               modules = (uu___1818_23692.modules);
               expected_typ = (uu___1818_23692.expected_typ);
               sigtab = (uu___1818_23692.sigtab);
               attrtab = (uu___1818_23692.attrtab);
               instantiate_imp = (uu___1818_23692.instantiate_imp);
               effects = (uu___1818_23692.effects);
               generalize = (uu___1818_23692.generalize);
               letrecs = (uu___1818_23692.letrecs);
               top_level = (uu___1818_23692.top_level);
               check_uvars = (uu___1818_23692.check_uvars);
               use_eq = (uu___1818_23692.use_eq);
               is_iface = (uu___1818_23692.is_iface);
               admit = (uu___1818_23692.admit);
               lax = (uu___1818_23692.lax);
               lax_universes = (uu___1818_23692.lax_universes);
               phase1 = (uu___1818_23692.phase1);
               failhard = (uu___1818_23692.failhard);
               nosynth = (uu___1818_23692.nosynth);
               uvar_subtyping = (uu___1818_23692.uvar_subtyping);
               tc_term = (uu___1818_23692.tc_term);
               type_of = (uu___1818_23692.type_of);
               universe_of = (uu___1818_23692.universe_of);
               check_type_of = (uu___1818_23692.check_type_of);
               use_bv_sorts = (uu___1818_23692.use_bv_sorts);
               qtbl_name_and_index = (uu___1818_23692.qtbl_name_and_index);
               normalized_eff_names = (uu___1818_23692.normalized_eff_names);
               fv_delta_depths = (uu___1818_23692.fv_delta_depths);
               proof_ns = (uu___1818_23692.proof_ns);
               synth_hook = (uu___1818_23692.synth_hook);
               splice = (uu___1818_23692.splice);
               postprocess = (uu___1818_23692.postprocess);
               is_native_tactic = (uu___1818_23692.is_native_tactic);
               identifier_info = (uu___1818_23692.identifier_info);
               tc_hooks = (uu___1818_23692.tc_hooks);
               dsenv = (uu___1818_23692.dsenv);
               nbe = (uu___1818_23692.nbe);
               strict_args_tab = (uu___1818_23692.strict_args_tab);
               erasable_types_tab = (uu___1818_23692.erasable_types_tab)
             }))
    | uu____23693 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23722  ->
             match uu____23722 with | (x,uu____23730) -> push_bv env1 x) env
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
            let uu___1832_23765 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1832_23765.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1832_23765.FStar_Syntax_Syntax.index);
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
        let uu____23838 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23838 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23866 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23866)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1853_23882 = env  in
      {
        solver = (uu___1853_23882.solver);
        range = (uu___1853_23882.range);
        curmodule = (uu___1853_23882.curmodule);
        gamma = (uu___1853_23882.gamma);
        gamma_sig = (uu___1853_23882.gamma_sig);
        gamma_cache = (uu___1853_23882.gamma_cache);
        modules = (uu___1853_23882.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1853_23882.sigtab);
        attrtab = (uu___1853_23882.attrtab);
        instantiate_imp = (uu___1853_23882.instantiate_imp);
        effects = (uu___1853_23882.effects);
        generalize = (uu___1853_23882.generalize);
        letrecs = (uu___1853_23882.letrecs);
        top_level = (uu___1853_23882.top_level);
        check_uvars = (uu___1853_23882.check_uvars);
        use_eq = false;
        is_iface = (uu___1853_23882.is_iface);
        admit = (uu___1853_23882.admit);
        lax = (uu___1853_23882.lax);
        lax_universes = (uu___1853_23882.lax_universes);
        phase1 = (uu___1853_23882.phase1);
        failhard = (uu___1853_23882.failhard);
        nosynth = (uu___1853_23882.nosynth);
        uvar_subtyping = (uu___1853_23882.uvar_subtyping);
        tc_term = (uu___1853_23882.tc_term);
        type_of = (uu___1853_23882.type_of);
        universe_of = (uu___1853_23882.universe_of);
        check_type_of = (uu___1853_23882.check_type_of);
        use_bv_sorts = (uu___1853_23882.use_bv_sorts);
        qtbl_name_and_index = (uu___1853_23882.qtbl_name_and_index);
        normalized_eff_names = (uu___1853_23882.normalized_eff_names);
        fv_delta_depths = (uu___1853_23882.fv_delta_depths);
        proof_ns = (uu___1853_23882.proof_ns);
        synth_hook = (uu___1853_23882.synth_hook);
        splice = (uu___1853_23882.splice);
        postprocess = (uu___1853_23882.postprocess);
        is_native_tactic = (uu___1853_23882.is_native_tactic);
        identifier_info = (uu___1853_23882.identifier_info);
        tc_hooks = (uu___1853_23882.tc_hooks);
        dsenv = (uu___1853_23882.dsenv);
        nbe = (uu___1853_23882.nbe);
        strict_args_tab = (uu___1853_23882.strict_args_tab);
        erasable_types_tab = (uu___1853_23882.erasable_types_tab)
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
    let uu____23913 = expected_typ env_  in
    ((let uu___1860_23919 = env_  in
      {
        solver = (uu___1860_23919.solver);
        range = (uu___1860_23919.range);
        curmodule = (uu___1860_23919.curmodule);
        gamma = (uu___1860_23919.gamma);
        gamma_sig = (uu___1860_23919.gamma_sig);
        gamma_cache = (uu___1860_23919.gamma_cache);
        modules = (uu___1860_23919.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1860_23919.sigtab);
        attrtab = (uu___1860_23919.attrtab);
        instantiate_imp = (uu___1860_23919.instantiate_imp);
        effects = (uu___1860_23919.effects);
        generalize = (uu___1860_23919.generalize);
        letrecs = (uu___1860_23919.letrecs);
        top_level = (uu___1860_23919.top_level);
        check_uvars = (uu___1860_23919.check_uvars);
        use_eq = false;
        is_iface = (uu___1860_23919.is_iface);
        admit = (uu___1860_23919.admit);
        lax = (uu___1860_23919.lax);
        lax_universes = (uu___1860_23919.lax_universes);
        phase1 = (uu___1860_23919.phase1);
        failhard = (uu___1860_23919.failhard);
        nosynth = (uu___1860_23919.nosynth);
        uvar_subtyping = (uu___1860_23919.uvar_subtyping);
        tc_term = (uu___1860_23919.tc_term);
        type_of = (uu___1860_23919.type_of);
        universe_of = (uu___1860_23919.universe_of);
        check_type_of = (uu___1860_23919.check_type_of);
        use_bv_sorts = (uu___1860_23919.use_bv_sorts);
        qtbl_name_and_index = (uu___1860_23919.qtbl_name_and_index);
        normalized_eff_names = (uu___1860_23919.normalized_eff_names);
        fv_delta_depths = (uu___1860_23919.fv_delta_depths);
        proof_ns = (uu___1860_23919.proof_ns);
        synth_hook = (uu___1860_23919.synth_hook);
        splice = (uu___1860_23919.splice);
        postprocess = (uu___1860_23919.postprocess);
        is_native_tactic = (uu___1860_23919.is_native_tactic);
        identifier_info = (uu___1860_23919.identifier_info);
        tc_hooks = (uu___1860_23919.tc_hooks);
        dsenv = (uu___1860_23919.dsenv);
        nbe = (uu___1860_23919.nbe);
        strict_args_tab = (uu___1860_23919.strict_args_tab);
        erasable_types_tab = (uu___1860_23919.erasable_types_tab)
      }), uu____23913)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23931 =
      let uu____23934 = FStar_Ident.id_of_text ""  in [uu____23934]  in
    FStar_Ident.lid_of_ids uu____23931  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23941 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23941
        then
          let uu____23946 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23946 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1868_23974 = env  in
       {
         solver = (uu___1868_23974.solver);
         range = (uu___1868_23974.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1868_23974.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1868_23974.expected_typ);
         sigtab = (uu___1868_23974.sigtab);
         attrtab = (uu___1868_23974.attrtab);
         instantiate_imp = (uu___1868_23974.instantiate_imp);
         effects = (uu___1868_23974.effects);
         generalize = (uu___1868_23974.generalize);
         letrecs = (uu___1868_23974.letrecs);
         top_level = (uu___1868_23974.top_level);
         check_uvars = (uu___1868_23974.check_uvars);
         use_eq = (uu___1868_23974.use_eq);
         is_iface = (uu___1868_23974.is_iface);
         admit = (uu___1868_23974.admit);
         lax = (uu___1868_23974.lax);
         lax_universes = (uu___1868_23974.lax_universes);
         phase1 = (uu___1868_23974.phase1);
         failhard = (uu___1868_23974.failhard);
         nosynth = (uu___1868_23974.nosynth);
         uvar_subtyping = (uu___1868_23974.uvar_subtyping);
         tc_term = (uu___1868_23974.tc_term);
         type_of = (uu___1868_23974.type_of);
         universe_of = (uu___1868_23974.universe_of);
         check_type_of = (uu___1868_23974.check_type_of);
         use_bv_sorts = (uu___1868_23974.use_bv_sorts);
         qtbl_name_and_index = (uu___1868_23974.qtbl_name_and_index);
         normalized_eff_names = (uu___1868_23974.normalized_eff_names);
         fv_delta_depths = (uu___1868_23974.fv_delta_depths);
         proof_ns = (uu___1868_23974.proof_ns);
         synth_hook = (uu___1868_23974.synth_hook);
         splice = (uu___1868_23974.splice);
         postprocess = (uu___1868_23974.postprocess);
         is_native_tactic = (uu___1868_23974.is_native_tactic);
         identifier_info = (uu___1868_23974.identifier_info);
         tc_hooks = (uu___1868_23974.tc_hooks);
         dsenv = (uu___1868_23974.dsenv);
         nbe = (uu___1868_23974.nbe);
         strict_args_tab = (uu___1868_23974.strict_args_tab);
         erasable_types_tab = (uu___1868_23974.erasable_types_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24026)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24030,(uu____24031,t)))::tl1
          ->
          let uu____24052 =
            let uu____24055 = FStar_Syntax_Free.uvars t  in
            ext out uu____24055  in
          aux uu____24052 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24058;
            FStar_Syntax_Syntax.index = uu____24059;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24067 =
            let uu____24070 = FStar_Syntax_Free.uvars t  in
            ext out uu____24070  in
          aux uu____24067 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24128)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24132,(uu____24133,t)))::tl1
          ->
          let uu____24154 =
            let uu____24157 = FStar_Syntax_Free.univs t  in
            ext out uu____24157  in
          aux uu____24154 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24160;
            FStar_Syntax_Syntax.index = uu____24161;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24169 =
            let uu____24172 = FStar_Syntax_Free.univs t  in
            ext out uu____24172  in
          aux uu____24169 tl1
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
          let uu____24234 = FStar_Util.set_add uname out  in
          aux uu____24234 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24237,(uu____24238,t)))::tl1
          ->
          let uu____24259 =
            let uu____24262 = FStar_Syntax_Free.univnames t  in
            ext out uu____24262  in
          aux uu____24259 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24265;
            FStar_Syntax_Syntax.index = uu____24266;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24274 =
            let uu____24277 = FStar_Syntax_Free.univnames t  in
            ext out uu____24277  in
          aux uu____24274 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24298  ->
            match uu___11_24298 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24302 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24315 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24326 =
      let uu____24335 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24335
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24326 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24383 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24396  ->
              match uu___12_24396 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24399 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24399
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24405) ->
                  let uu____24422 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24422))
       in
    FStar_All.pipe_right uu____24383 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24436  ->
    match uu___13_24436 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24442 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24442
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24465  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24520) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24553,uu____24554) -> false  in
      let uu____24568 =
        FStar_List.tryFind
          (fun uu____24590  ->
             match uu____24590 with | (p,uu____24601) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24568 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24620,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24650 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24650
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2011_24672 = e  in
        {
          solver = (uu___2011_24672.solver);
          range = (uu___2011_24672.range);
          curmodule = (uu___2011_24672.curmodule);
          gamma = (uu___2011_24672.gamma);
          gamma_sig = (uu___2011_24672.gamma_sig);
          gamma_cache = (uu___2011_24672.gamma_cache);
          modules = (uu___2011_24672.modules);
          expected_typ = (uu___2011_24672.expected_typ);
          sigtab = (uu___2011_24672.sigtab);
          attrtab = (uu___2011_24672.attrtab);
          instantiate_imp = (uu___2011_24672.instantiate_imp);
          effects = (uu___2011_24672.effects);
          generalize = (uu___2011_24672.generalize);
          letrecs = (uu___2011_24672.letrecs);
          top_level = (uu___2011_24672.top_level);
          check_uvars = (uu___2011_24672.check_uvars);
          use_eq = (uu___2011_24672.use_eq);
          is_iface = (uu___2011_24672.is_iface);
          admit = (uu___2011_24672.admit);
          lax = (uu___2011_24672.lax);
          lax_universes = (uu___2011_24672.lax_universes);
          phase1 = (uu___2011_24672.phase1);
          failhard = (uu___2011_24672.failhard);
          nosynth = (uu___2011_24672.nosynth);
          uvar_subtyping = (uu___2011_24672.uvar_subtyping);
          tc_term = (uu___2011_24672.tc_term);
          type_of = (uu___2011_24672.type_of);
          universe_of = (uu___2011_24672.universe_of);
          check_type_of = (uu___2011_24672.check_type_of);
          use_bv_sorts = (uu___2011_24672.use_bv_sorts);
          qtbl_name_and_index = (uu___2011_24672.qtbl_name_and_index);
          normalized_eff_names = (uu___2011_24672.normalized_eff_names);
          fv_delta_depths = (uu___2011_24672.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2011_24672.synth_hook);
          splice = (uu___2011_24672.splice);
          postprocess = (uu___2011_24672.postprocess);
          is_native_tactic = (uu___2011_24672.is_native_tactic);
          identifier_info = (uu___2011_24672.identifier_info);
          tc_hooks = (uu___2011_24672.tc_hooks);
          dsenv = (uu___2011_24672.dsenv);
          nbe = (uu___2011_24672.nbe);
          strict_args_tab = (uu___2011_24672.strict_args_tab);
          erasable_types_tab = (uu___2011_24672.erasable_types_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2020_24720 = e  in
      {
        solver = (uu___2020_24720.solver);
        range = (uu___2020_24720.range);
        curmodule = (uu___2020_24720.curmodule);
        gamma = (uu___2020_24720.gamma);
        gamma_sig = (uu___2020_24720.gamma_sig);
        gamma_cache = (uu___2020_24720.gamma_cache);
        modules = (uu___2020_24720.modules);
        expected_typ = (uu___2020_24720.expected_typ);
        sigtab = (uu___2020_24720.sigtab);
        attrtab = (uu___2020_24720.attrtab);
        instantiate_imp = (uu___2020_24720.instantiate_imp);
        effects = (uu___2020_24720.effects);
        generalize = (uu___2020_24720.generalize);
        letrecs = (uu___2020_24720.letrecs);
        top_level = (uu___2020_24720.top_level);
        check_uvars = (uu___2020_24720.check_uvars);
        use_eq = (uu___2020_24720.use_eq);
        is_iface = (uu___2020_24720.is_iface);
        admit = (uu___2020_24720.admit);
        lax = (uu___2020_24720.lax);
        lax_universes = (uu___2020_24720.lax_universes);
        phase1 = (uu___2020_24720.phase1);
        failhard = (uu___2020_24720.failhard);
        nosynth = (uu___2020_24720.nosynth);
        uvar_subtyping = (uu___2020_24720.uvar_subtyping);
        tc_term = (uu___2020_24720.tc_term);
        type_of = (uu___2020_24720.type_of);
        universe_of = (uu___2020_24720.universe_of);
        check_type_of = (uu___2020_24720.check_type_of);
        use_bv_sorts = (uu___2020_24720.use_bv_sorts);
        qtbl_name_and_index = (uu___2020_24720.qtbl_name_and_index);
        normalized_eff_names = (uu___2020_24720.normalized_eff_names);
        fv_delta_depths = (uu___2020_24720.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2020_24720.synth_hook);
        splice = (uu___2020_24720.splice);
        postprocess = (uu___2020_24720.postprocess);
        is_native_tactic = (uu___2020_24720.is_native_tactic);
        identifier_info = (uu___2020_24720.identifier_info);
        tc_hooks = (uu___2020_24720.tc_hooks);
        dsenv = (uu___2020_24720.dsenv);
        nbe = (uu___2020_24720.nbe);
        strict_args_tab = (uu___2020_24720.strict_args_tab);
        erasable_types_tab = (uu___2020_24720.erasable_types_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24736 = FStar_Syntax_Free.names t  in
      let uu____24739 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24736 uu____24739
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24762 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24762
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24772 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24772
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24793 =
      match uu____24793 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24813 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24813)
       in
    let uu____24821 =
      let uu____24825 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24825 FStar_List.rev  in
    FStar_All.pipe_right uu____24821 (FStar_String.concat " ")
  
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
                  (let uu____24895 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24895 with
                   | FStar_Pervasives_Native.Some uu____24899 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24902 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24912;
        univ_ineqs = uu____24913; implicits = uu____24914;_} -> true
    | uu____24926 -> false
  
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
          let uu___2064_24957 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2064_24957.deferred);
            univ_ineqs = (uu___2064_24957.univ_ineqs);
            implicits = (uu___2064_24957.implicits)
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
          let uu____24996 = FStar_Options.defensive ()  in
          if uu____24996
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25002 =
              let uu____25004 =
                let uu____25006 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25006  in
              Prims.op_Negation uu____25004  in
            (if uu____25002
             then
               let uu____25013 =
                 let uu____25019 =
                   let uu____25021 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25023 =
                     let uu____25025 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25025
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25021 uu____25023
                    in
                 (FStar_Errors.Warning_Defensive, uu____25019)  in
               FStar_Errors.log_issue rng uu____25013
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
          let uu____25065 =
            let uu____25067 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25067  in
          if uu____25065
          then ()
          else
            (let uu____25072 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25072 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25098 =
            let uu____25100 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25100  in
          if uu____25098
          then ()
          else
            (let uu____25105 = bound_vars e  in
             def_check_closed_in rng msg uu____25105 t)
  
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
          let uu___2101_25144 = g  in
          let uu____25145 =
            let uu____25146 =
              let uu____25147 =
                let uu____25154 =
                  let uu____25155 =
                    let uu____25172 =
                      let uu____25183 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25183]  in
                    (f, uu____25172)  in
                  FStar_Syntax_Syntax.Tm_app uu____25155  in
                FStar_Syntax_Syntax.mk uu____25154  in
              uu____25147 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25220  -> FStar_TypeChecker_Common.NonTrivial _25220)
              uu____25146
             in
          {
            guard_f = uu____25145;
            deferred = (uu___2101_25144.deferred);
            univ_ineqs = (uu___2101_25144.univ_ineqs);
            implicits = (uu___2101_25144.implicits)
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
          let uu___2108_25238 = g  in
          let uu____25239 =
            let uu____25240 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25240  in
          {
            guard_f = uu____25239;
            deferred = (uu___2108_25238.deferred);
            univ_ineqs = (uu___2108_25238.univ_ineqs);
            implicits = (uu___2108_25238.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2113_25257 = g  in
          let uu____25258 =
            let uu____25259 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25259  in
          {
            guard_f = uu____25258;
            deferred = (uu___2113_25257.deferred);
            univ_ineqs = (uu___2113_25257.univ_ineqs);
            implicits = (uu___2113_25257.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2117_25261 = g  in
          let uu____25262 =
            let uu____25263 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25263  in
          {
            guard_f = uu____25262;
            deferred = (uu___2117_25261.deferred);
            univ_ineqs = (uu___2117_25261.univ_ineqs);
            implicits = (uu___2117_25261.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25270 ->
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
          let uu____25287 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25287
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25294 =
      let uu____25295 = FStar_Syntax_Util.unmeta t  in
      uu____25295.FStar_Syntax_Syntax.n  in
    match uu____25294 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25299 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25342 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25342;
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
                       let uu____25437 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25437
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2172_25444 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2172_25444.deferred);
              univ_ineqs = (uu___2172_25444.univ_ineqs);
              implicits = (uu___2172_25444.implicits)
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
               let uu____25478 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25478
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
            let uu___2187_25505 = g  in
            let uu____25506 =
              let uu____25507 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25507  in
            {
              guard_f = uu____25506;
              deferred = (uu___2187_25505.deferred);
              univ_ineqs = (uu___2187_25505.univ_ineqs);
              implicits = (uu___2187_25505.implicits)
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
              let uu____25565 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25565 with
              | FStar_Pervasives_Native.Some
                  (uu____25590::(tm,uu____25592)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25656 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25674 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25674;
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
                      let uu___2209_25706 = trivial_guard  in
                      {
                        guard_f = (uu___2209_25706.guard_f);
                        deferred = (uu___2209_25706.deferred);
                        univ_ineqs = (uu___2209_25706.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25724  -> ());
    push = (fun uu____25726  -> ());
    pop = (fun uu____25729  -> ());
    snapshot =
      (fun uu____25732  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____25751  -> fun uu____25752  -> ());
    encode_sig = (fun uu____25767  -> fun uu____25768  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25774 =
             let uu____25781 = FStar_Options.peek ()  in (e, g, uu____25781)
              in
           [uu____25774]);
    solve = (fun uu____25797  -> fun uu____25798  -> fun uu____25799  -> ());
    finish = (fun uu____25806  -> ());
    refresh = (fun uu____25808  -> ())
  } 