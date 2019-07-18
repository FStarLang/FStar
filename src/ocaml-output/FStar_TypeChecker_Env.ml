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
  is_pattern: Prims.bool ;
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
  try_solve_implicits_hook:
    env -> FStar_Syntax_Syntax.term -> implicit Prims.list -> unit ;
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
    }
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        solver
  
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        range
  
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        curmodule
  
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        gamma
  
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        gamma_sig
  
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        gamma_cache
  
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        modules
  
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        expected_typ
  
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        sigtab
  
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        attrtab
  
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        is_pattern
  
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        instantiate_imp
  
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        effects
  
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        generalize
  
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        letrecs
  
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        top_level
  
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        check_uvars
  
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        use_eq
  
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        is_iface
  
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        admit1
  
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        lax1
  
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        lax_universes
  
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        phase1
  
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        failhard
  
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        nosynth
  
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        uvar_subtyping
  
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        tc_term
  
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        type_of
  
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        universe_of
  
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        check_type_of
  
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        use_bv_sorts
  
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap * (FStar_Ident.lident * Prims.int)
      FStar_Pervasives_Native.option))
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        qtbl_name_and_index
  
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        normalized_eff_names
  
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        fv_delta_depths
  
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        proof_ns
  
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env -> env -> FStar_Syntax_Syntax.term -> implicit Prims.list -> unit) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        try_solve_implicits_hook
  
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        splice1
  
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        postprocess
  
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        is_native_tactic
  
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        identifier_info
  
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        tc_hooks
  
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        dsenv
  
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { solver; range; curmodule; gamma; gamma_sig; gamma_cache; modules;
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;_} ->
        nbe1
  
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
           (fun uu___0_12567  ->
              match uu___0_12567 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12570 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12570  in
                  let uu____12571 =
                    let uu____12572 = FStar_Syntax_Subst.compress y  in
                    uu____12572.FStar_Syntax_Syntax.n  in
                  (match uu____12571 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12576 =
                         let uu___332_12577 = y1  in
                         let uu____12578 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___332_12577.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___332_12577.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12578
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12576
                   | uu____12581 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___338_12595 = env  in
      let uu____12596 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___338_12595.solver);
        range = (uu___338_12595.range);
        curmodule = (uu___338_12595.curmodule);
        gamma = uu____12596;
        gamma_sig = (uu___338_12595.gamma_sig);
        gamma_cache = (uu___338_12595.gamma_cache);
        modules = (uu___338_12595.modules);
        expected_typ = (uu___338_12595.expected_typ);
        sigtab = (uu___338_12595.sigtab);
        attrtab = (uu___338_12595.attrtab);
        is_pattern = (uu___338_12595.is_pattern);
        instantiate_imp = (uu___338_12595.instantiate_imp);
        effects = (uu___338_12595.effects);
        generalize = (uu___338_12595.generalize);
        letrecs = (uu___338_12595.letrecs);
        top_level = (uu___338_12595.top_level);
        check_uvars = (uu___338_12595.check_uvars);
        use_eq = (uu___338_12595.use_eq);
        is_iface = (uu___338_12595.is_iface);
        admit = (uu___338_12595.admit);
        lax = (uu___338_12595.lax);
        lax_universes = (uu___338_12595.lax_universes);
        phase1 = (uu___338_12595.phase1);
        failhard = (uu___338_12595.failhard);
        nosynth = (uu___338_12595.nosynth);
        uvar_subtyping = (uu___338_12595.uvar_subtyping);
        tc_term = (uu___338_12595.tc_term);
        type_of = (uu___338_12595.type_of);
        universe_of = (uu___338_12595.universe_of);
        check_type_of = (uu___338_12595.check_type_of);
        use_bv_sorts = (uu___338_12595.use_bv_sorts);
        qtbl_name_and_index = (uu___338_12595.qtbl_name_and_index);
        normalized_eff_names = (uu___338_12595.normalized_eff_names);
        fv_delta_depths = (uu___338_12595.fv_delta_depths);
        proof_ns = (uu___338_12595.proof_ns);
        synth_hook = (uu___338_12595.synth_hook);
        try_solve_implicits_hook = (uu___338_12595.try_solve_implicits_hook);
        splice = (uu___338_12595.splice);
        postprocess = (uu___338_12595.postprocess);
        is_native_tactic = (uu___338_12595.is_native_tactic);
        identifier_info = (uu___338_12595.identifier_info);
        tc_hooks = (uu___338_12595.tc_hooks);
        dsenv = (uu___338_12595.dsenv);
        nbe = (uu___338_12595.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12604  -> fun uu____12605  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___345_12627 = env  in
      {
        solver = (uu___345_12627.solver);
        range = (uu___345_12627.range);
        curmodule = (uu___345_12627.curmodule);
        gamma = (uu___345_12627.gamma);
        gamma_sig = (uu___345_12627.gamma_sig);
        gamma_cache = (uu___345_12627.gamma_cache);
        modules = (uu___345_12627.modules);
        expected_typ = (uu___345_12627.expected_typ);
        sigtab = (uu___345_12627.sigtab);
        attrtab = (uu___345_12627.attrtab);
        is_pattern = (uu___345_12627.is_pattern);
        instantiate_imp = (uu___345_12627.instantiate_imp);
        effects = (uu___345_12627.effects);
        generalize = (uu___345_12627.generalize);
        letrecs = (uu___345_12627.letrecs);
        top_level = (uu___345_12627.top_level);
        check_uvars = (uu___345_12627.check_uvars);
        use_eq = (uu___345_12627.use_eq);
        is_iface = (uu___345_12627.is_iface);
        admit = (uu___345_12627.admit);
        lax = (uu___345_12627.lax);
        lax_universes = (uu___345_12627.lax_universes);
        phase1 = (uu___345_12627.phase1);
        failhard = (uu___345_12627.failhard);
        nosynth = (uu___345_12627.nosynth);
        uvar_subtyping = (uu___345_12627.uvar_subtyping);
        tc_term = (uu___345_12627.tc_term);
        type_of = (uu___345_12627.type_of);
        universe_of = (uu___345_12627.universe_of);
        check_type_of = (uu___345_12627.check_type_of);
        use_bv_sorts = (uu___345_12627.use_bv_sorts);
        qtbl_name_and_index = (uu___345_12627.qtbl_name_and_index);
        normalized_eff_names = (uu___345_12627.normalized_eff_names);
        fv_delta_depths = (uu___345_12627.fv_delta_depths);
        proof_ns = (uu___345_12627.proof_ns);
        synth_hook = (uu___345_12627.synth_hook);
        try_solve_implicits_hook = (uu___345_12627.try_solve_implicits_hook);
        splice = (uu___345_12627.splice);
        postprocess = (uu___345_12627.postprocess);
        is_native_tactic = (uu___345_12627.is_native_tactic);
        identifier_info = (uu___345_12627.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___345_12627.dsenv);
        nbe = (uu___345_12627.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___349_12639 = e  in
      let uu____12640 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___349_12639.solver);
        range = (uu___349_12639.range);
        curmodule = (uu___349_12639.curmodule);
        gamma = (uu___349_12639.gamma);
        gamma_sig = (uu___349_12639.gamma_sig);
        gamma_cache = (uu___349_12639.gamma_cache);
        modules = (uu___349_12639.modules);
        expected_typ = (uu___349_12639.expected_typ);
        sigtab = (uu___349_12639.sigtab);
        attrtab = (uu___349_12639.attrtab);
        is_pattern = (uu___349_12639.is_pattern);
        instantiate_imp = (uu___349_12639.instantiate_imp);
        effects = (uu___349_12639.effects);
        generalize = (uu___349_12639.generalize);
        letrecs = (uu___349_12639.letrecs);
        top_level = (uu___349_12639.top_level);
        check_uvars = (uu___349_12639.check_uvars);
        use_eq = (uu___349_12639.use_eq);
        is_iface = (uu___349_12639.is_iface);
        admit = (uu___349_12639.admit);
        lax = (uu___349_12639.lax);
        lax_universes = (uu___349_12639.lax_universes);
        phase1 = (uu___349_12639.phase1);
        failhard = (uu___349_12639.failhard);
        nosynth = (uu___349_12639.nosynth);
        uvar_subtyping = (uu___349_12639.uvar_subtyping);
        tc_term = (uu___349_12639.tc_term);
        type_of = (uu___349_12639.type_of);
        universe_of = (uu___349_12639.universe_of);
        check_type_of = (uu___349_12639.check_type_of);
        use_bv_sorts = (uu___349_12639.use_bv_sorts);
        qtbl_name_and_index = (uu___349_12639.qtbl_name_and_index);
        normalized_eff_names = (uu___349_12639.normalized_eff_names);
        fv_delta_depths = (uu___349_12639.fv_delta_depths);
        proof_ns = (uu___349_12639.proof_ns);
        synth_hook = (uu___349_12639.synth_hook);
        try_solve_implicits_hook = (uu___349_12639.try_solve_implicits_hook);
        splice = (uu___349_12639.splice);
        postprocess = (uu___349_12639.postprocess);
        is_native_tactic = (uu___349_12639.is_native_tactic);
        identifier_info = (uu___349_12639.identifier_info);
        tc_hooks = (uu___349_12639.tc_hooks);
        dsenv = uu____12640;
        nbe = (uu___349_12639.nbe)
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
      | (NoDelta ,uu____12669) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12672,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12674,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12677 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____12691 . unit -> 'Auu____12691 FStar_Util.smap =
  fun uu____12698  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12704 . unit -> 'Auu____12704 FStar_Util.smap =
  fun uu____12711  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____12849 = new_gamma_cache ()  in
                  let uu____12852 = new_sigtab ()  in
                  let uu____12855 = new_sigtab ()  in
                  let uu____12862 =
                    let uu____12877 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12877, FStar_Pervasives_Native.None)  in
                  let uu____12898 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12902 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12906 = FStar_Options.using_facts_from ()  in
                  let uu____12907 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12910 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12849;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12852;
                    attrtab = uu____12855;
                    is_pattern = false;
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
                    qtbl_name_and_index = uu____12862;
                    normalized_eff_names = uu____12898;
                    fv_delta_depths = uu____12902;
                    proof_ns = uu____12906;
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
                    is_native_tactic = (fun uu____12981  -> false);
                    identifier_info = uu____12907;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12910;
                    nbe = nbe1
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
  fun uu____13060  ->
    let uu____13061 = FStar_ST.op_Bang query_indices  in
    match uu____13061 with
    | [] -> failwith "Empty query indices!"
    | uu____13116 ->
        let uu____13126 =
          let uu____13136 =
            let uu____13144 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13144  in
          let uu____13198 = FStar_ST.op_Bang query_indices  in uu____13136 ::
            uu____13198
           in
        FStar_ST.op_Colon_Equals query_indices uu____13126
  
let (pop_query_indices : unit -> unit) =
  fun uu____13294  ->
    let uu____13295 = FStar_ST.op_Bang query_indices  in
    match uu____13295 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13422  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13459  ->
    match uu____13459 with
    | (l,n1) ->
        let uu____13469 = FStar_ST.op_Bang query_indices  in
        (match uu____13469 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13591 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13614  ->
    let uu____13615 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13615
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13683 =
       let uu____13686 = FStar_ST.op_Bang stack  in env :: uu____13686  in
     FStar_ST.op_Colon_Equals stack uu____13683);
    (let uu___420_13735 = env  in
     let uu____13736 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13739 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13742 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13749 =
       let uu____13764 =
         let uu____13768 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13768  in
       let uu____13800 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13764, uu____13800)  in
     let uu____13849 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13852 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13855 =
       let uu____13858 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13858  in
     {
       solver = (uu___420_13735.solver);
       range = (uu___420_13735.range);
       curmodule = (uu___420_13735.curmodule);
       gamma = (uu___420_13735.gamma);
       gamma_sig = (uu___420_13735.gamma_sig);
       gamma_cache = uu____13736;
       modules = (uu___420_13735.modules);
       expected_typ = (uu___420_13735.expected_typ);
       sigtab = uu____13739;
       attrtab = uu____13742;
       is_pattern = (uu___420_13735.is_pattern);
       instantiate_imp = (uu___420_13735.instantiate_imp);
       effects = (uu___420_13735.effects);
       generalize = (uu___420_13735.generalize);
       letrecs = (uu___420_13735.letrecs);
       top_level = (uu___420_13735.top_level);
       check_uvars = (uu___420_13735.check_uvars);
       use_eq = (uu___420_13735.use_eq);
       is_iface = (uu___420_13735.is_iface);
       admit = (uu___420_13735.admit);
       lax = (uu___420_13735.lax);
       lax_universes = (uu___420_13735.lax_universes);
       phase1 = (uu___420_13735.phase1);
       failhard = (uu___420_13735.failhard);
       nosynth = (uu___420_13735.nosynth);
       uvar_subtyping = (uu___420_13735.uvar_subtyping);
       tc_term = (uu___420_13735.tc_term);
       type_of = (uu___420_13735.type_of);
       universe_of = (uu___420_13735.universe_of);
       check_type_of = (uu___420_13735.check_type_of);
       use_bv_sorts = (uu___420_13735.use_bv_sorts);
       qtbl_name_and_index = uu____13749;
       normalized_eff_names = uu____13849;
       fv_delta_depths = uu____13852;
       proof_ns = (uu___420_13735.proof_ns);
       synth_hook = (uu___420_13735.synth_hook);
       try_solve_implicits_hook = (uu___420_13735.try_solve_implicits_hook);
       splice = (uu___420_13735.splice);
       postprocess = (uu___420_13735.postprocess);
       is_native_tactic = (uu___420_13735.is_native_tactic);
       identifier_info = uu____13855;
       tc_hooks = (uu___420_13735.tc_hooks);
       dsenv = (uu___420_13735.dsenv);
       nbe = (uu___420_13735.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13883  ->
    let uu____13884 = FStar_ST.op_Bang stack  in
    match uu____13884 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13938 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14028  ->
           let uu____14029 = snapshot_stack env  in
           match uu____14029 with
           | (stack_depth,env1) ->
               let uu____14063 = snapshot_query_indices ()  in
               (match uu____14063 with
                | (query_indices_depth,()) ->
                    let uu____14096 = (env1.solver).snapshot msg  in
                    (match uu____14096 with
                     | (solver_depth,()) ->
                         let uu____14153 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14153 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___445_14220 = env1  in
                                 {
                                   solver = (uu___445_14220.solver);
                                   range = (uu___445_14220.range);
                                   curmodule = (uu___445_14220.curmodule);
                                   gamma = (uu___445_14220.gamma);
                                   gamma_sig = (uu___445_14220.gamma_sig);
                                   gamma_cache = (uu___445_14220.gamma_cache);
                                   modules = (uu___445_14220.modules);
                                   expected_typ =
                                     (uu___445_14220.expected_typ);
                                   sigtab = (uu___445_14220.sigtab);
                                   attrtab = (uu___445_14220.attrtab);
                                   is_pattern = (uu___445_14220.is_pattern);
                                   instantiate_imp =
                                     (uu___445_14220.instantiate_imp);
                                   effects = (uu___445_14220.effects);
                                   generalize = (uu___445_14220.generalize);
                                   letrecs = (uu___445_14220.letrecs);
                                   top_level = (uu___445_14220.top_level);
                                   check_uvars = (uu___445_14220.check_uvars);
                                   use_eq = (uu___445_14220.use_eq);
                                   is_iface = (uu___445_14220.is_iface);
                                   admit = (uu___445_14220.admit);
                                   lax = (uu___445_14220.lax);
                                   lax_universes =
                                     (uu___445_14220.lax_universes);
                                   phase1 = (uu___445_14220.phase1);
                                   failhard = (uu___445_14220.failhard);
                                   nosynth = (uu___445_14220.nosynth);
                                   uvar_subtyping =
                                     (uu___445_14220.uvar_subtyping);
                                   tc_term = (uu___445_14220.tc_term);
                                   type_of = (uu___445_14220.type_of);
                                   universe_of = (uu___445_14220.universe_of);
                                   check_type_of =
                                     (uu___445_14220.check_type_of);
                                   use_bv_sorts =
                                     (uu___445_14220.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___445_14220.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___445_14220.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___445_14220.fv_delta_depths);
                                   proof_ns = (uu___445_14220.proof_ns);
                                   synth_hook = (uu___445_14220.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___445_14220.try_solve_implicits_hook);
                                   splice = (uu___445_14220.splice);
                                   postprocess = (uu___445_14220.postprocess);
                                   is_native_tactic =
                                     (uu___445_14220.is_native_tactic);
                                   identifier_info =
                                     (uu___445_14220.identifier_info);
                                   tc_hooks = (uu___445_14220.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___445_14220.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14254  ->
             let uu____14255 =
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
             match uu____14255 with
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
                             ((let uu____14435 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14435
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14451 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14451
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14483,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14525 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14555  ->
                  match uu____14555 with
                  | (m,uu____14563) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14525 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___490_14578 = env  in
               {
                 solver = (uu___490_14578.solver);
                 range = (uu___490_14578.range);
                 curmodule = (uu___490_14578.curmodule);
                 gamma = (uu___490_14578.gamma);
                 gamma_sig = (uu___490_14578.gamma_sig);
                 gamma_cache = (uu___490_14578.gamma_cache);
                 modules = (uu___490_14578.modules);
                 expected_typ = (uu___490_14578.expected_typ);
                 sigtab = (uu___490_14578.sigtab);
                 attrtab = (uu___490_14578.attrtab);
                 is_pattern = (uu___490_14578.is_pattern);
                 instantiate_imp = (uu___490_14578.instantiate_imp);
                 effects = (uu___490_14578.effects);
                 generalize = (uu___490_14578.generalize);
                 letrecs = (uu___490_14578.letrecs);
                 top_level = (uu___490_14578.top_level);
                 check_uvars = (uu___490_14578.check_uvars);
                 use_eq = (uu___490_14578.use_eq);
                 is_iface = (uu___490_14578.is_iface);
                 admit = (uu___490_14578.admit);
                 lax = (uu___490_14578.lax);
                 lax_universes = (uu___490_14578.lax_universes);
                 phase1 = (uu___490_14578.phase1);
                 failhard = (uu___490_14578.failhard);
                 nosynth = (uu___490_14578.nosynth);
                 uvar_subtyping = (uu___490_14578.uvar_subtyping);
                 tc_term = (uu___490_14578.tc_term);
                 type_of = (uu___490_14578.type_of);
                 universe_of = (uu___490_14578.universe_of);
                 check_type_of = (uu___490_14578.check_type_of);
                 use_bv_sorts = (uu___490_14578.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___490_14578.normalized_eff_names);
                 fv_delta_depths = (uu___490_14578.fv_delta_depths);
                 proof_ns = (uu___490_14578.proof_ns);
                 synth_hook = (uu___490_14578.synth_hook);
                 try_solve_implicits_hook =
                   (uu___490_14578.try_solve_implicits_hook);
                 splice = (uu___490_14578.splice);
                 postprocess = (uu___490_14578.postprocess);
                 is_native_tactic = (uu___490_14578.is_native_tactic);
                 identifier_info = (uu___490_14578.identifier_info);
                 tc_hooks = (uu___490_14578.tc_hooks);
                 dsenv = (uu___490_14578.dsenv);
                 nbe = (uu___490_14578.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____14595,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___499_14611 = env  in
               {
                 solver = (uu___499_14611.solver);
                 range = (uu___499_14611.range);
                 curmodule = (uu___499_14611.curmodule);
                 gamma = (uu___499_14611.gamma);
                 gamma_sig = (uu___499_14611.gamma_sig);
                 gamma_cache = (uu___499_14611.gamma_cache);
                 modules = (uu___499_14611.modules);
                 expected_typ = (uu___499_14611.expected_typ);
                 sigtab = (uu___499_14611.sigtab);
                 attrtab = (uu___499_14611.attrtab);
                 is_pattern = (uu___499_14611.is_pattern);
                 instantiate_imp = (uu___499_14611.instantiate_imp);
                 effects = (uu___499_14611.effects);
                 generalize = (uu___499_14611.generalize);
                 letrecs = (uu___499_14611.letrecs);
                 top_level = (uu___499_14611.top_level);
                 check_uvars = (uu___499_14611.check_uvars);
                 use_eq = (uu___499_14611.use_eq);
                 is_iface = (uu___499_14611.is_iface);
                 admit = (uu___499_14611.admit);
                 lax = (uu___499_14611.lax);
                 lax_universes = (uu___499_14611.lax_universes);
                 phase1 = (uu___499_14611.phase1);
                 failhard = (uu___499_14611.failhard);
                 nosynth = (uu___499_14611.nosynth);
                 uvar_subtyping = (uu___499_14611.uvar_subtyping);
                 tc_term = (uu___499_14611.tc_term);
                 type_of = (uu___499_14611.type_of);
                 universe_of = (uu___499_14611.universe_of);
                 check_type_of = (uu___499_14611.check_type_of);
                 use_bv_sorts = (uu___499_14611.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___499_14611.normalized_eff_names);
                 fv_delta_depths = (uu___499_14611.fv_delta_depths);
                 proof_ns = (uu___499_14611.proof_ns);
                 synth_hook = (uu___499_14611.synth_hook);
                 try_solve_implicits_hook =
                   (uu___499_14611.try_solve_implicits_hook);
                 splice = (uu___499_14611.splice);
                 postprocess = (uu___499_14611.postprocess);
                 is_native_tactic = (uu___499_14611.is_native_tactic);
                 identifier_info = (uu___499_14611.identifier_info);
                 tc_hooks = (uu___499_14611.tc_hooks);
                 dsenv = (uu___499_14611.dsenv);
                 nbe = (uu___499_14611.nbe)
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
        (let uu___506_14654 = e  in
         {
           solver = (uu___506_14654.solver);
           range = r;
           curmodule = (uu___506_14654.curmodule);
           gamma = (uu___506_14654.gamma);
           gamma_sig = (uu___506_14654.gamma_sig);
           gamma_cache = (uu___506_14654.gamma_cache);
           modules = (uu___506_14654.modules);
           expected_typ = (uu___506_14654.expected_typ);
           sigtab = (uu___506_14654.sigtab);
           attrtab = (uu___506_14654.attrtab);
           is_pattern = (uu___506_14654.is_pattern);
           instantiate_imp = (uu___506_14654.instantiate_imp);
           effects = (uu___506_14654.effects);
           generalize = (uu___506_14654.generalize);
           letrecs = (uu___506_14654.letrecs);
           top_level = (uu___506_14654.top_level);
           check_uvars = (uu___506_14654.check_uvars);
           use_eq = (uu___506_14654.use_eq);
           is_iface = (uu___506_14654.is_iface);
           admit = (uu___506_14654.admit);
           lax = (uu___506_14654.lax);
           lax_universes = (uu___506_14654.lax_universes);
           phase1 = (uu___506_14654.phase1);
           failhard = (uu___506_14654.failhard);
           nosynth = (uu___506_14654.nosynth);
           uvar_subtyping = (uu___506_14654.uvar_subtyping);
           tc_term = (uu___506_14654.tc_term);
           type_of = (uu___506_14654.type_of);
           universe_of = (uu___506_14654.universe_of);
           check_type_of = (uu___506_14654.check_type_of);
           use_bv_sorts = (uu___506_14654.use_bv_sorts);
           qtbl_name_and_index = (uu___506_14654.qtbl_name_and_index);
           normalized_eff_names = (uu___506_14654.normalized_eff_names);
           fv_delta_depths = (uu___506_14654.fv_delta_depths);
           proof_ns = (uu___506_14654.proof_ns);
           synth_hook = (uu___506_14654.synth_hook);
           try_solve_implicits_hook =
             (uu___506_14654.try_solve_implicits_hook);
           splice = (uu___506_14654.splice);
           postprocess = (uu___506_14654.postprocess);
           is_native_tactic = (uu___506_14654.is_native_tactic);
           identifier_info = (uu___506_14654.identifier_info);
           tc_hooks = (uu___506_14654.tc_hooks);
           dsenv = (uu___506_14654.dsenv);
           nbe = (uu___506_14654.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14674 =
        let uu____14675 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14675 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14674
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14730 =
          let uu____14731 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14731 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14730
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14786 =
          let uu____14787 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14787 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14786
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14842 =
        let uu____14843 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14843 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14842
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___523_14907 = env  in
      {
        solver = (uu___523_14907.solver);
        range = (uu___523_14907.range);
        curmodule = lid;
        gamma = (uu___523_14907.gamma);
        gamma_sig = (uu___523_14907.gamma_sig);
        gamma_cache = (uu___523_14907.gamma_cache);
        modules = (uu___523_14907.modules);
        expected_typ = (uu___523_14907.expected_typ);
        sigtab = (uu___523_14907.sigtab);
        attrtab = (uu___523_14907.attrtab);
        is_pattern = (uu___523_14907.is_pattern);
        instantiate_imp = (uu___523_14907.instantiate_imp);
        effects = (uu___523_14907.effects);
        generalize = (uu___523_14907.generalize);
        letrecs = (uu___523_14907.letrecs);
        top_level = (uu___523_14907.top_level);
        check_uvars = (uu___523_14907.check_uvars);
        use_eq = (uu___523_14907.use_eq);
        is_iface = (uu___523_14907.is_iface);
        admit = (uu___523_14907.admit);
        lax = (uu___523_14907.lax);
        lax_universes = (uu___523_14907.lax_universes);
        phase1 = (uu___523_14907.phase1);
        failhard = (uu___523_14907.failhard);
        nosynth = (uu___523_14907.nosynth);
        uvar_subtyping = (uu___523_14907.uvar_subtyping);
        tc_term = (uu___523_14907.tc_term);
        type_of = (uu___523_14907.type_of);
        universe_of = (uu___523_14907.universe_of);
        check_type_of = (uu___523_14907.check_type_of);
        use_bv_sorts = (uu___523_14907.use_bv_sorts);
        qtbl_name_and_index = (uu___523_14907.qtbl_name_and_index);
        normalized_eff_names = (uu___523_14907.normalized_eff_names);
        fv_delta_depths = (uu___523_14907.fv_delta_depths);
        proof_ns = (uu___523_14907.proof_ns);
        synth_hook = (uu___523_14907.synth_hook);
        try_solve_implicits_hook = (uu___523_14907.try_solve_implicits_hook);
        splice = (uu___523_14907.splice);
        postprocess = (uu___523_14907.postprocess);
        is_native_tactic = (uu___523_14907.is_native_tactic);
        identifier_info = (uu___523_14907.identifier_info);
        tc_hooks = (uu___523_14907.tc_hooks);
        dsenv = (uu___523_14907.dsenv);
        nbe = (uu___523_14907.nbe)
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
      let uu____14938 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14938
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14951 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14951)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14966 =
      let uu____14968 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14968  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14966)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14977  ->
    let uu____14978 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14978
  
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals  ->
    fun us  ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
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
      | ((formals,t),uu____15078) ->
          let vs = mk_univ_subst formals us  in
          let uu____15102 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15102)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15119  ->
    match uu___1_15119 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15145  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15165 = inst_tscheme t  in
      match uu____15165 with
      | (us,t1) ->
          let uu____15176 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15176)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____15197  ->
          match uu____15197 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____15219 =
                         let uu____15221 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____15225 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____15229 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____15231 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____15221 uu____15225 uu____15229 uu____15231
                          in
                       failwith uu____15219)
                    else ();
                    (let uu____15236 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____15236))
               | uu____15245 ->
                   let uu____15246 =
                     let uu____15248 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____15248
                      in
                   failwith uu____15246)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15260 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15271 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15282 -> false
  
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
             | ([],uu____15330) -> Maybe
             | (uu____15337,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15357 -> No  in
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
          let uu____15451 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15451 with
          | FStar_Pervasives_Native.None  ->
              let uu____15474 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15518  ->
                     match uu___2_15518 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15557 = FStar_Ident.lid_equals lid l  in
                         if uu____15557
                         then
                           let uu____15580 =
                             let uu____15599 =
                               let uu____15614 = inst_tscheme t  in
                               FStar_Util.Inl uu____15614  in
                             let uu____15629 = FStar_Ident.range_of_lid l  in
                             (uu____15599, uu____15629)  in
                           FStar_Pervasives_Native.Some uu____15580
                         else FStar_Pervasives_Native.None
                     | uu____15682 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15474
                (fun uu____15720  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_15729  ->
                        match uu___3_15729 with
                        | (uu____15732,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15734);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15735;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15736;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15737;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15738;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15758 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15758
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
                                  uu____15810 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15817 -> cache t  in
                            let uu____15818 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15818 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15824 =
                                   let uu____15825 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15825)
                                    in
                                 maybe_cache uu____15824)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15896 = find_in_sigtab env lid  in
         match uu____15896 with
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
      let uu____15977 = lookup_qname env lid  in
      match uu____15977 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15998,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16112 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16112 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16157 =
          let uu____16160 = lookup_attr env1 attr  in se1 :: uu____16160  in
        FStar_Util.smap_add (attrtab env1) attr uu____16157  in
      FStar_List.iter
        (fun attr  ->
           let uu____16170 =
             let uu____16171 = FStar_Syntax_Subst.compress attr  in
             uu____16171.FStar_Syntax_Syntax.n  in
           match uu____16170 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16175 =
                 let uu____16177 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16177.FStar_Ident.str  in
               add_one1 env se uu____16175
           | uu____16178 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16201) ->
          add_sigelts env ses
      | uu____16210 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____16225 -> ()))

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
        (fun uu___4_16257  ->
           match uu___4_16257 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16275 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16337,lb::[]),uu____16339) ->
            let uu____16348 =
              let uu____16357 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16366 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16357, uu____16366)  in
            FStar_Pervasives_Native.Some uu____16348
        | FStar_Syntax_Syntax.Sig_let ((uu____16379,lbs),uu____16381) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16413 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16426 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16426
                     then
                       let uu____16439 =
                         let uu____16448 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16457 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16448, uu____16457)  in
                       FStar_Pervasives_Native.Some uu____16439
                     else FStar_Pervasives_Native.None)
        | uu____16480 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____16540 =
            let uu____16549 =
              let uu____16554 =
                let uu____16555 =
                  let uu____16558 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____16558
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____16555)  in
              inst_tscheme1 uu____16554  in
            (uu____16549, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16540
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16580,uu____16581) ->
          let uu____16586 =
            let uu____16595 =
              let uu____16600 =
                let uu____16601 =
                  let uu____16604 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16604  in
                (us, uu____16601)  in
              inst_tscheme1 uu____16600  in
            (uu____16595, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16586
      | uu____16623 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16712 =
          match uu____16712 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16808,uvs,t,uu____16811,uu____16812,uu____16813);
                      FStar_Syntax_Syntax.sigrng = uu____16814;
                      FStar_Syntax_Syntax.sigquals = uu____16815;
                      FStar_Syntax_Syntax.sigmeta = uu____16816;
                      FStar_Syntax_Syntax.sigattrs = uu____16817;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16840 =
                     let uu____16849 = inst_tscheme1 (uvs, t)  in
                     (uu____16849, rng)  in
                   FStar_Pervasives_Native.Some uu____16840
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16873;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16875;
                      FStar_Syntax_Syntax.sigattrs = uu____16876;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16893 =
                     let uu____16895 = in_cur_mod env l  in uu____16895 = Yes
                      in
                   if uu____16893
                   then
                     let uu____16907 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16907
                      then
                        let uu____16923 =
                          let uu____16932 = inst_tscheme1 (uvs, t)  in
                          (uu____16932, rng)  in
                        FStar_Pervasives_Native.Some uu____16923
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16965 =
                        let uu____16974 = inst_tscheme1 (uvs, t)  in
                        (uu____16974, rng)  in
                      FStar_Pervasives_Native.Some uu____16965)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16999,uu____17000);
                      FStar_Syntax_Syntax.sigrng = uu____17001;
                      FStar_Syntax_Syntax.sigquals = uu____17002;
                      FStar_Syntax_Syntax.sigmeta = uu____17003;
                      FStar_Syntax_Syntax.sigattrs = uu____17004;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17045 =
                          let uu____17054 = inst_tscheme1 (uvs, k)  in
                          (uu____17054, rng)  in
                        FStar_Pervasives_Native.Some uu____17045
                    | uu____17075 ->
                        let uu____17076 =
                          let uu____17085 =
                            let uu____17090 =
                              let uu____17091 =
                                let uu____17094 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17094
                                 in
                              (uvs, uu____17091)  in
                            inst_tscheme1 uu____17090  in
                          (uu____17085, rng)  in
                        FStar_Pervasives_Native.Some uu____17076)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17117,uu____17118);
                      FStar_Syntax_Syntax.sigrng = uu____17119;
                      FStar_Syntax_Syntax.sigquals = uu____17120;
                      FStar_Syntax_Syntax.sigmeta = uu____17121;
                      FStar_Syntax_Syntax.sigattrs = uu____17122;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17164 =
                          let uu____17173 = inst_tscheme_with (uvs, k) us  in
                          (uu____17173, rng)  in
                        FStar_Pervasives_Native.Some uu____17164
                    | uu____17194 ->
                        let uu____17195 =
                          let uu____17204 =
                            let uu____17209 =
                              let uu____17210 =
                                let uu____17213 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17213
                                 in
                              (uvs, uu____17210)  in
                            inst_tscheme_with uu____17209 us  in
                          (uu____17204, rng)  in
                        FStar_Pervasives_Native.Some uu____17195)
               | FStar_Util.Inr se ->
                   let uu____17249 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17270;
                          FStar_Syntax_Syntax.sigrng = uu____17271;
                          FStar_Syntax_Syntax.sigquals = uu____17272;
                          FStar_Syntax_Syntax.sigmeta = uu____17273;
                          FStar_Syntax_Syntax.sigattrs = uu____17274;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17289 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____17249
                     (FStar_Util.map_option
                        (fun uu____17337  ->
                           match uu____17337 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17368 =
          let uu____17379 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17379 mapper  in
        match uu____17368 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17453 =
              let uu____17464 =
                let uu____17471 =
                  let uu___850_17474 = t  in
                  let uu____17475 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___850_17474.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17475;
                    FStar_Syntax_Syntax.vars =
                      (uu___850_17474.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17471)  in
              (uu____17464, r)  in
            FStar_Pervasives_Native.Some uu____17453
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17524 = lookup_qname env l  in
      match uu____17524 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17545 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17599 = try_lookup_bv env bv  in
      match uu____17599 with
      | FStar_Pervasives_Native.None  ->
          let uu____17614 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17614 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17630 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17631 =
            let uu____17632 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17632  in
          (uu____17630, uu____17631)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17654 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17654 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17720 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17720  in
          let uu____17721 =
            let uu____17730 =
              let uu____17735 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17735)  in
            (uu____17730, r1)  in
          FStar_Pervasives_Native.Some uu____17721
  
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
        let uu____17770 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17770 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17803,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17828 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17828  in
            let uu____17829 =
              let uu____17834 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17834, r1)  in
            FStar_Pervasives_Native.Some uu____17829
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17858 = try_lookup_lid env l  in
      match uu____17858 with
      | FStar_Pervasives_Native.None  ->
          let uu____17885 = name_not_found l  in
          let uu____17891 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17885 uu____17891
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_17934  ->
              match uu___5_17934 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17938 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17959 = lookup_qname env lid  in
      match uu____17959 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17968,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17971;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17973;
              FStar_Syntax_Syntax.sigattrs = uu____17974;_},FStar_Pervasives_Native.None
            ),uu____17975)
          ->
          let uu____18024 =
            let uu____18031 =
              let uu____18032 =
                let uu____18035 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18035 t  in
              (uvs, uu____18032)  in
            (uu____18031, q)  in
          FStar_Pervasives_Native.Some uu____18024
      | uu____18048 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18070 = lookup_qname env lid  in
      match uu____18070 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18075,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18078;
              FStar_Syntax_Syntax.sigquals = uu____18079;
              FStar_Syntax_Syntax.sigmeta = uu____18080;
              FStar_Syntax_Syntax.sigattrs = uu____18081;_},FStar_Pervasives_Native.None
            ),uu____18082)
          ->
          let uu____18131 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18131 (uvs, t)
      | uu____18136 ->
          let uu____18137 = name_not_found lid  in
          let uu____18143 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18137 uu____18143
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18163 = lookup_qname env lid  in
      match uu____18163 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18168,uvs,t,uu____18171,uu____18172,uu____18173);
              FStar_Syntax_Syntax.sigrng = uu____18174;
              FStar_Syntax_Syntax.sigquals = uu____18175;
              FStar_Syntax_Syntax.sigmeta = uu____18176;
              FStar_Syntax_Syntax.sigattrs = uu____18177;_},FStar_Pervasives_Native.None
            ),uu____18178)
          ->
          let uu____18233 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18233 (uvs, t)
      | uu____18238 ->
          let uu____18239 = name_not_found lid  in
          let uu____18245 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18239 uu____18245
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18268 = lookup_qname env lid  in
      match uu____18268 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18276,uu____18277,uu____18278,uu____18279,uu____18280,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18282;
              FStar_Syntax_Syntax.sigquals = uu____18283;
              FStar_Syntax_Syntax.sigmeta = uu____18284;
              FStar_Syntax_Syntax.sigattrs = uu____18285;_},uu____18286),uu____18287)
          -> (true, dcs)
      | uu____18350 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18366 = lookup_qname env lid  in
      match uu____18366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18367,uu____18368,uu____18369,l,uu____18371,uu____18372);
              FStar_Syntax_Syntax.sigrng = uu____18373;
              FStar_Syntax_Syntax.sigquals = uu____18374;
              FStar_Syntax_Syntax.sigmeta = uu____18375;
              FStar_Syntax_Syntax.sigattrs = uu____18376;_},uu____18377),uu____18378)
          -> l
      | uu____18435 ->
          let uu____18436 =
            let uu____18438 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18438  in
          failwith uu____18436
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18508)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18565) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18589 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18589
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18624 -> FStar_Pervasives_Native.None)
          | uu____18633 -> FStar_Pervasives_Native.None
  
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
        let uu____18695 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18695
  
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
        let uu____18728 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18728
  
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
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____18780,uu____18781) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18830),uu____18831) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18880 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18898 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18908 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18925 ->
                  let uu____18932 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18932
              | FStar_Syntax_Syntax.Sig_let ((uu____18933,lbs),uu____18935)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18951 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18951
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18958 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18966 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18967 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18974 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18975 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18976 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18977 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18990 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19008 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19008
           (fun d_opt  ->
              let uu____19021 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19021
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19031 =
                   let uu____19034 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19034  in
                 match uu____19031 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19035 =
                       let uu____19037 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19037
                        in
                     failwith uu____19035
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19042 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19042
                       then
                         let uu____19045 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19047 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19049 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19045 uu____19047 uu____19049
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
        (FStar_Util.Inr (se,uu____19074),uu____19075) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19124 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19146),uu____19147) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19196 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19218 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19218
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19241 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19241 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19265 =
                      let uu____19266 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19266.FStar_Syntax_Syntax.n  in
                    match uu____19265 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19271 -> false))
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____19305 = lookup_qname env ftv  in
      match uu____19305 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19309) ->
          let uu____19354 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____19354 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19375,t),r) ->
               let uu____19390 =
                 let uu____19391 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19391 t  in
               FStar_Pervasives_Native.Some uu____19390)
      | uu____19392 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19404 = try_lookup_effect_lid env ftv  in
      match uu____19404 with
      | FStar_Pervasives_Native.None  ->
          let uu____19407 = name_not_found ftv  in
          let uu____19413 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19407 uu____19413
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
        let uu____19437 = lookup_qname env lid0  in
        match uu____19437 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19448);
                FStar_Syntax_Syntax.sigrng = uu____19449;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19451;
                FStar_Syntax_Syntax.sigattrs = uu____19452;_},FStar_Pervasives_Native.None
              ),uu____19453)
            ->
            let lid1 =
              let uu____19507 =
                let uu____19508 = FStar_Ident.range_of_lid lid  in
                let uu____19509 =
                  let uu____19510 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19510  in
                FStar_Range.set_use_range uu____19508 uu____19509  in
              FStar_Ident.set_lid_range lid uu____19507  in
            let uu____19511 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_19517  ->
                      match uu___6_19517 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19520 -> false))
               in
            if uu____19511
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19539 =
                      let uu____19541 =
                        let uu____19543 = get_range env  in
                        FStar_Range.string_of_range uu____19543  in
                      let uu____19544 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19546 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19541 uu____19544 uu____19546
                       in
                    failwith uu____19539)
                  in
               match (binders, univs1) with
               | ([],uu____19567) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19593,uu____19594::uu____19595::uu____19596) ->
                   let uu____19617 =
                     let uu____19619 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19621 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19619 uu____19621
                      in
                   failwith uu____19617
               | uu____19632 ->
                   let uu____19647 =
                     let uu____19652 =
                       let uu____19653 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19653)  in
                     inst_tscheme_with uu____19652 insts  in
                   (match uu____19647 with
                    | (uu____19666,t) ->
                        let t1 =
                          let uu____19669 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19669 t  in
                        let uu____19670 =
                          let uu____19671 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19671.FStar_Syntax_Syntax.n  in
                        (match uu____19670 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19706 -> failwith "Impossible")))
        | uu____19714 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19738 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19738 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19751,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19758 = find1 l2  in
            (match uu____19758 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19765 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19765 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19769 = find1 l  in
            (match uu____19769 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19774 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19774
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19789 = lookup_qname env l1  in
      match uu____19789 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19792;
              FStar_Syntax_Syntax.sigrng = uu____19793;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19795;
              FStar_Syntax_Syntax.sigattrs = uu____19796;_},uu____19797),uu____19798)
          -> q
      | uu____19849 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19873 =
          let uu____19874 =
            let uu____19876 = FStar_Util.string_of_int i  in
            let uu____19878 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19876 uu____19878
             in
          failwith uu____19874  in
        let uu____19881 = lookup_datacon env lid  in
        match uu____19881 with
        | (uu____19886,t) ->
            let uu____19888 =
              let uu____19889 = FStar_Syntax_Subst.compress t  in
              uu____19889.FStar_Syntax_Syntax.n  in
            (match uu____19888 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19893) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19937 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19937
                      FStar_Pervasives_Native.fst)
             | uu____19948 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19962 = lookup_qname env l  in
      match uu____19962 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19964,uu____19965,uu____19966);
              FStar_Syntax_Syntax.sigrng = uu____19967;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19969;
              FStar_Syntax_Syntax.sigattrs = uu____19970;_},uu____19971),uu____19972)
          ->
          FStar_Util.for_some
            (fun uu___7_20025  ->
               match uu___7_20025 with
               | FStar_Syntax_Syntax.Projector uu____20027 -> true
               | uu____20033 -> false) quals
      | uu____20035 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20049 = lookup_qname env lid  in
      match uu____20049 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20051,uu____20052,uu____20053,uu____20054,uu____20055,uu____20056);
              FStar_Syntax_Syntax.sigrng = uu____20057;
              FStar_Syntax_Syntax.sigquals = uu____20058;
              FStar_Syntax_Syntax.sigmeta = uu____20059;
              FStar_Syntax_Syntax.sigattrs = uu____20060;_},uu____20061),uu____20062)
          -> true
      | uu____20120 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20134 = lookup_qname env lid  in
      match uu____20134 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20136,uu____20137,uu____20138,uu____20139,uu____20140,uu____20141);
              FStar_Syntax_Syntax.sigrng = uu____20142;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20144;
              FStar_Syntax_Syntax.sigattrs = uu____20145;_},uu____20146),uu____20147)
          ->
          FStar_Util.for_some
            (fun uu___8_20208  ->
               match uu___8_20208 with
               | FStar_Syntax_Syntax.RecordType uu____20210 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20220 -> true
               | uu____20230 -> false) quals
      | uu____20232 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20242,uu____20243);
            FStar_Syntax_Syntax.sigrng = uu____20244;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20246;
            FStar_Syntax_Syntax.sigattrs = uu____20247;_},uu____20248),uu____20249)
        ->
        FStar_Util.for_some
          (fun uu___9_20306  ->
             match uu___9_20306 with
             | FStar_Syntax_Syntax.Action uu____20308 -> true
             | uu____20310 -> false) quals
    | uu____20312 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20326 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20326
  
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
      let uu____20343 =
        let uu____20344 = FStar_Syntax_Util.un_uinst head1  in
        uu____20344.FStar_Syntax_Syntax.n  in
      match uu____20343 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20350 ->
               true
           | uu____20353 -> false)
      | uu____20355 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20369 = lookup_qname env l  in
      match uu____20369 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20372),uu____20373) ->
          FStar_Util.for_some
            (fun uu___10_20421  ->
               match uu___10_20421 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20424 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20426 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20502 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20520) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20538 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20546 ->
                 FStar_Pervasives_Native.Some true
             | uu____20565 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20568 =
        let uu____20572 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20572 mapper  in
      match uu____20568 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20632 = lookup_qname env lid  in
      match uu____20632 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20636,uu____20637,tps,uu____20639,uu____20640,uu____20641);
              FStar_Syntax_Syntax.sigrng = uu____20642;
              FStar_Syntax_Syntax.sigquals = uu____20643;
              FStar_Syntax_Syntax.sigmeta = uu____20644;
              FStar_Syntax_Syntax.sigattrs = uu____20645;_},uu____20646),uu____20647)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20713 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20759  ->
              match uu____20759 with
              | (d,uu____20768) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20784 = effect_decl_opt env l  in
      match uu____20784 with
      | FStar_Pervasives_Native.None  ->
          let uu____20799 = name_not_found l  in
          let uu____20805 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20799 uu____20805
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20828  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20847  ->
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
        let uu____20879 = FStar_Ident.lid_equals l1 l2  in
        if uu____20879
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20890 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20890
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20901 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20954  ->
                        match uu____20954 with
                        | (m1,m2,uu____20968,uu____20969,uu____20970) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20901 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20987 =
                    let uu____20993 =
                      let uu____20995 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20997 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20995
                        uu____20997
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20993)
                     in
                  FStar_Errors.raise_error uu____20987 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21007,uu____21008,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21042 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21042
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
  'Auu____21062 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21062) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21091 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21117  ->
                match uu____21117 with
                | (d,uu____21124) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21091 with
      | FStar_Pervasives_Native.None  ->
          let uu____21135 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21135
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21150 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____21150 with
           | (uu____21165,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21183)::(wp,uu____21185)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21241 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          let uu____21299 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____21299
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____21304 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____21304
             then
               FStar_Syntax_Syntax.mk_GTotal' res_t
                 (FStar_Pervasives_Native.Some res_u)
             else
               (let eff_name1 = norm_eff_name env eff_name  in
                let ed = get_effect_decl env eff_name1  in
                let null_wp =
                  inst_effect_fun_with [res_u] env ed
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let null_wp_res =
                  let uu____21315 = get_range env  in
                  let uu____21316 =
                    let uu____21323 =
                      let uu____21324 =
                        let uu____21341 =
                          let uu____21352 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____21352]  in
                        (null_wp, uu____21341)  in
                      FStar_Syntax_Syntax.Tm_app uu____21324  in
                    FStar_Syntax_Syntax.mk uu____21323  in
                  uu____21316 FStar_Pervasives_Native.None uu____21315  in
                let uu____21389 =
                  let uu____21390 =
                    let uu____21401 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____21401]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____21390;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____21389))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1504_21439 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1504_21439.order);
              joins = (uu___1504_21439.joins)
            }  in
          let uu___1507_21448 = env  in
          {
            solver = (uu___1507_21448.solver);
            range = (uu___1507_21448.range);
            curmodule = (uu___1507_21448.curmodule);
            gamma = (uu___1507_21448.gamma);
            gamma_sig = (uu___1507_21448.gamma_sig);
            gamma_cache = (uu___1507_21448.gamma_cache);
            modules = (uu___1507_21448.modules);
            expected_typ = (uu___1507_21448.expected_typ);
            sigtab = (uu___1507_21448.sigtab);
            attrtab = (uu___1507_21448.attrtab);
            is_pattern = (uu___1507_21448.is_pattern);
            instantiate_imp = (uu___1507_21448.instantiate_imp);
            effects;
            generalize = (uu___1507_21448.generalize);
            letrecs = (uu___1507_21448.letrecs);
            top_level = (uu___1507_21448.top_level);
            check_uvars = (uu___1507_21448.check_uvars);
            use_eq = (uu___1507_21448.use_eq);
            is_iface = (uu___1507_21448.is_iface);
            admit = (uu___1507_21448.admit);
            lax = (uu___1507_21448.lax);
            lax_universes = (uu___1507_21448.lax_universes);
            phase1 = (uu___1507_21448.phase1);
            failhard = (uu___1507_21448.failhard);
            nosynth = (uu___1507_21448.nosynth);
            uvar_subtyping = (uu___1507_21448.uvar_subtyping);
            tc_term = (uu___1507_21448.tc_term);
            type_of = (uu___1507_21448.type_of);
            universe_of = (uu___1507_21448.universe_of);
            check_type_of = (uu___1507_21448.check_type_of);
            use_bv_sorts = (uu___1507_21448.use_bv_sorts);
            qtbl_name_and_index = (uu___1507_21448.qtbl_name_and_index);
            normalized_eff_names = (uu___1507_21448.normalized_eff_names);
            fv_delta_depths = (uu___1507_21448.fv_delta_depths);
            proof_ns = (uu___1507_21448.proof_ns);
            synth_hook = (uu___1507_21448.synth_hook);
            try_solve_implicits_hook =
              (uu___1507_21448.try_solve_implicits_hook);
            splice = (uu___1507_21448.splice);
            postprocess = (uu___1507_21448.postprocess);
            is_native_tactic = (uu___1507_21448.is_native_tactic);
            identifier_info = (uu___1507_21448.identifier_info);
            tc_hooks = (uu___1507_21448.tc_hooks);
            dsenv = (uu___1507_21448.dsenv);
            nbe = (uu___1507_21448.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____21478 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____21478  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____21636 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____21637 = l1 u t wp e  in
                                l2 u t uu____21636 uu____21637))
                | uu____21638 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21710 = inst_tscheme_with lift_t [u]  in
            match uu____21710 with
            | (uu____21717,lift_t1) ->
                let uu____21719 =
                  let uu____21726 =
                    let uu____21727 =
                      let uu____21744 =
                        let uu____21755 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21764 =
                          let uu____21775 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21775]  in
                        uu____21755 :: uu____21764  in
                      (lift_t1, uu____21744)  in
                    FStar_Syntax_Syntax.Tm_app uu____21727  in
                  FStar_Syntax_Syntax.mk uu____21726  in
                uu____21719 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____21885 = inst_tscheme_with lift_t [u]  in
            match uu____21885 with
            | (uu____21892,lift_t1) ->
                let uu____21894 =
                  let uu____21901 =
                    let uu____21902 =
                      let uu____21919 =
                        let uu____21930 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21939 =
                          let uu____21950 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21959 =
                            let uu____21970 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21970]  in
                          uu____21950 :: uu____21959  in
                        uu____21930 :: uu____21939  in
                      (lift_t1, uu____21919)  in
                    FStar_Syntax_Syntax.Tm_app uu____21902  in
                  FStar_Syntax_Syntax.mk uu____21901  in
                uu____21894 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____22072 =
                let uu____22073 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____22073
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____22072  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____22082 =
              let uu____22084 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____22084  in
            let uu____22085 =
              let uu____22087 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____22115 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____22115)
                 in
              FStar_Util.dflt "none" uu____22087  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22082
              uu____22085
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____22144  ->
                    match uu____22144 with
                    | (e,uu____22152) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____22175 =
            match uu____22175 with
            | (i,j) ->
                let uu____22186 = FStar_Ident.lid_equals i j  in
                if uu____22186
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _22193  -> FStar_Pervasives_Native.Some _22193)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____22222 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____22232 = FStar_Ident.lid_equals i k  in
                        if uu____22232
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____22246 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____22246
                                  then []
                                  else
                                    (let uu____22253 =
                                       let uu____22262 =
                                         find_edge order1 (i, k)  in
                                       let uu____22265 =
                                         find_edge order1 (k, j)  in
                                       (uu____22262, uu____22265)  in
                                     match uu____22253 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____22280 =
                                           compose_edges e1 e2  in
                                         [uu____22280]
                                     | uu____22281 -> [])))))
                 in
              FStar_List.append order1 uu____22222  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____22311 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____22314 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____22314
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____22311
                   then
                     let uu____22321 =
                       let uu____22327 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____22327)
                        in
                     let uu____22331 = get_range env  in
                     FStar_Errors.raise_error uu____22321 uu____22331
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____22409 = FStar_Ident.lid_equals i j
                                   in
                                if uu____22409
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____22461 =
                                              let uu____22470 =
                                                find_edge order2 (i, k)  in
                                              let uu____22473 =
                                                find_edge order2 (j, k)  in
                                              (uu____22470, uu____22473)  in
                                            match uu____22461 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____22515,uu____22516)
                                                     ->
                                                     let uu____22523 =
                                                       let uu____22530 =
                                                         let uu____22532 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22532
                                                          in
                                                       let uu____22535 =
                                                         let uu____22537 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22537
                                                          in
                                                       (uu____22530,
                                                         uu____22535)
                                                        in
                                                     (match uu____22523 with
                                                      | (true ,true ) ->
                                                          let uu____22554 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____22554
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
                                            | uu____22597 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1634_22670 = env.effects  in
              { decls = (uu___1634_22670.decls); order = order2; joins }  in
            let uu___1637_22671 = env  in
            {
              solver = (uu___1637_22671.solver);
              range = (uu___1637_22671.range);
              curmodule = (uu___1637_22671.curmodule);
              gamma = (uu___1637_22671.gamma);
              gamma_sig = (uu___1637_22671.gamma_sig);
              gamma_cache = (uu___1637_22671.gamma_cache);
              modules = (uu___1637_22671.modules);
              expected_typ = (uu___1637_22671.expected_typ);
              sigtab = (uu___1637_22671.sigtab);
              attrtab = (uu___1637_22671.attrtab);
              is_pattern = (uu___1637_22671.is_pattern);
              instantiate_imp = (uu___1637_22671.instantiate_imp);
              effects;
              generalize = (uu___1637_22671.generalize);
              letrecs = (uu___1637_22671.letrecs);
              top_level = (uu___1637_22671.top_level);
              check_uvars = (uu___1637_22671.check_uvars);
              use_eq = (uu___1637_22671.use_eq);
              is_iface = (uu___1637_22671.is_iface);
              admit = (uu___1637_22671.admit);
              lax = (uu___1637_22671.lax);
              lax_universes = (uu___1637_22671.lax_universes);
              phase1 = (uu___1637_22671.phase1);
              failhard = (uu___1637_22671.failhard);
              nosynth = (uu___1637_22671.nosynth);
              uvar_subtyping = (uu___1637_22671.uvar_subtyping);
              tc_term = (uu___1637_22671.tc_term);
              type_of = (uu___1637_22671.type_of);
              universe_of = (uu___1637_22671.universe_of);
              check_type_of = (uu___1637_22671.check_type_of);
              use_bv_sorts = (uu___1637_22671.use_bv_sorts);
              qtbl_name_and_index = (uu___1637_22671.qtbl_name_and_index);
              normalized_eff_names = (uu___1637_22671.normalized_eff_names);
              fv_delta_depths = (uu___1637_22671.fv_delta_depths);
              proof_ns = (uu___1637_22671.proof_ns);
              synth_hook = (uu___1637_22671.synth_hook);
              try_solve_implicits_hook =
                (uu___1637_22671.try_solve_implicits_hook);
              splice = (uu___1637_22671.splice);
              postprocess = (uu___1637_22671.postprocess);
              is_native_tactic = (uu___1637_22671.is_native_tactic);
              identifier_info = (uu___1637_22671.identifier_info);
              tc_hooks = (uu___1637_22671.tc_hooks);
              dsenv = (uu___1637_22671.dsenv);
              nbe = (uu___1637_22671.nbe)
            }))
      | uu____22672 -> env
  
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
        | uu____22701 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22714 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22714 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22731 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22731 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____22756 =
                     let uu____22762 =
                       let uu____22764 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22772 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22783 =
                         let uu____22785 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22785  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22764 uu____22772 uu____22783
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22762)
                      in
                   FStar_Errors.raise_error uu____22756
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22793 =
                     let uu____22804 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22804 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22841  ->
                        fun uu____22842  ->
                          match (uu____22841, uu____22842) with
                          | ((x,uu____22872),(t,uu____22874)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22793
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22905 =
                     let uu___1675_22906 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1675_22906.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1675_22906.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1675_22906.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1675_22906.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22905
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22918 .
    'Auu____22918 ->
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
          let uu____22948 = effect_decl_opt env effect_name  in
          match uu____22948 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22987 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____23010 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____23049 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____23049
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____23054 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____23054
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____23069 =
                     let uu____23072 = get_range env  in
                     let uu____23073 =
                       let uu____23080 =
                         let uu____23081 =
                           let uu____23098 =
                             let uu____23109 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23109; wp]  in
                           (repr, uu____23098)  in
                         FStar_Syntax_Syntax.Tm_app uu____23081  in
                       FStar_Syntax_Syntax.mk uu____23080  in
                     uu____23073 FStar_Pervasives_Native.None uu____23072  in
                   FStar_Pervasives_Native.Some uu____23069)
  
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
      | uu____23253 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23268 =
        let uu____23269 = FStar_Syntax_Subst.compress t  in
        uu____23269.FStar_Syntax_Syntax.n  in
      match uu____23268 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23273,c) ->
          is_reifiable_comp env c
      | uu____23295 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23315 =
           let uu____23317 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23317  in
         if uu____23315
         then
           let uu____23320 =
             let uu____23326 =
               let uu____23328 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23328
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23326)  in
           let uu____23332 = get_range env  in
           FStar_Errors.raise_error uu____23320 uu____23332
         else ());
        (let uu____23335 = effect_repr_aux true env c u_c  in
         match uu____23335 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1740_23371 = env  in
        {
          solver = (uu___1740_23371.solver);
          range = (uu___1740_23371.range);
          curmodule = (uu___1740_23371.curmodule);
          gamma = (uu___1740_23371.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1740_23371.gamma_cache);
          modules = (uu___1740_23371.modules);
          expected_typ = (uu___1740_23371.expected_typ);
          sigtab = (uu___1740_23371.sigtab);
          attrtab = (uu___1740_23371.attrtab);
          is_pattern = (uu___1740_23371.is_pattern);
          instantiate_imp = (uu___1740_23371.instantiate_imp);
          effects = (uu___1740_23371.effects);
          generalize = (uu___1740_23371.generalize);
          letrecs = (uu___1740_23371.letrecs);
          top_level = (uu___1740_23371.top_level);
          check_uvars = (uu___1740_23371.check_uvars);
          use_eq = (uu___1740_23371.use_eq);
          is_iface = (uu___1740_23371.is_iface);
          admit = (uu___1740_23371.admit);
          lax = (uu___1740_23371.lax);
          lax_universes = (uu___1740_23371.lax_universes);
          phase1 = (uu___1740_23371.phase1);
          failhard = (uu___1740_23371.failhard);
          nosynth = (uu___1740_23371.nosynth);
          uvar_subtyping = (uu___1740_23371.uvar_subtyping);
          tc_term = (uu___1740_23371.tc_term);
          type_of = (uu___1740_23371.type_of);
          universe_of = (uu___1740_23371.universe_of);
          check_type_of = (uu___1740_23371.check_type_of);
          use_bv_sorts = (uu___1740_23371.use_bv_sorts);
          qtbl_name_and_index = (uu___1740_23371.qtbl_name_and_index);
          normalized_eff_names = (uu___1740_23371.normalized_eff_names);
          fv_delta_depths = (uu___1740_23371.fv_delta_depths);
          proof_ns = (uu___1740_23371.proof_ns);
          synth_hook = (uu___1740_23371.synth_hook);
          try_solve_implicits_hook =
            (uu___1740_23371.try_solve_implicits_hook);
          splice = (uu___1740_23371.splice);
          postprocess = (uu___1740_23371.postprocess);
          is_native_tactic = (uu___1740_23371.is_native_tactic);
          identifier_info = (uu___1740_23371.identifier_info);
          tc_hooks = (uu___1740_23371.tc_hooks);
          dsenv = (uu___1740_23371.dsenv);
          nbe = (uu___1740_23371.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1747_23385 = env  in
      {
        solver = (uu___1747_23385.solver);
        range = (uu___1747_23385.range);
        curmodule = (uu___1747_23385.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1747_23385.gamma_sig);
        gamma_cache = (uu___1747_23385.gamma_cache);
        modules = (uu___1747_23385.modules);
        expected_typ = (uu___1747_23385.expected_typ);
        sigtab = (uu___1747_23385.sigtab);
        attrtab = (uu___1747_23385.attrtab);
        is_pattern = (uu___1747_23385.is_pattern);
        instantiate_imp = (uu___1747_23385.instantiate_imp);
        effects = (uu___1747_23385.effects);
        generalize = (uu___1747_23385.generalize);
        letrecs = (uu___1747_23385.letrecs);
        top_level = (uu___1747_23385.top_level);
        check_uvars = (uu___1747_23385.check_uvars);
        use_eq = (uu___1747_23385.use_eq);
        is_iface = (uu___1747_23385.is_iface);
        admit = (uu___1747_23385.admit);
        lax = (uu___1747_23385.lax);
        lax_universes = (uu___1747_23385.lax_universes);
        phase1 = (uu___1747_23385.phase1);
        failhard = (uu___1747_23385.failhard);
        nosynth = (uu___1747_23385.nosynth);
        uvar_subtyping = (uu___1747_23385.uvar_subtyping);
        tc_term = (uu___1747_23385.tc_term);
        type_of = (uu___1747_23385.type_of);
        universe_of = (uu___1747_23385.universe_of);
        check_type_of = (uu___1747_23385.check_type_of);
        use_bv_sorts = (uu___1747_23385.use_bv_sorts);
        qtbl_name_and_index = (uu___1747_23385.qtbl_name_and_index);
        normalized_eff_names = (uu___1747_23385.normalized_eff_names);
        fv_delta_depths = (uu___1747_23385.fv_delta_depths);
        proof_ns = (uu___1747_23385.proof_ns);
        synth_hook = (uu___1747_23385.synth_hook);
        try_solve_implicits_hook = (uu___1747_23385.try_solve_implicits_hook);
        splice = (uu___1747_23385.splice);
        postprocess = (uu___1747_23385.postprocess);
        is_native_tactic = (uu___1747_23385.is_native_tactic);
        identifier_info = (uu___1747_23385.identifier_info);
        tc_hooks = (uu___1747_23385.tc_hooks);
        dsenv = (uu___1747_23385.dsenv);
        nbe = (uu___1747_23385.nbe)
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
            (let uu___1760_23443 = env  in
             {
               solver = (uu___1760_23443.solver);
               range = (uu___1760_23443.range);
               curmodule = (uu___1760_23443.curmodule);
               gamma = rest;
               gamma_sig = (uu___1760_23443.gamma_sig);
               gamma_cache = (uu___1760_23443.gamma_cache);
               modules = (uu___1760_23443.modules);
               expected_typ = (uu___1760_23443.expected_typ);
               sigtab = (uu___1760_23443.sigtab);
               attrtab = (uu___1760_23443.attrtab);
               is_pattern = (uu___1760_23443.is_pattern);
               instantiate_imp = (uu___1760_23443.instantiate_imp);
               effects = (uu___1760_23443.effects);
               generalize = (uu___1760_23443.generalize);
               letrecs = (uu___1760_23443.letrecs);
               top_level = (uu___1760_23443.top_level);
               check_uvars = (uu___1760_23443.check_uvars);
               use_eq = (uu___1760_23443.use_eq);
               is_iface = (uu___1760_23443.is_iface);
               admit = (uu___1760_23443.admit);
               lax = (uu___1760_23443.lax);
               lax_universes = (uu___1760_23443.lax_universes);
               phase1 = (uu___1760_23443.phase1);
               failhard = (uu___1760_23443.failhard);
               nosynth = (uu___1760_23443.nosynth);
               uvar_subtyping = (uu___1760_23443.uvar_subtyping);
               tc_term = (uu___1760_23443.tc_term);
               type_of = (uu___1760_23443.type_of);
               universe_of = (uu___1760_23443.universe_of);
               check_type_of = (uu___1760_23443.check_type_of);
               use_bv_sorts = (uu___1760_23443.use_bv_sorts);
               qtbl_name_and_index = (uu___1760_23443.qtbl_name_and_index);
               normalized_eff_names = (uu___1760_23443.normalized_eff_names);
               fv_delta_depths = (uu___1760_23443.fv_delta_depths);
               proof_ns = (uu___1760_23443.proof_ns);
               synth_hook = (uu___1760_23443.synth_hook);
               try_solve_implicits_hook =
                 (uu___1760_23443.try_solve_implicits_hook);
               splice = (uu___1760_23443.splice);
               postprocess = (uu___1760_23443.postprocess);
               is_native_tactic = (uu___1760_23443.is_native_tactic);
               identifier_info = (uu___1760_23443.identifier_info);
               tc_hooks = (uu___1760_23443.tc_hooks);
               dsenv = (uu___1760_23443.dsenv);
               nbe = (uu___1760_23443.nbe)
             }))
    | uu____23444 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23473  ->
             match uu____23473 with | (x,uu____23481) -> push_bv env1 x) env
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
            let uu___1774_23516 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1774_23516.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1774_23516.FStar_Syntax_Syntax.index);
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
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___1785_23558 = env  in
       {
         solver = (uu___1785_23558.solver);
         range = (uu___1785_23558.range);
         curmodule = (uu___1785_23558.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1785_23558.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1785_23558.sigtab);
         attrtab = (uu___1785_23558.attrtab);
         is_pattern = (uu___1785_23558.is_pattern);
         instantiate_imp = (uu___1785_23558.instantiate_imp);
         effects = (uu___1785_23558.effects);
         generalize = (uu___1785_23558.generalize);
         letrecs = (uu___1785_23558.letrecs);
         top_level = (uu___1785_23558.top_level);
         check_uvars = (uu___1785_23558.check_uvars);
         use_eq = (uu___1785_23558.use_eq);
         is_iface = (uu___1785_23558.is_iface);
         admit = (uu___1785_23558.admit);
         lax = (uu___1785_23558.lax);
         lax_universes = (uu___1785_23558.lax_universes);
         phase1 = (uu___1785_23558.phase1);
         failhard = (uu___1785_23558.failhard);
         nosynth = (uu___1785_23558.nosynth);
         uvar_subtyping = (uu___1785_23558.uvar_subtyping);
         tc_term = (uu___1785_23558.tc_term);
         type_of = (uu___1785_23558.type_of);
         universe_of = (uu___1785_23558.universe_of);
         check_type_of = (uu___1785_23558.check_type_of);
         use_bv_sorts = (uu___1785_23558.use_bv_sorts);
         qtbl_name_and_index = (uu___1785_23558.qtbl_name_and_index);
         normalized_eff_names = (uu___1785_23558.normalized_eff_names);
         fv_delta_depths = (uu___1785_23558.fv_delta_depths);
         proof_ns = (uu___1785_23558.proof_ns);
         synth_hook = (uu___1785_23558.synth_hook);
         try_solve_implicits_hook =
           (uu___1785_23558.try_solve_implicits_hook);
         splice = (uu___1785_23558.splice);
         postprocess = (uu___1785_23558.postprocess);
         is_native_tactic = (uu___1785_23558.is_native_tactic);
         identifier_info = (uu___1785_23558.identifier_info);
         tc_hooks = (uu___1785_23558.tc_hooks);
         dsenv = (uu___1785_23558.dsenv);
         nbe = (uu___1785_23558.nbe)
       })
  
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
        let uu____23602 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23602 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23630 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23630)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1800_23646 = env  in
      {
        solver = (uu___1800_23646.solver);
        range = (uu___1800_23646.range);
        curmodule = (uu___1800_23646.curmodule);
        gamma = (uu___1800_23646.gamma);
        gamma_sig = (uu___1800_23646.gamma_sig);
        gamma_cache = (uu___1800_23646.gamma_cache);
        modules = (uu___1800_23646.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1800_23646.sigtab);
        attrtab = (uu___1800_23646.attrtab);
        is_pattern = (uu___1800_23646.is_pattern);
        instantiate_imp = (uu___1800_23646.instantiate_imp);
        effects = (uu___1800_23646.effects);
        generalize = (uu___1800_23646.generalize);
        letrecs = (uu___1800_23646.letrecs);
        top_level = (uu___1800_23646.top_level);
        check_uvars = (uu___1800_23646.check_uvars);
        use_eq = false;
        is_iface = (uu___1800_23646.is_iface);
        admit = (uu___1800_23646.admit);
        lax = (uu___1800_23646.lax);
        lax_universes = (uu___1800_23646.lax_universes);
        phase1 = (uu___1800_23646.phase1);
        failhard = (uu___1800_23646.failhard);
        nosynth = (uu___1800_23646.nosynth);
        uvar_subtyping = (uu___1800_23646.uvar_subtyping);
        tc_term = (uu___1800_23646.tc_term);
        type_of = (uu___1800_23646.type_of);
        universe_of = (uu___1800_23646.universe_of);
        check_type_of = (uu___1800_23646.check_type_of);
        use_bv_sorts = (uu___1800_23646.use_bv_sorts);
        qtbl_name_and_index = (uu___1800_23646.qtbl_name_and_index);
        normalized_eff_names = (uu___1800_23646.normalized_eff_names);
        fv_delta_depths = (uu___1800_23646.fv_delta_depths);
        proof_ns = (uu___1800_23646.proof_ns);
        synth_hook = (uu___1800_23646.synth_hook);
        try_solve_implicits_hook = (uu___1800_23646.try_solve_implicits_hook);
        splice = (uu___1800_23646.splice);
        postprocess = (uu___1800_23646.postprocess);
        is_native_tactic = (uu___1800_23646.is_native_tactic);
        identifier_info = (uu___1800_23646.identifier_info);
        tc_hooks = (uu___1800_23646.tc_hooks);
        dsenv = (uu___1800_23646.dsenv);
        nbe = (uu___1800_23646.nbe)
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
    let uu____23677 = expected_typ env_  in
    ((let uu___1807_23683 = env_  in
      {
        solver = (uu___1807_23683.solver);
        range = (uu___1807_23683.range);
        curmodule = (uu___1807_23683.curmodule);
        gamma = (uu___1807_23683.gamma);
        gamma_sig = (uu___1807_23683.gamma_sig);
        gamma_cache = (uu___1807_23683.gamma_cache);
        modules = (uu___1807_23683.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1807_23683.sigtab);
        attrtab = (uu___1807_23683.attrtab);
        is_pattern = (uu___1807_23683.is_pattern);
        instantiate_imp = (uu___1807_23683.instantiate_imp);
        effects = (uu___1807_23683.effects);
        generalize = (uu___1807_23683.generalize);
        letrecs = (uu___1807_23683.letrecs);
        top_level = (uu___1807_23683.top_level);
        check_uvars = (uu___1807_23683.check_uvars);
        use_eq = false;
        is_iface = (uu___1807_23683.is_iface);
        admit = (uu___1807_23683.admit);
        lax = (uu___1807_23683.lax);
        lax_universes = (uu___1807_23683.lax_universes);
        phase1 = (uu___1807_23683.phase1);
        failhard = (uu___1807_23683.failhard);
        nosynth = (uu___1807_23683.nosynth);
        uvar_subtyping = (uu___1807_23683.uvar_subtyping);
        tc_term = (uu___1807_23683.tc_term);
        type_of = (uu___1807_23683.type_of);
        universe_of = (uu___1807_23683.universe_of);
        check_type_of = (uu___1807_23683.check_type_of);
        use_bv_sorts = (uu___1807_23683.use_bv_sorts);
        qtbl_name_and_index = (uu___1807_23683.qtbl_name_and_index);
        normalized_eff_names = (uu___1807_23683.normalized_eff_names);
        fv_delta_depths = (uu___1807_23683.fv_delta_depths);
        proof_ns = (uu___1807_23683.proof_ns);
        synth_hook = (uu___1807_23683.synth_hook);
        try_solve_implicits_hook = (uu___1807_23683.try_solve_implicits_hook);
        splice = (uu___1807_23683.splice);
        postprocess = (uu___1807_23683.postprocess);
        is_native_tactic = (uu___1807_23683.is_native_tactic);
        identifier_info = (uu___1807_23683.identifier_info);
        tc_hooks = (uu___1807_23683.tc_hooks);
        dsenv = (uu___1807_23683.dsenv);
        nbe = (uu___1807_23683.nbe)
      }), uu____23677)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23695 =
      let uu____23698 = FStar_Ident.id_of_text ""  in [uu____23698]  in
    FStar_Ident.lid_of_ids uu____23695  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23705 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23705
        then
          let uu____23710 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23710 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1815_23738 = env  in
       {
         solver = (uu___1815_23738.solver);
         range = (uu___1815_23738.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1815_23738.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1815_23738.expected_typ);
         sigtab = (uu___1815_23738.sigtab);
         attrtab = (uu___1815_23738.attrtab);
         is_pattern = (uu___1815_23738.is_pattern);
         instantiate_imp = (uu___1815_23738.instantiate_imp);
         effects = (uu___1815_23738.effects);
         generalize = (uu___1815_23738.generalize);
         letrecs = (uu___1815_23738.letrecs);
         top_level = (uu___1815_23738.top_level);
         check_uvars = (uu___1815_23738.check_uvars);
         use_eq = (uu___1815_23738.use_eq);
         is_iface = (uu___1815_23738.is_iface);
         admit = (uu___1815_23738.admit);
         lax = (uu___1815_23738.lax);
         lax_universes = (uu___1815_23738.lax_universes);
         phase1 = (uu___1815_23738.phase1);
         failhard = (uu___1815_23738.failhard);
         nosynth = (uu___1815_23738.nosynth);
         uvar_subtyping = (uu___1815_23738.uvar_subtyping);
         tc_term = (uu___1815_23738.tc_term);
         type_of = (uu___1815_23738.type_of);
         universe_of = (uu___1815_23738.universe_of);
         check_type_of = (uu___1815_23738.check_type_of);
         use_bv_sorts = (uu___1815_23738.use_bv_sorts);
         qtbl_name_and_index = (uu___1815_23738.qtbl_name_and_index);
         normalized_eff_names = (uu___1815_23738.normalized_eff_names);
         fv_delta_depths = (uu___1815_23738.fv_delta_depths);
         proof_ns = (uu___1815_23738.proof_ns);
         synth_hook = (uu___1815_23738.synth_hook);
         try_solve_implicits_hook =
           (uu___1815_23738.try_solve_implicits_hook);
         splice = (uu___1815_23738.splice);
         postprocess = (uu___1815_23738.postprocess);
         is_native_tactic = (uu___1815_23738.is_native_tactic);
         identifier_info = (uu___1815_23738.identifier_info);
         tc_hooks = (uu___1815_23738.tc_hooks);
         dsenv = (uu___1815_23738.dsenv);
         nbe = (uu___1815_23738.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23790)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23794,(uu____23795,t)))::tl1
          ->
          let uu____23816 =
            let uu____23819 = FStar_Syntax_Free.uvars t  in
            ext out uu____23819  in
          aux uu____23816 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23822;
            FStar_Syntax_Syntax.index = uu____23823;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23831 =
            let uu____23834 = FStar_Syntax_Free.uvars t  in
            ext out uu____23834  in
          aux uu____23831 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23892)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23896,(uu____23897,t)))::tl1
          ->
          let uu____23918 =
            let uu____23921 = FStar_Syntax_Free.univs t  in
            ext out uu____23921  in
          aux uu____23918 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23924;
            FStar_Syntax_Syntax.index = uu____23925;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23933 =
            let uu____23936 = FStar_Syntax_Free.univs t  in
            ext out uu____23936  in
          aux uu____23933 tl1
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
          let uu____23998 = FStar_Util.set_add uname out  in
          aux uu____23998 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24001,(uu____24002,t)))::tl1
          ->
          let uu____24023 =
            let uu____24026 = FStar_Syntax_Free.univnames t  in
            ext out uu____24026  in
          aux uu____24023 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24029;
            FStar_Syntax_Syntax.index = uu____24030;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24038 =
            let uu____24041 = FStar_Syntax_Free.univnames t  in
            ext out uu____24041  in
          aux uu____24038 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24062  ->
            match uu___11_24062 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24066 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24079 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24090 =
      let uu____24099 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24099
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24090 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24147 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24160  ->
              match uu___12_24160 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24163 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24163
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24169) ->
                  let uu____24186 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24186))
       in
    FStar_All.pipe_right uu____24147 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24200  ->
    match uu___13_24200 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24206 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24206
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24229  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24284) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24317,uu____24318) -> false  in
      let uu____24332 =
        FStar_List.tryFind
          (fun uu____24354  ->
             match uu____24354 with | (p,uu____24365) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24332 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24384,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24414 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24414
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1958_24436 = e  in
        {
          solver = (uu___1958_24436.solver);
          range = (uu___1958_24436.range);
          curmodule = (uu___1958_24436.curmodule);
          gamma = (uu___1958_24436.gamma);
          gamma_sig = (uu___1958_24436.gamma_sig);
          gamma_cache = (uu___1958_24436.gamma_cache);
          modules = (uu___1958_24436.modules);
          expected_typ = (uu___1958_24436.expected_typ);
          sigtab = (uu___1958_24436.sigtab);
          attrtab = (uu___1958_24436.attrtab);
          is_pattern = (uu___1958_24436.is_pattern);
          instantiate_imp = (uu___1958_24436.instantiate_imp);
          effects = (uu___1958_24436.effects);
          generalize = (uu___1958_24436.generalize);
          letrecs = (uu___1958_24436.letrecs);
          top_level = (uu___1958_24436.top_level);
          check_uvars = (uu___1958_24436.check_uvars);
          use_eq = (uu___1958_24436.use_eq);
          is_iface = (uu___1958_24436.is_iface);
          admit = (uu___1958_24436.admit);
          lax = (uu___1958_24436.lax);
          lax_universes = (uu___1958_24436.lax_universes);
          phase1 = (uu___1958_24436.phase1);
          failhard = (uu___1958_24436.failhard);
          nosynth = (uu___1958_24436.nosynth);
          uvar_subtyping = (uu___1958_24436.uvar_subtyping);
          tc_term = (uu___1958_24436.tc_term);
          type_of = (uu___1958_24436.type_of);
          universe_of = (uu___1958_24436.universe_of);
          check_type_of = (uu___1958_24436.check_type_of);
          use_bv_sorts = (uu___1958_24436.use_bv_sorts);
          qtbl_name_and_index = (uu___1958_24436.qtbl_name_and_index);
          normalized_eff_names = (uu___1958_24436.normalized_eff_names);
          fv_delta_depths = (uu___1958_24436.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1958_24436.synth_hook);
          try_solve_implicits_hook =
            (uu___1958_24436.try_solve_implicits_hook);
          splice = (uu___1958_24436.splice);
          postprocess = (uu___1958_24436.postprocess);
          is_native_tactic = (uu___1958_24436.is_native_tactic);
          identifier_info = (uu___1958_24436.identifier_info);
          tc_hooks = (uu___1958_24436.tc_hooks);
          dsenv = (uu___1958_24436.dsenv);
          nbe = (uu___1958_24436.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1967_24484 = e  in
      {
        solver = (uu___1967_24484.solver);
        range = (uu___1967_24484.range);
        curmodule = (uu___1967_24484.curmodule);
        gamma = (uu___1967_24484.gamma);
        gamma_sig = (uu___1967_24484.gamma_sig);
        gamma_cache = (uu___1967_24484.gamma_cache);
        modules = (uu___1967_24484.modules);
        expected_typ = (uu___1967_24484.expected_typ);
        sigtab = (uu___1967_24484.sigtab);
        attrtab = (uu___1967_24484.attrtab);
        is_pattern = (uu___1967_24484.is_pattern);
        instantiate_imp = (uu___1967_24484.instantiate_imp);
        effects = (uu___1967_24484.effects);
        generalize = (uu___1967_24484.generalize);
        letrecs = (uu___1967_24484.letrecs);
        top_level = (uu___1967_24484.top_level);
        check_uvars = (uu___1967_24484.check_uvars);
        use_eq = (uu___1967_24484.use_eq);
        is_iface = (uu___1967_24484.is_iface);
        admit = (uu___1967_24484.admit);
        lax = (uu___1967_24484.lax);
        lax_universes = (uu___1967_24484.lax_universes);
        phase1 = (uu___1967_24484.phase1);
        failhard = (uu___1967_24484.failhard);
        nosynth = (uu___1967_24484.nosynth);
        uvar_subtyping = (uu___1967_24484.uvar_subtyping);
        tc_term = (uu___1967_24484.tc_term);
        type_of = (uu___1967_24484.type_of);
        universe_of = (uu___1967_24484.universe_of);
        check_type_of = (uu___1967_24484.check_type_of);
        use_bv_sorts = (uu___1967_24484.use_bv_sorts);
        qtbl_name_and_index = (uu___1967_24484.qtbl_name_and_index);
        normalized_eff_names = (uu___1967_24484.normalized_eff_names);
        fv_delta_depths = (uu___1967_24484.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1967_24484.synth_hook);
        try_solve_implicits_hook = (uu___1967_24484.try_solve_implicits_hook);
        splice = (uu___1967_24484.splice);
        postprocess = (uu___1967_24484.postprocess);
        is_native_tactic = (uu___1967_24484.is_native_tactic);
        identifier_info = (uu___1967_24484.identifier_info);
        tc_hooks = (uu___1967_24484.tc_hooks);
        dsenv = (uu___1967_24484.dsenv);
        nbe = (uu___1967_24484.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24500 = FStar_Syntax_Free.names t  in
      let uu____24503 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24500 uu____24503
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24526 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24526
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24536 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24536
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24557 =
      match uu____24557 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24577 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____24577)
       in
    let uu____24585 =
      let uu____24589 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24589 FStar_List.rev  in
    FStar_All.pipe_right uu____24585 (FStar_String.concat " ")
  
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
                  (let uu____24659 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24659 with
                   | FStar_Pervasives_Native.Some uu____24663 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24666 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24676;
        univ_ineqs = uu____24677; implicits = uu____24678;_} -> true
    | uu____24690 -> false
  
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
          let uu___2011_24721 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2011_24721.deferred);
            univ_ineqs = (uu___2011_24721.univ_ineqs);
            implicits = (uu___2011_24721.implicits)
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
          let uu____24760 = FStar_Options.defensive ()  in
          if uu____24760
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24766 =
              let uu____24768 =
                let uu____24770 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24770  in
              Prims.op_Negation uu____24768  in
            (if uu____24766
             then
               let uu____24777 =
                 let uu____24783 =
                   let uu____24785 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24787 =
                     let uu____24789 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24789
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24785 uu____24787
                    in
                 (FStar_Errors.Warning_Defensive, uu____24783)  in
               FStar_Errors.log_issue rng uu____24777
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
          let uu____24829 =
            let uu____24831 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24831  in
          if uu____24829
          then ()
          else
            (let uu____24836 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24836 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24862 =
            let uu____24864 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24864  in
          if uu____24862
          then ()
          else
            (let uu____24869 = bound_vars e  in
             def_check_closed_in rng msg uu____24869 t)
  
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
          let uu___2048_24908 = g  in
          let uu____24909 =
            let uu____24910 =
              let uu____24911 =
                let uu____24918 =
                  let uu____24919 =
                    let uu____24936 =
                      let uu____24947 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24947]  in
                    (f, uu____24936)  in
                  FStar_Syntax_Syntax.Tm_app uu____24919  in
                FStar_Syntax_Syntax.mk uu____24918  in
              uu____24911 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24984  -> FStar_TypeChecker_Common.NonTrivial _24984)
              uu____24910
             in
          {
            guard_f = uu____24909;
            deferred = (uu___2048_24908.deferred);
            univ_ineqs = (uu___2048_24908.univ_ineqs);
            implicits = (uu___2048_24908.implicits)
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
          let uu___2055_25002 = g  in
          let uu____25003 =
            let uu____25004 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25004  in
          {
            guard_f = uu____25003;
            deferred = (uu___2055_25002.deferred);
            univ_ineqs = (uu___2055_25002.univ_ineqs);
            implicits = (uu___2055_25002.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2060_25021 = g  in
          let uu____25022 =
            let uu____25023 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25023  in
          {
            guard_f = uu____25022;
            deferred = (uu___2060_25021.deferred);
            univ_ineqs = (uu___2060_25021.univ_ineqs);
            implicits = (uu___2060_25021.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2064_25025 = g  in
          let uu____25026 =
            let uu____25027 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25027  in
          {
            guard_f = uu____25026;
            deferred = (uu___2064_25025.deferred);
            univ_ineqs = (uu___2064_25025.univ_ineqs);
            implicits = (uu___2064_25025.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25034 ->
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
          let uu____25051 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25051
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25058 =
      let uu____25059 = FStar_Syntax_Util.unmeta t  in
      uu____25059.FStar_Syntax_Syntax.n  in
    match uu____25058 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25063 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____25106 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____25106;
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
                       let uu____25201 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25201
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2119_25208 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2119_25208.deferred);
              univ_ineqs = (uu___2119_25208.univ_ineqs);
              implicits = (uu___2119_25208.implicits)
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
               let uu____25242 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25242
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
            let uu___2134_25269 = g  in
            let uu____25270 =
              let uu____25271 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25271  in
            {
              guard_f = uu____25270;
              deferred = (uu___2134_25269.deferred);
              univ_ineqs = (uu___2134_25269.univ_ineqs);
              implicits = (uu___2134_25269.implicits)
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
              let uu____25329 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25329 with
              | FStar_Pervasives_Native.Some
                  (uu____25354::(tm,uu____25356)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25420 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25438 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25438;
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
                      let uu___2156_25470 = trivial_guard  in
                      {
                        guard_f = (uu___2156_25470.guard_f);
                        deferred = (uu___2156_25470.deferred);
                        univ_ineqs = (uu___2156_25470.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____25488  -> ());
    push = (fun uu____25490  -> ());
    pop = (fun uu____25493  -> ());
    snapshot =
      (fun uu____25496  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____25515  -> fun uu____25516  -> ());
    encode_sig = (fun uu____25531  -> fun uu____25532  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25538 =
             let uu____25545 = FStar_Options.peek ()  in (e, g, uu____25545)
              in
           [uu____25538]);
    solve = (fun uu____25561  -> fun uu____25562  -> fun uu____25563  -> ());
    finish = (fun uu____25570  -> ());
    refresh = (fun uu____25572  -> ())
  } 