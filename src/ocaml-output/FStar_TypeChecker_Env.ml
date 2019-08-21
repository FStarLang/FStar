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
type mlift =
  {
  mlift_t: FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option ;
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
let (__proj__Mkmlift__item__mlift_t :
  mlift -> FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_t
  
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_wp
  
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with | { mlift_t; mlift_wp; mlift_term;_} -> mlift_term
  
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
    Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap }
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> solver
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> range
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> curmodule
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> gamma
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> gamma_sig
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> gamma_cache
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> modules
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> expected_typ
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> sigtab
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> attrtab
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> is_pattern
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> instantiate_imp
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> effects
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> generalize
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> letrecs
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> top_level
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> check_uvars
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> use_eq
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> is_iface
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> admit1
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> lax1
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> lax_universes
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> phase1
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> failhard
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> nosynth
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> uvar_subtyping
  
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> tc_term
  
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> type_of
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> universe_of
  
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
        expected_typ; sigtab; attrtab; is_pattern; instantiate_imp; effects;
        generalize; letrecs; top_level; check_uvars; use_eq; is_iface;
        admit = admit1; lax = lax1; lax_universes; phase1; failhard; 
        nosynth; uvar_subtyping; tc_term; type_of; universe_of;
        check_type_of; use_bv_sorts; qtbl_name_and_index;
        normalized_eff_names; fv_delta_depths; proof_ns; synth_hook;
        try_solve_implicits_hook; splice = splice1; postprocess;
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> check_type_of
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> use_bv_sorts
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> qtbl_name_and_index
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> normalized_eff_names
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> fv_delta_depths
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> proof_ns
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> synth_hook
  
let (__proj__Mkenv__item__try_solve_implicits_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.implicits -> unit)
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> try_solve_implicits_hook
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> splice1
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> postprocess
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> is_native_tactic
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> identifier_info
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> tc_hooks
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> dsenv
  
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> nbe1
  
let (__proj__Mkenv__item__strict_args_tab :
  env -> Prims.int Prims.list FStar_Pervasives_Native.option FStar_Util.smap)
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
        is_native_tactic; identifier_info; tc_hooks; dsenv; nbe = nbe1;
        strict_args_tab;_} -> strict_args_tab
  
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
           (fun uu___0_12910  ->
              match uu___0_12910 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12913 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12913  in
                  let uu____12914 =
                    let uu____12915 = FStar_Syntax_Subst.compress y  in
                    uu____12915.FStar_Syntax_Syntax.n  in
                  (match uu____12914 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12919 =
                         let uu___314_12920 = y1  in
                         let uu____12921 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___314_12920.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___314_12920.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12921
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12919
                   | uu____12924 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___320_12938 = env  in
      let uu____12939 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___320_12938.solver);
        range = (uu___320_12938.range);
        curmodule = (uu___320_12938.curmodule);
        gamma = uu____12939;
        gamma_sig = (uu___320_12938.gamma_sig);
        gamma_cache = (uu___320_12938.gamma_cache);
        modules = (uu___320_12938.modules);
        expected_typ = (uu___320_12938.expected_typ);
        sigtab = (uu___320_12938.sigtab);
        attrtab = (uu___320_12938.attrtab);
        is_pattern = (uu___320_12938.is_pattern);
        instantiate_imp = (uu___320_12938.instantiate_imp);
        effects = (uu___320_12938.effects);
        generalize = (uu___320_12938.generalize);
        letrecs = (uu___320_12938.letrecs);
        top_level = (uu___320_12938.top_level);
        check_uvars = (uu___320_12938.check_uvars);
        use_eq = (uu___320_12938.use_eq);
        is_iface = (uu___320_12938.is_iface);
        admit = (uu___320_12938.admit);
        lax = (uu___320_12938.lax);
        lax_universes = (uu___320_12938.lax_universes);
        phase1 = (uu___320_12938.phase1);
        failhard = (uu___320_12938.failhard);
        nosynth = (uu___320_12938.nosynth);
        uvar_subtyping = (uu___320_12938.uvar_subtyping);
        tc_term = (uu___320_12938.tc_term);
        type_of = (uu___320_12938.type_of);
        universe_of = (uu___320_12938.universe_of);
        check_type_of = (uu___320_12938.check_type_of);
        use_bv_sorts = (uu___320_12938.use_bv_sorts);
        qtbl_name_and_index = (uu___320_12938.qtbl_name_and_index);
        normalized_eff_names = (uu___320_12938.normalized_eff_names);
        fv_delta_depths = (uu___320_12938.fv_delta_depths);
        proof_ns = (uu___320_12938.proof_ns);
        synth_hook = (uu___320_12938.synth_hook);
        try_solve_implicits_hook = (uu___320_12938.try_solve_implicits_hook);
        splice = (uu___320_12938.splice);
        postprocess = (uu___320_12938.postprocess);
        is_native_tactic = (uu___320_12938.is_native_tactic);
        identifier_info = (uu___320_12938.identifier_info);
        tc_hooks = (uu___320_12938.tc_hooks);
        dsenv = (uu___320_12938.dsenv);
        nbe = (uu___320_12938.nbe);
        strict_args_tab = (uu___320_12938.strict_args_tab)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12947  -> fun uu____12948  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___327_12970 = env  in
      {
        solver = (uu___327_12970.solver);
        range = (uu___327_12970.range);
        curmodule = (uu___327_12970.curmodule);
        gamma = (uu___327_12970.gamma);
        gamma_sig = (uu___327_12970.gamma_sig);
        gamma_cache = (uu___327_12970.gamma_cache);
        modules = (uu___327_12970.modules);
        expected_typ = (uu___327_12970.expected_typ);
        sigtab = (uu___327_12970.sigtab);
        attrtab = (uu___327_12970.attrtab);
        is_pattern = (uu___327_12970.is_pattern);
        instantiate_imp = (uu___327_12970.instantiate_imp);
        effects = (uu___327_12970.effects);
        generalize = (uu___327_12970.generalize);
        letrecs = (uu___327_12970.letrecs);
        top_level = (uu___327_12970.top_level);
        check_uvars = (uu___327_12970.check_uvars);
        use_eq = (uu___327_12970.use_eq);
        is_iface = (uu___327_12970.is_iface);
        admit = (uu___327_12970.admit);
        lax = (uu___327_12970.lax);
        lax_universes = (uu___327_12970.lax_universes);
        phase1 = (uu___327_12970.phase1);
        failhard = (uu___327_12970.failhard);
        nosynth = (uu___327_12970.nosynth);
        uvar_subtyping = (uu___327_12970.uvar_subtyping);
        tc_term = (uu___327_12970.tc_term);
        type_of = (uu___327_12970.type_of);
        universe_of = (uu___327_12970.universe_of);
        check_type_of = (uu___327_12970.check_type_of);
        use_bv_sorts = (uu___327_12970.use_bv_sorts);
        qtbl_name_and_index = (uu___327_12970.qtbl_name_and_index);
        normalized_eff_names = (uu___327_12970.normalized_eff_names);
        fv_delta_depths = (uu___327_12970.fv_delta_depths);
        proof_ns = (uu___327_12970.proof_ns);
        synth_hook = (uu___327_12970.synth_hook);
        try_solve_implicits_hook = (uu___327_12970.try_solve_implicits_hook);
        splice = (uu___327_12970.splice);
        postprocess = (uu___327_12970.postprocess);
        is_native_tactic = (uu___327_12970.is_native_tactic);
        identifier_info = (uu___327_12970.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___327_12970.dsenv);
        nbe = (uu___327_12970.nbe);
        strict_args_tab = (uu___327_12970.strict_args_tab)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___331_12982 = e  in
      let uu____12983 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___331_12982.solver);
        range = (uu___331_12982.range);
        curmodule = (uu___331_12982.curmodule);
        gamma = (uu___331_12982.gamma);
        gamma_sig = (uu___331_12982.gamma_sig);
        gamma_cache = (uu___331_12982.gamma_cache);
        modules = (uu___331_12982.modules);
        expected_typ = (uu___331_12982.expected_typ);
        sigtab = (uu___331_12982.sigtab);
        attrtab = (uu___331_12982.attrtab);
        is_pattern = (uu___331_12982.is_pattern);
        instantiate_imp = (uu___331_12982.instantiate_imp);
        effects = (uu___331_12982.effects);
        generalize = (uu___331_12982.generalize);
        letrecs = (uu___331_12982.letrecs);
        top_level = (uu___331_12982.top_level);
        check_uvars = (uu___331_12982.check_uvars);
        use_eq = (uu___331_12982.use_eq);
        is_iface = (uu___331_12982.is_iface);
        admit = (uu___331_12982.admit);
        lax = (uu___331_12982.lax);
        lax_universes = (uu___331_12982.lax_universes);
        phase1 = (uu___331_12982.phase1);
        failhard = (uu___331_12982.failhard);
        nosynth = (uu___331_12982.nosynth);
        uvar_subtyping = (uu___331_12982.uvar_subtyping);
        tc_term = (uu___331_12982.tc_term);
        type_of = (uu___331_12982.type_of);
        universe_of = (uu___331_12982.universe_of);
        check_type_of = (uu___331_12982.check_type_of);
        use_bv_sorts = (uu___331_12982.use_bv_sorts);
        qtbl_name_and_index = (uu___331_12982.qtbl_name_and_index);
        normalized_eff_names = (uu___331_12982.normalized_eff_names);
        fv_delta_depths = (uu___331_12982.fv_delta_depths);
        proof_ns = (uu___331_12982.proof_ns);
        synth_hook = (uu___331_12982.synth_hook);
        try_solve_implicits_hook = (uu___331_12982.try_solve_implicits_hook);
        splice = (uu___331_12982.splice);
        postprocess = (uu___331_12982.postprocess);
        is_native_tactic = (uu___331_12982.is_native_tactic);
        identifier_info = (uu___331_12982.identifier_info);
        tc_hooks = (uu___331_12982.tc_hooks);
        dsenv = uu____12983;
        nbe = (uu___331_12982.nbe);
        strict_args_tab = (uu___331_12982.strict_args_tab)
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
      | (NoDelta ,uu____13012) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____13015,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____13017,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____13020 -> false
  
let (default_table_size : Prims.int) = (Prims.of_int (200)) 
let new_sigtab : 'Auu____13034 . unit -> 'Auu____13034 FStar_Util.smap =
  fun uu____13041  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____13047 . unit -> 'Auu____13047 FStar_Util.smap =
  fun uu____13054  -> FStar_Util.smap_create (Prims.of_int (100)) 
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
                  let uu____13192 = new_gamma_cache ()  in
                  let uu____13195 = new_sigtab ()  in
                  let uu____13198 = new_sigtab ()  in
                  let uu____13205 =
                    let uu____13220 =
                      FStar_Util.smap_create (Prims.of_int (10))  in
                    (uu____13220, FStar_Pervasives_Native.None)  in
                  let uu____13241 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  let uu____13245 =
                    FStar_Util.smap_create (Prims.of_int (50))  in
                  let uu____13249 = FStar_Options.using_facts_from ()  in
                  let uu____13250 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____13253 = FStar_Syntax_DsEnv.empty_env deps  in
                  let uu____13254 =
                    FStar_Util.smap_create (Prims.of_int (20))  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____13192;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____13195;
                    attrtab = uu____13198;
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
                    qtbl_name_and_index = uu____13205;
                    normalized_eff_names = uu____13241;
                    fv_delta_depths = uu____13245;
                    proof_ns = uu____13249;
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
                    is_native_tactic = (fun uu____13336  -> false);
                    identifier_info = uu____13250;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____13253;
                    nbe = nbe1;
                    strict_args_tab = uu____13254
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
  fun uu____13415  ->
    let uu____13416 = FStar_ST.op_Bang query_indices  in
    match uu____13416 with
    | [] -> failwith "Empty query indices!"
    | uu____13471 ->
        let uu____13481 =
          let uu____13491 =
            let uu____13499 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____13499  in
          let uu____13553 = FStar_ST.op_Bang query_indices  in uu____13491 ::
            uu____13553
           in
        FStar_ST.op_Colon_Equals query_indices uu____13481
  
let (pop_query_indices : unit -> unit) =
  fun uu____13649  ->
    let uu____13650 = FStar_ST.op_Bang query_indices  in
    match uu____13650 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____13777  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____13814  ->
    match uu____13814 with
    | (l,n1) ->
        let uu____13824 = FStar_ST.op_Bang query_indices  in
        (match uu____13824 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13946 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13969  ->
    let uu____13970 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13970
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____14038 =
       let uu____14041 = FStar_ST.op_Bang stack  in env :: uu____14041  in
     FStar_ST.op_Colon_Equals stack uu____14038);
    (let uu___402_14090 = env  in
     let uu____14091 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____14094 = FStar_Util.smap_copy (sigtab env)  in
     let uu____14097 = FStar_Util.smap_copy (attrtab env)  in
     let uu____14104 =
       let uu____14119 =
         let uu____14123 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____14123  in
       let uu____14155 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____14119, uu____14155)  in
     let uu____14204 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____14207 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____14210 =
       let uu____14213 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____14213  in
     let uu____14233 = FStar_Util.smap_copy env.strict_args_tab  in
     {
       solver = (uu___402_14090.solver);
       range = (uu___402_14090.range);
       curmodule = (uu___402_14090.curmodule);
       gamma = (uu___402_14090.gamma);
       gamma_sig = (uu___402_14090.gamma_sig);
       gamma_cache = uu____14091;
       modules = (uu___402_14090.modules);
       expected_typ = (uu___402_14090.expected_typ);
       sigtab = uu____14094;
       attrtab = uu____14097;
       is_pattern = (uu___402_14090.is_pattern);
       instantiate_imp = (uu___402_14090.instantiate_imp);
       effects = (uu___402_14090.effects);
       generalize = (uu___402_14090.generalize);
       letrecs = (uu___402_14090.letrecs);
       top_level = (uu___402_14090.top_level);
       check_uvars = (uu___402_14090.check_uvars);
       use_eq = (uu___402_14090.use_eq);
       is_iface = (uu___402_14090.is_iface);
       admit = (uu___402_14090.admit);
       lax = (uu___402_14090.lax);
       lax_universes = (uu___402_14090.lax_universes);
       phase1 = (uu___402_14090.phase1);
       failhard = (uu___402_14090.failhard);
       nosynth = (uu___402_14090.nosynth);
       uvar_subtyping = (uu___402_14090.uvar_subtyping);
       tc_term = (uu___402_14090.tc_term);
       type_of = (uu___402_14090.type_of);
       universe_of = (uu___402_14090.universe_of);
       check_type_of = (uu___402_14090.check_type_of);
       use_bv_sorts = (uu___402_14090.use_bv_sorts);
       qtbl_name_and_index = uu____14104;
       normalized_eff_names = uu____14204;
       fv_delta_depths = uu____14207;
       proof_ns = (uu___402_14090.proof_ns);
       synth_hook = (uu___402_14090.synth_hook);
       try_solve_implicits_hook = (uu___402_14090.try_solve_implicits_hook);
       splice = (uu___402_14090.splice);
       postprocess = (uu___402_14090.postprocess);
       is_native_tactic = (uu___402_14090.is_native_tactic);
       identifier_info = uu____14210;
       tc_hooks = (uu___402_14090.tc_hooks);
       dsenv = (uu___402_14090.dsenv);
       nbe = (uu___402_14090.nbe);
       strict_args_tab = uu____14233
     })
  
let (pop_stack : unit -> env) =
  fun uu____14251  ->
    let uu____14252 = FStar_ST.op_Bang stack  in
    match uu____14252 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____14306 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____14396  ->
           let uu____14397 = snapshot_stack env  in
           match uu____14397 with
           | (stack_depth,env1) ->
               let uu____14431 = snapshot_query_indices ()  in
               (match uu____14431 with
                | (query_indices_depth,()) ->
                    let uu____14464 = (env1.solver).snapshot msg  in
                    (match uu____14464 with
                     | (solver_depth,()) ->
                         let uu____14521 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____14521 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___427_14588 = env1  in
                                 {
                                   solver = (uu___427_14588.solver);
                                   range = (uu___427_14588.range);
                                   curmodule = (uu___427_14588.curmodule);
                                   gamma = (uu___427_14588.gamma);
                                   gamma_sig = (uu___427_14588.gamma_sig);
                                   gamma_cache = (uu___427_14588.gamma_cache);
                                   modules = (uu___427_14588.modules);
                                   expected_typ =
                                     (uu___427_14588.expected_typ);
                                   sigtab = (uu___427_14588.sigtab);
                                   attrtab = (uu___427_14588.attrtab);
                                   is_pattern = (uu___427_14588.is_pattern);
                                   instantiate_imp =
                                     (uu___427_14588.instantiate_imp);
                                   effects = (uu___427_14588.effects);
                                   generalize = (uu___427_14588.generalize);
                                   letrecs = (uu___427_14588.letrecs);
                                   top_level = (uu___427_14588.top_level);
                                   check_uvars = (uu___427_14588.check_uvars);
                                   use_eq = (uu___427_14588.use_eq);
                                   is_iface = (uu___427_14588.is_iface);
                                   admit = (uu___427_14588.admit);
                                   lax = (uu___427_14588.lax);
                                   lax_universes =
                                     (uu___427_14588.lax_universes);
                                   phase1 = (uu___427_14588.phase1);
                                   failhard = (uu___427_14588.failhard);
                                   nosynth = (uu___427_14588.nosynth);
                                   uvar_subtyping =
                                     (uu___427_14588.uvar_subtyping);
                                   tc_term = (uu___427_14588.tc_term);
                                   type_of = (uu___427_14588.type_of);
                                   universe_of = (uu___427_14588.universe_of);
                                   check_type_of =
                                     (uu___427_14588.check_type_of);
                                   use_bv_sorts =
                                     (uu___427_14588.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___427_14588.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___427_14588.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___427_14588.fv_delta_depths);
                                   proof_ns = (uu___427_14588.proof_ns);
                                   synth_hook = (uu___427_14588.synth_hook);
                                   try_solve_implicits_hook =
                                     (uu___427_14588.try_solve_implicits_hook);
                                   splice = (uu___427_14588.splice);
                                   postprocess = (uu___427_14588.postprocess);
                                   is_native_tactic =
                                     (uu___427_14588.is_native_tactic);
                                   identifier_info =
                                     (uu___427_14588.identifier_info);
                                   tc_hooks = (uu___427_14588.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___427_14588.nbe);
                                   strict_args_tab =
                                     (uu___427_14588.strict_args_tab)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____14622  ->
             let uu____14623 =
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
             match uu____14623 with
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
                             ((let uu____14803 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____14803
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____14819 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____14819
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14851,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14893 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14923  ->
                  match uu____14923 with
                  | (m,uu____14931) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14893 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___472_14946 = env  in
               {
                 solver = (uu___472_14946.solver);
                 range = (uu___472_14946.range);
                 curmodule = (uu___472_14946.curmodule);
                 gamma = (uu___472_14946.gamma);
                 gamma_sig = (uu___472_14946.gamma_sig);
                 gamma_cache = (uu___472_14946.gamma_cache);
                 modules = (uu___472_14946.modules);
                 expected_typ = (uu___472_14946.expected_typ);
                 sigtab = (uu___472_14946.sigtab);
                 attrtab = (uu___472_14946.attrtab);
                 is_pattern = (uu___472_14946.is_pattern);
                 instantiate_imp = (uu___472_14946.instantiate_imp);
                 effects = (uu___472_14946.effects);
                 generalize = (uu___472_14946.generalize);
                 letrecs = (uu___472_14946.letrecs);
                 top_level = (uu___472_14946.top_level);
                 check_uvars = (uu___472_14946.check_uvars);
                 use_eq = (uu___472_14946.use_eq);
                 is_iface = (uu___472_14946.is_iface);
                 admit = (uu___472_14946.admit);
                 lax = (uu___472_14946.lax);
                 lax_universes = (uu___472_14946.lax_universes);
                 phase1 = (uu___472_14946.phase1);
                 failhard = (uu___472_14946.failhard);
                 nosynth = (uu___472_14946.nosynth);
                 uvar_subtyping = (uu___472_14946.uvar_subtyping);
                 tc_term = (uu___472_14946.tc_term);
                 type_of = (uu___472_14946.type_of);
                 universe_of = (uu___472_14946.universe_of);
                 check_type_of = (uu___472_14946.check_type_of);
                 use_bv_sorts = (uu___472_14946.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___472_14946.normalized_eff_names);
                 fv_delta_depths = (uu___472_14946.fv_delta_depths);
                 proof_ns = (uu___472_14946.proof_ns);
                 synth_hook = (uu___472_14946.synth_hook);
                 try_solve_implicits_hook =
                   (uu___472_14946.try_solve_implicits_hook);
                 splice = (uu___472_14946.splice);
                 postprocess = (uu___472_14946.postprocess);
                 is_native_tactic = (uu___472_14946.is_native_tactic);
                 identifier_info = (uu___472_14946.identifier_info);
                 tc_hooks = (uu___472_14946.tc_hooks);
                 dsenv = (uu___472_14946.dsenv);
                 nbe = (uu___472_14946.nbe);
                 strict_args_tab = (uu___472_14946.strict_args_tab)
               }))
         | FStar_Pervasives_Native.Some (uu____14963,m) ->
             let next = m + Prims.int_one  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___481_14979 = env  in
               {
                 solver = (uu___481_14979.solver);
                 range = (uu___481_14979.range);
                 curmodule = (uu___481_14979.curmodule);
                 gamma = (uu___481_14979.gamma);
                 gamma_sig = (uu___481_14979.gamma_sig);
                 gamma_cache = (uu___481_14979.gamma_cache);
                 modules = (uu___481_14979.modules);
                 expected_typ = (uu___481_14979.expected_typ);
                 sigtab = (uu___481_14979.sigtab);
                 attrtab = (uu___481_14979.attrtab);
                 is_pattern = (uu___481_14979.is_pattern);
                 instantiate_imp = (uu___481_14979.instantiate_imp);
                 effects = (uu___481_14979.effects);
                 generalize = (uu___481_14979.generalize);
                 letrecs = (uu___481_14979.letrecs);
                 top_level = (uu___481_14979.top_level);
                 check_uvars = (uu___481_14979.check_uvars);
                 use_eq = (uu___481_14979.use_eq);
                 is_iface = (uu___481_14979.is_iface);
                 admit = (uu___481_14979.admit);
                 lax = (uu___481_14979.lax);
                 lax_universes = (uu___481_14979.lax_universes);
                 phase1 = (uu___481_14979.phase1);
                 failhard = (uu___481_14979.failhard);
                 nosynth = (uu___481_14979.nosynth);
                 uvar_subtyping = (uu___481_14979.uvar_subtyping);
                 tc_term = (uu___481_14979.tc_term);
                 type_of = (uu___481_14979.type_of);
                 universe_of = (uu___481_14979.universe_of);
                 check_type_of = (uu___481_14979.check_type_of);
                 use_bv_sorts = (uu___481_14979.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___481_14979.normalized_eff_names);
                 fv_delta_depths = (uu___481_14979.fv_delta_depths);
                 proof_ns = (uu___481_14979.proof_ns);
                 synth_hook = (uu___481_14979.synth_hook);
                 try_solve_implicits_hook =
                   (uu___481_14979.try_solve_implicits_hook);
                 splice = (uu___481_14979.splice);
                 postprocess = (uu___481_14979.postprocess);
                 is_native_tactic = (uu___481_14979.is_native_tactic);
                 identifier_info = (uu___481_14979.identifier_info);
                 tc_hooks = (uu___481_14979.tc_hooks);
                 dsenv = (uu___481_14979.dsenv);
                 nbe = (uu___481_14979.nbe);
                 strict_args_tab = (uu___481_14979.strict_args_tab)
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
        (let uu___488_15022 = e  in
         {
           solver = (uu___488_15022.solver);
           range = r;
           curmodule = (uu___488_15022.curmodule);
           gamma = (uu___488_15022.gamma);
           gamma_sig = (uu___488_15022.gamma_sig);
           gamma_cache = (uu___488_15022.gamma_cache);
           modules = (uu___488_15022.modules);
           expected_typ = (uu___488_15022.expected_typ);
           sigtab = (uu___488_15022.sigtab);
           attrtab = (uu___488_15022.attrtab);
           is_pattern = (uu___488_15022.is_pattern);
           instantiate_imp = (uu___488_15022.instantiate_imp);
           effects = (uu___488_15022.effects);
           generalize = (uu___488_15022.generalize);
           letrecs = (uu___488_15022.letrecs);
           top_level = (uu___488_15022.top_level);
           check_uvars = (uu___488_15022.check_uvars);
           use_eq = (uu___488_15022.use_eq);
           is_iface = (uu___488_15022.is_iface);
           admit = (uu___488_15022.admit);
           lax = (uu___488_15022.lax);
           lax_universes = (uu___488_15022.lax_universes);
           phase1 = (uu___488_15022.phase1);
           failhard = (uu___488_15022.failhard);
           nosynth = (uu___488_15022.nosynth);
           uvar_subtyping = (uu___488_15022.uvar_subtyping);
           tc_term = (uu___488_15022.tc_term);
           type_of = (uu___488_15022.type_of);
           universe_of = (uu___488_15022.universe_of);
           check_type_of = (uu___488_15022.check_type_of);
           use_bv_sorts = (uu___488_15022.use_bv_sorts);
           qtbl_name_and_index = (uu___488_15022.qtbl_name_and_index);
           normalized_eff_names = (uu___488_15022.normalized_eff_names);
           fv_delta_depths = (uu___488_15022.fv_delta_depths);
           proof_ns = (uu___488_15022.proof_ns);
           synth_hook = (uu___488_15022.synth_hook);
           try_solve_implicits_hook =
             (uu___488_15022.try_solve_implicits_hook);
           splice = (uu___488_15022.splice);
           postprocess = (uu___488_15022.postprocess);
           is_native_tactic = (uu___488_15022.is_native_tactic);
           identifier_info = (uu___488_15022.identifier_info);
           tc_hooks = (uu___488_15022.tc_hooks);
           dsenv = (uu___488_15022.dsenv);
           nbe = (uu___488_15022.nbe);
           strict_args_tab = (uu___488_15022.strict_args_tab)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____15042 =
        let uu____15043 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____15043 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15042
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____15098 =
          let uu____15099 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____15099 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15098
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____15154 =
          let uu____15155 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____15155 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____15154
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____15210 =
        let uu____15211 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____15211 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____15210
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___505_15275 = env  in
      {
        solver = (uu___505_15275.solver);
        range = (uu___505_15275.range);
        curmodule = lid;
        gamma = (uu___505_15275.gamma);
        gamma_sig = (uu___505_15275.gamma_sig);
        gamma_cache = (uu___505_15275.gamma_cache);
        modules = (uu___505_15275.modules);
        expected_typ = (uu___505_15275.expected_typ);
        sigtab = (uu___505_15275.sigtab);
        attrtab = (uu___505_15275.attrtab);
        is_pattern = (uu___505_15275.is_pattern);
        instantiate_imp = (uu___505_15275.instantiate_imp);
        effects = (uu___505_15275.effects);
        generalize = (uu___505_15275.generalize);
        letrecs = (uu___505_15275.letrecs);
        top_level = (uu___505_15275.top_level);
        check_uvars = (uu___505_15275.check_uvars);
        use_eq = (uu___505_15275.use_eq);
        is_iface = (uu___505_15275.is_iface);
        admit = (uu___505_15275.admit);
        lax = (uu___505_15275.lax);
        lax_universes = (uu___505_15275.lax_universes);
        phase1 = (uu___505_15275.phase1);
        failhard = (uu___505_15275.failhard);
        nosynth = (uu___505_15275.nosynth);
        uvar_subtyping = (uu___505_15275.uvar_subtyping);
        tc_term = (uu___505_15275.tc_term);
        type_of = (uu___505_15275.type_of);
        universe_of = (uu___505_15275.universe_of);
        check_type_of = (uu___505_15275.check_type_of);
        use_bv_sorts = (uu___505_15275.use_bv_sorts);
        qtbl_name_and_index = (uu___505_15275.qtbl_name_and_index);
        normalized_eff_names = (uu___505_15275.normalized_eff_names);
        fv_delta_depths = (uu___505_15275.fv_delta_depths);
        proof_ns = (uu___505_15275.proof_ns);
        synth_hook = (uu___505_15275.synth_hook);
        try_solve_implicits_hook = (uu___505_15275.try_solve_implicits_hook);
        splice = (uu___505_15275.splice);
        postprocess = (uu___505_15275.postprocess);
        is_native_tactic = (uu___505_15275.is_native_tactic);
        identifier_info = (uu___505_15275.identifier_info);
        tc_hooks = (uu___505_15275.tc_hooks);
        dsenv = (uu___505_15275.dsenv);
        nbe = (uu___505_15275.nbe);
        strict_args_tab = (uu___505_15275.strict_args_tab)
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
      let uu____15306 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____15306
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____15319 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____15319)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____15334 =
      let uu____15336 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____15336  in
    (FStar_Errors.Fatal_VariableNotFound, uu____15334)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____15345  ->
    let uu____15346 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____15346
  
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
      | ((formals,t),uu____15446) ->
          let vs = mk_univ_subst formals us  in
          let uu____15470 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____15470)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___1_15487  ->
    match uu___1_15487 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____15513  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____15533 = inst_tscheme t  in
      match uu____15533 with
      | (us,t1) ->
          let uu____15544 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____15544)
  
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
          let uu____15569 =
            FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname  in
          let uu____15571 =
            FStar_Syntax_Print.binders_to_string ", "
              ed.FStar_Syntax_Syntax.binders
             in
          FStar_Util.format2
            "Effect template %s should be applied to arguments for its binders (%s) before it can be used at an effect position"
            uu____15569 uu____15571
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
        fun uu____15598  ->
          match uu____15598 with
          | (us,t) ->
              (check_effect_is_not_a_template ed env.range;
               if (FStar_List.length insts) <> (FStar_List.length us)
               then
                 (let uu____15612 =
                    let uu____15614 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length us)
                       in
                    let uu____15618 =
                      FStar_All.pipe_left FStar_Util.string_of_int
                        (FStar_List.length insts)
                       in
                    let uu____15622 =
                      FStar_Syntax_Print.lid_to_string
                        ed.FStar_Syntax_Syntax.mname
                       in
                    let uu____15624 = FStar_Syntax_Print.term_to_string t  in
                    FStar_Util.format4
                      "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                      uu____15614 uu____15618 uu____15622 uu____15624
                     in
                  failwith uu____15612)
               else ();
               (let uu____15629 = inst_tscheme_with (us, t) insts  in
                FStar_Pervasives_Native.snd uu____15629))
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____15647 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____15658 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____15669 -> false
  
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
             | ([],uu____15717) -> Maybe
             | (uu____15724,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____15744 -> No  in
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
          let uu____15838 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____15838 with
          | FStar_Pervasives_Native.None  ->
              let uu____15861 =
                FStar_Util.find_map env.gamma
                  (fun uu___2_15905  ->
                     match uu___2_15905 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15944 = FStar_Ident.lid_equals lid l  in
                         if uu____15944
                         then
                           let uu____15967 =
                             let uu____15986 =
                               let uu____16001 = inst_tscheme t  in
                               FStar_Util.Inl uu____16001  in
                             let uu____16016 = FStar_Ident.range_of_lid l  in
                             (uu____15986, uu____16016)  in
                           FStar_Pervasives_Native.Some uu____15967
                         else FStar_Pervasives_Native.None
                     | uu____16069 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15861
                (fun uu____16107  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___3_16116  ->
                        match uu___3_16116 with
                        | (uu____16119,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____16121);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____16122;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____16123;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____16124;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____16125;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____16145 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____16145
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
                                  uu____16197 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____16204 -> cache t  in
                            let uu____16205 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____16205 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____16211 =
                                   let uu____16212 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____16212)
                                    in
                                 maybe_cache uu____16211)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____16283 = find_in_sigtab env lid  in
         match uu____16283 with
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
      let uu____16364 = lookup_qname env lid  in
      match uu____16364 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____16385,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____16499 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____16499 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____16544 =
          let uu____16547 = lookup_attr env1 attr  in se1 :: uu____16547  in
        FStar_Util.smap_add (attrtab env1) attr uu____16544  in
      FStar_List.iter
        (fun attr  ->
           let uu____16557 =
             let uu____16558 = FStar_Syntax_Subst.compress attr  in
             uu____16558.FStar_Syntax_Syntax.n  in
           match uu____16557 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____16562 =
                 let uu____16564 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____16564.FStar_Ident.str  in
               add_one1 env se uu____16562
           | uu____16565 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____16588) ->
          add_sigelts env ses
      | uu____16597 ->
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
            | uu____16612 -> ()))

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
        (fun uu___4_16644  ->
           match uu___4_16644 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____16662 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____16724,lb::[]),uu____16726) ->
            let uu____16735 =
              let uu____16744 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____16753 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____16744, uu____16753)  in
            FStar_Pervasives_Native.Some uu____16735
        | FStar_Syntax_Syntax.Sig_let ((uu____16766,lbs),uu____16768) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____16800 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____16813 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____16813
                     then
                       let uu____16826 =
                         let uu____16835 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16844 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____16835, uu____16844)  in
                       FStar_Pervasives_Native.Some uu____16826
                     else FStar_Pervasives_Native.None)
        | uu____16867 -> FStar_Pervasives_Native.None
  
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
                    let uu____16959 =
                      let uu____16961 =
                        let uu____16963 =
                          let uu____16965 =
                            let uu____16967 =
                              FStar_Util.string_of_int
                                (FStar_List.length
                                   (FStar_Pervasives_Native.fst
                                      ne.FStar_Syntax_Syntax.signature))
                               in
                            let uu____16973 =
                              let uu____16975 =
                                FStar_Util.string_of_int
                                  (FStar_List.length us)
                                 in
                              Prims.op_Hat ", got " uu____16975  in
                            Prims.op_Hat uu____16967 uu____16973  in
                          Prims.op_Hat ", expected " uu____16965  in
                        Prims.op_Hat
                          (ne.FStar_Syntax_Syntax.mname).FStar_Ident.str
                          uu____16963
                         in
                      Prims.op_Hat
                        "effect_signature: incorrect number of universes for the signature of "
                        uu____16961
                       in
                    failwith uu____16959
                  else ());
             (let uu____16982 =
                let uu____16991 =
                  inst_ts us_opt ne.FStar_Syntax_Syntax.signature  in
                (uu____16991, (se.FStar_Syntax_Syntax.sigrng))  in
              FStar_Pervasives_Native.Some uu____16982))
        | FStar_Syntax_Syntax.Sig_effect_abbrev
            (lid,us,binders,uu____17011,uu____17012) ->
            let uu____17017 =
              let uu____17026 =
                let uu____17031 =
                  let uu____17032 =
                    let uu____17035 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff
                       in
                    FStar_Syntax_Util.arrow binders uu____17035  in
                  (us, uu____17032)  in
                inst_ts us_opt uu____17031  in
              (uu____17026, (se.FStar_Syntax_Syntax.sigrng))  in
            FStar_Pervasives_Native.Some uu____17017
        | uu____17054 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____17143 =
          match uu____17143 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____17239,uvs,t,uu____17242,uu____17243,uu____17244);
                      FStar_Syntax_Syntax.sigrng = uu____17245;
                      FStar_Syntax_Syntax.sigquals = uu____17246;
                      FStar_Syntax_Syntax.sigmeta = uu____17247;
                      FStar_Syntax_Syntax.sigattrs = uu____17248;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17271 =
                     let uu____17280 = inst_tscheme1 (uvs, t)  in
                     (uu____17280, rng)  in
                   FStar_Pervasives_Native.Some uu____17271
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____17304;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____17306;
                      FStar_Syntax_Syntax.sigattrs = uu____17307;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____17324 =
                     let uu____17326 = in_cur_mod env l  in uu____17326 = Yes
                      in
                   if uu____17324
                   then
                     let uu____17338 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____17338
                      then
                        let uu____17354 =
                          let uu____17363 = inst_tscheme1 (uvs, t)  in
                          (uu____17363, rng)  in
                        FStar_Pervasives_Native.Some uu____17354
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____17396 =
                        let uu____17405 = inst_tscheme1 (uvs, t)  in
                        (uu____17405, rng)  in
                      FStar_Pervasives_Native.Some uu____17396)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17430,uu____17431);
                      FStar_Syntax_Syntax.sigrng = uu____17432;
                      FStar_Syntax_Syntax.sigquals = uu____17433;
                      FStar_Syntax_Syntax.sigmeta = uu____17434;
                      FStar_Syntax_Syntax.sigattrs = uu____17435;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____17476 =
                          let uu____17485 = inst_tscheme1 (uvs, k)  in
                          (uu____17485, rng)  in
                        FStar_Pervasives_Native.Some uu____17476
                    | uu____17506 ->
                        let uu____17507 =
                          let uu____17516 =
                            let uu____17521 =
                              let uu____17522 =
                                let uu____17525 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17525
                                 in
                              (uvs, uu____17522)  in
                            inst_tscheme1 uu____17521  in
                          (uu____17516, rng)  in
                        FStar_Pervasives_Native.Some uu____17507)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____17548,uu____17549);
                      FStar_Syntax_Syntax.sigrng = uu____17550;
                      FStar_Syntax_Syntax.sigquals = uu____17551;
                      FStar_Syntax_Syntax.sigmeta = uu____17552;
                      FStar_Syntax_Syntax.sigattrs = uu____17553;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____17595 =
                          let uu____17604 = inst_tscheme_with (uvs, k) us  in
                          (uu____17604, rng)  in
                        FStar_Pervasives_Native.Some uu____17595
                    | uu____17625 ->
                        let uu____17626 =
                          let uu____17635 =
                            let uu____17640 =
                              let uu____17641 =
                                let uu____17644 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____17644
                                 in
                              (uvs, uu____17641)  in
                            inst_tscheme_with uu____17640 us  in
                          (uu____17635, rng)  in
                        FStar_Pervasives_Native.Some uu____17626)
               | FStar_Util.Inr se ->
                   let uu____17680 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____17701;
                          FStar_Syntax_Syntax.sigrng = uu____17702;
                          FStar_Syntax_Syntax.sigquals = uu____17703;
                          FStar_Syntax_Syntax.sigmeta = uu____17704;
                          FStar_Syntax_Syntax.sigattrs = uu____17705;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____17720 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) env.range
                      in
                   FStar_All.pipe_right uu____17680
                     (FStar_Util.map_option
                        (fun uu____17768  ->
                           match uu____17768 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____17799 =
          let uu____17810 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____17810 mapper  in
        match uu____17799 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____17884 =
              let uu____17895 =
                let uu____17902 =
                  let uu___842_17905 = t  in
                  let uu____17906 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___842_17905.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17906;
                    FStar_Syntax_Syntax.vars =
                      (uu___842_17905.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17902)  in
              (uu____17895, r)  in
            FStar_Pervasives_Native.Some uu____17884
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17955 = lookup_qname env l  in
      match uu____17955 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17976 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____18030 = try_lookup_bv env bv  in
      match uu____18030 with
      | FStar_Pervasives_Native.None  ->
          let uu____18045 = variable_not_found bv  in
          FStar_Errors.raise_error uu____18045 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____18061 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____18062 =
            let uu____18063 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____18063  in
          (uu____18061, uu____18062)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____18085 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____18085 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____18151 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____18151  in
          let uu____18152 =
            let uu____18161 =
              let uu____18166 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____18166)  in
            (uu____18161, r1)  in
          FStar_Pervasives_Native.Some uu____18152
  
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
        let uu____18201 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____18201 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____18234,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____18259 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____18259  in
            let uu____18260 =
              let uu____18265 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____18265, r1)  in
            FStar_Pervasives_Native.Some uu____18260
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____18289 = try_lookup_lid env l  in
      match uu____18289 with
      | FStar_Pervasives_Native.None  ->
          let uu____18316 = name_not_found l  in
          let uu____18322 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____18316 uu____18322
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___5_18365  ->
              match uu___5_18365 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____18369 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18390 = lookup_qname env lid  in
      match uu____18390 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18399,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18402;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____18404;
              FStar_Syntax_Syntax.sigattrs = uu____18405;_},FStar_Pervasives_Native.None
            ),uu____18406)
          ->
          let uu____18455 =
            let uu____18462 =
              let uu____18463 =
                let uu____18466 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____18466 t  in
              (uvs, uu____18463)  in
            (uu____18462, q)  in
          FStar_Pervasives_Native.Some uu____18455
      | uu____18479 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18501 = lookup_qname env lid  in
      match uu____18501 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____18506,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____18509;
              FStar_Syntax_Syntax.sigquals = uu____18510;
              FStar_Syntax_Syntax.sigmeta = uu____18511;
              FStar_Syntax_Syntax.sigattrs = uu____18512;_},FStar_Pervasives_Native.None
            ),uu____18513)
          ->
          let uu____18562 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18562 (uvs, t)
      | uu____18567 ->
          let uu____18568 = name_not_found lid  in
          let uu____18574 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18568 uu____18574
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____18594 = lookup_qname env lid  in
      match uu____18594 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18599,uvs,t,uu____18602,uu____18603,uu____18604);
              FStar_Syntax_Syntax.sigrng = uu____18605;
              FStar_Syntax_Syntax.sigquals = uu____18606;
              FStar_Syntax_Syntax.sigmeta = uu____18607;
              FStar_Syntax_Syntax.sigattrs = uu____18608;_},FStar_Pervasives_Native.None
            ),uu____18609)
          ->
          let uu____18664 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____18664 (uvs, t)
      | uu____18669 ->
          let uu____18670 = name_not_found lid  in
          let uu____18676 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____18670 uu____18676
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____18699 = lookup_qname env lid  in
      match uu____18699 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____18707,uu____18708,uu____18709,uu____18710,uu____18711,dcs);
              FStar_Syntax_Syntax.sigrng = uu____18713;
              FStar_Syntax_Syntax.sigquals = uu____18714;
              FStar_Syntax_Syntax.sigmeta = uu____18715;
              FStar_Syntax_Syntax.sigattrs = uu____18716;_},uu____18717),uu____18718)
          -> (true, dcs)
      | uu____18781 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____18797 = lookup_qname env lid  in
      match uu____18797 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____18798,uu____18799,uu____18800,l,uu____18802,uu____18803);
              FStar_Syntax_Syntax.sigrng = uu____18804;
              FStar_Syntax_Syntax.sigquals = uu____18805;
              FStar_Syntax_Syntax.sigmeta = uu____18806;
              FStar_Syntax_Syntax.sigattrs = uu____18807;_},uu____18808),uu____18809)
          -> l
      | uu____18866 ->
          let uu____18867 =
            let uu____18869 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____18869  in
          failwith uu____18867
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18939)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18996) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____19020 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____19020
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____19055 -> FStar_Pervasives_Native.None)
          | uu____19064 -> FStar_Pervasives_Native.None
  
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
        let uu____19126 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____19126
  
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
        let uu____19159 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____19159
  
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
             (FStar_Util.Inl uu____19211,uu____19212) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____19261),uu____19262) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____19311 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_bundle uu____19329 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_datacon uu____19339 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero)
              | FStar_Syntax_Syntax.Sig_declare_typ uu____19356 ->
                  let uu____19363 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____19363
              | FStar_Syntax_Syntax.Sig_let ((uu____19364,lbs),uu____19366)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____19382 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____19382
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____19389 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_one)
              | FStar_Syntax_Syntax.Sig_main uu____19397 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____19398 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____19405 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19406 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____19407 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____19408 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____19421 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____19439 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____19439
           (fun d_opt  ->
              let uu____19452 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____19452
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____19462 =
                   let uu____19465 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____19465  in
                 match uu____19462 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____19466 =
                       let uu____19468 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____19468
                        in
                     failwith uu____19466
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____19473 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____19473
                       then
                         let uu____19476 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____19478 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____19480 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____19476 uu____19478 uu____19480
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
        (FStar_Util.Inr (se,uu____19505),uu____19506) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____19555 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____19577),uu____19578) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____19627 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____19649 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____19649
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____19672 = lookup_attrs_of_lid env fv_lid1  in
        match uu____19672 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____19696 =
                      let uu____19697 = FStar_Syntax_Util.un_uinst tm  in
                      uu____19697.FStar_Syntax_Syntax.n  in
                    match uu____19696 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____19702 -> false))
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        fv_with_lid_has_attr env
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v attr_lid
  
let (fv_has_strict_args :
  env ->
    FStar_Syntax_Syntax.fv ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let s =
        let uu____19739 = FStar_Syntax_Syntax.lid_of_fv fv  in
        uu____19739.FStar_Ident.str  in
      let uu____19740 = FStar_Util.smap_try_find env.strict_args_tab s  in
      match uu____19740 with
      | FStar_Pervasives_Native.None  ->
          let attrs =
            let uu____19768 = FStar_Syntax_Syntax.lid_of_fv fv  in
            lookup_attrs_of_lid env uu____19768  in
          (match attrs with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some attrs1 ->
               let res =
                 FStar_Util.find_map attrs1
                   (fun x  ->
                      let uu____19796 =
                        FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                          FStar_Parser_Const.strict_on_arguments_attr
                         in
                      FStar_Pervasives_Native.fst uu____19796)
                  in
               (FStar_Util.smap_add env.strict_args_tab s res; res))
      | FStar_Pervasives_Native.Some l -> l
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____19846 = lookup_qname env ftv  in
      match uu____19846 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____19850) ->
          let uu____19895 =
            effect_signature FStar_Pervasives_Native.None se env.range  in
          (match uu____19895 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____19916,t),r) ->
               let uu____19931 =
                 let uu____19932 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____19932 t  in
               FStar_Pervasives_Native.Some uu____19931)
      | uu____19933 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____19945 = try_lookup_effect_lid env ftv  in
      match uu____19945 with
      | FStar_Pervasives_Native.None  ->
          let uu____19948 = name_not_found ftv  in
          let uu____19954 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____19948 uu____19954
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
        let uu____19978 = lookup_qname env lid0  in
        match uu____19978 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____19989);
                FStar_Syntax_Syntax.sigrng = uu____19990;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____19992;
                FStar_Syntax_Syntax.sigattrs = uu____19993;_},FStar_Pervasives_Native.None
              ),uu____19994)
            ->
            let lid1 =
              let uu____20048 =
                let uu____20049 = FStar_Ident.range_of_lid lid  in
                let uu____20050 =
                  let uu____20051 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____20051  in
                FStar_Range.set_use_range uu____20049 uu____20050  in
              FStar_Ident.set_lid_range lid uu____20048  in
            let uu____20052 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___6_20058  ->
                      match uu___6_20058 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____20061 -> false))
               in
            if uu____20052
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____20080 =
                      let uu____20082 =
                        let uu____20084 = get_range env  in
                        FStar_Range.string_of_range uu____20084  in
                      let uu____20085 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____20087 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____20082 uu____20085 uu____20087
                       in
                    failwith uu____20080)
                  in
               match (binders, univs1) with
               | ([],uu____20108) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____20134,uu____20135::uu____20136::uu____20137) ->
                   let uu____20158 =
                     let uu____20160 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____20162 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____20160 uu____20162
                      in
                   failwith uu____20158
               | uu____20173 ->
                   let uu____20188 =
                     let uu____20193 =
                       let uu____20194 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____20194)  in
                     inst_tscheme_with uu____20193 insts  in
                   (match uu____20188 with
                    | (uu____20207,t) ->
                        let t1 =
                          let uu____20210 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____20210 t  in
                        let uu____20211 =
                          let uu____20212 = FStar_Syntax_Subst.compress t1
                             in
                          uu____20212.FStar_Syntax_Syntax.n  in
                        (match uu____20211 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____20247 -> failwith "Impossible")))
        | uu____20255 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____20279 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____20279 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____20292,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____20299 = find1 l2  in
            (match uu____20299 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____20306 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____20306 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____20310 = find1 l  in
            (match uu____20310 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____20315 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____20315
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____20330 = lookup_qname env l1  in
      match uu____20330 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____20333;
              FStar_Syntax_Syntax.sigrng = uu____20334;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____20336;
              FStar_Syntax_Syntax.sigattrs = uu____20337;_},uu____20338),uu____20339)
          -> q
      | uu____20390 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____20414 =
          let uu____20415 =
            let uu____20417 = FStar_Util.string_of_int i  in
            let uu____20419 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____20417 uu____20419
             in
          failwith uu____20415  in
        let uu____20422 = lookup_datacon env lid  in
        match uu____20422 with
        | (uu____20427,t) ->
            let uu____20429 =
              let uu____20430 = FStar_Syntax_Subst.compress t  in
              uu____20430.FStar_Syntax_Syntax.n  in
            (match uu____20429 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____20434) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____20478 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____20478
                      FStar_Pervasives_Native.fst)
             | uu____20489 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20503 = lookup_qname env l  in
      match uu____20503 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____20505,uu____20506,uu____20507);
              FStar_Syntax_Syntax.sigrng = uu____20508;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20510;
              FStar_Syntax_Syntax.sigattrs = uu____20511;_},uu____20512),uu____20513)
          ->
          FStar_Util.for_some
            (fun uu___7_20566  ->
               match uu___7_20566 with
               | FStar_Syntax_Syntax.Projector uu____20568 -> true
               | uu____20574 -> false) quals
      | uu____20576 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20590 = lookup_qname env lid  in
      match uu____20590 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____20592,uu____20593,uu____20594,uu____20595,uu____20596,uu____20597);
              FStar_Syntax_Syntax.sigrng = uu____20598;
              FStar_Syntax_Syntax.sigquals = uu____20599;
              FStar_Syntax_Syntax.sigmeta = uu____20600;
              FStar_Syntax_Syntax.sigattrs = uu____20601;_},uu____20602),uu____20603)
          -> true
      | uu____20661 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20675 = lookup_qname env lid  in
      match uu____20675 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20677,uu____20678,uu____20679,uu____20680,uu____20681,uu____20682);
              FStar_Syntax_Syntax.sigrng = uu____20683;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____20685;
              FStar_Syntax_Syntax.sigattrs = uu____20686;_},uu____20687),uu____20688)
          ->
          FStar_Util.for_some
            (fun uu___8_20749  ->
               match uu___8_20749 with
               | FStar_Syntax_Syntax.RecordType uu____20751 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____20761 -> true
               | uu____20771 -> false) quals
      | uu____20773 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____20783,uu____20784);
            FStar_Syntax_Syntax.sigrng = uu____20785;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____20787;
            FStar_Syntax_Syntax.sigattrs = uu____20788;_},uu____20789),uu____20790)
        ->
        FStar_Util.for_some
          (fun uu___9_20847  ->
             match uu___9_20847 with
             | FStar_Syntax_Syntax.Action uu____20849 -> true
             | uu____20851 -> false) quals
    | uu____20853 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____20867 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____20867
  
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
      let uu____20884 =
        let uu____20885 = FStar_Syntax_Util.un_uinst head1  in
        uu____20885.FStar_Syntax_Syntax.n  in
      match uu____20884 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____20891 ->
               true
           | uu____20894 -> false)
      | uu____20896 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____20910 = lookup_qname env l  in
      match uu____20910 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____20913),uu____20914) ->
          FStar_Util.for_some
            (fun uu___10_20962  ->
               match uu___10_20962 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____20965 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____20967 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____21043 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____21061) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____21079 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____21087 ->
                 FStar_Pervasives_Native.Some true
             | uu____21106 -> FStar_Pervasives_Native.Some false)
         in
      let uu____21109 =
        let uu____21113 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____21113 mapper  in
      match uu____21109 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____21173 = lookup_qname env lid  in
      match uu____21173 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____21177,uu____21178,tps,uu____21180,uu____21181,uu____21182);
              FStar_Syntax_Syntax.sigrng = uu____21183;
              FStar_Syntax_Syntax.sigquals = uu____21184;
              FStar_Syntax_Syntax.sigmeta = uu____21185;
              FStar_Syntax_Syntax.sigattrs = uu____21186;_},uu____21187),uu____21188)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____21254 -> FStar_Pervasives_Native.None
  
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
           (fun uu____21300  ->
              match uu____21300 with
              | (d,uu____21309) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____21325 = effect_decl_opt env l  in
      match uu____21325 with
      | FStar_Pervasives_Native.None  ->
          let uu____21340 = name_not_found l  in
          let uu____21346 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____21340 uu____21346
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (is_layered_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____21374 = FStar_All.pipe_right l (get_effect_decl env)  in
      FStar_All.pipe_right uu____21374
        (fun ed  -> ed.FStar_Syntax_Syntax.is_layered)
  
let (identity_mlift : mlift) =
  {
    mlift_t = FStar_Pervasives_Native.None;
    mlift_wp = (fun uu____21382  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____21401  ->
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
        let uu____21433 = FStar_Ident.lid_equals l1 l2  in
        if uu____21433
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____21444 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____21444
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____21455 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____21508  ->
                        match uu____21508 with
                        | (m1,m2,uu____21522,uu____21523,uu____21524) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____21455 with
              | FStar_Pervasives_Native.None  ->
                  let uu____21541 =
                    let uu____21547 =
                      let uu____21549 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____21551 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____21549
                        uu____21551
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____21547)
                     in
                  FStar_Errors.raise_error uu____21541 env.range
              | FStar_Pervasives_Native.Some
                  (uu____21561,uu____21562,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____21596 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____21596
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
  'Auu____21616 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____21616) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____21645 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____21671  ->
                match uu____21671 with
                | (d,uu____21678) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____21645 with
      | FStar_Pervasives_Native.None  ->
          let uu____21689 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____21689
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____21704 = inst_tscheme md.FStar_Syntax_Syntax.signature  in
          (match uu____21704 with
           | (uu____21715,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____21733)::(wp,uu____21735)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____21791 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1502_21841 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1502_21841.order);
              joins = (uu___1502_21841.joins)
            }  in
          let uu___1505_21850 = env  in
          {
            solver = (uu___1505_21850.solver);
            range = (uu___1505_21850.range);
            curmodule = (uu___1505_21850.curmodule);
            gamma = (uu___1505_21850.gamma);
            gamma_sig = (uu___1505_21850.gamma_sig);
            gamma_cache = (uu___1505_21850.gamma_cache);
            modules = (uu___1505_21850.modules);
            expected_typ = (uu___1505_21850.expected_typ);
            sigtab = (uu___1505_21850.sigtab);
            attrtab = (uu___1505_21850.attrtab);
            is_pattern = (uu___1505_21850.is_pattern);
            instantiate_imp = (uu___1505_21850.instantiate_imp);
            effects;
            generalize = (uu___1505_21850.generalize);
            letrecs = (uu___1505_21850.letrecs);
            top_level = (uu___1505_21850.top_level);
            check_uvars = (uu___1505_21850.check_uvars);
            use_eq = (uu___1505_21850.use_eq);
            is_iface = (uu___1505_21850.is_iface);
            admit = (uu___1505_21850.admit);
            lax = (uu___1505_21850.lax);
            lax_universes = (uu___1505_21850.lax_universes);
            phase1 = (uu___1505_21850.phase1);
            failhard = (uu___1505_21850.failhard);
            nosynth = (uu___1505_21850.nosynth);
            uvar_subtyping = (uu___1505_21850.uvar_subtyping);
            tc_term = (uu___1505_21850.tc_term);
            type_of = (uu___1505_21850.type_of);
            universe_of = (uu___1505_21850.universe_of);
            check_type_of = (uu___1505_21850.check_type_of);
            use_bv_sorts = (uu___1505_21850.use_bv_sorts);
            qtbl_name_and_index = (uu___1505_21850.qtbl_name_and_index);
            normalized_eff_names = (uu___1505_21850.normalized_eff_names);
            fv_delta_depths = (uu___1505_21850.fv_delta_depths);
            proof_ns = (uu___1505_21850.proof_ns);
            synth_hook = (uu___1505_21850.synth_hook);
            try_solve_implicits_hook =
              (uu___1505_21850.try_solve_implicits_hook);
            splice = (uu___1505_21850.splice);
            postprocess = (uu___1505_21850.postprocess);
            is_native_tactic = (uu___1505_21850.is_native_tactic);
            identifier_info = (uu___1505_21850.identifier_info);
            tc_hooks = (uu___1505_21850.tc_hooks);
            dsenv = (uu___1505_21850.dsenv);
            nbe = (uu___1505_21850.nbe);
            strict_args_tab = (uu___1505_21850.strict_args_tab)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let src_ed = get_effect_decl env sub1.FStar_Syntax_Syntax.source
             in
          let dst_ed = get_effect_decl env sub1.FStar_Syntax_Syntax.target
             in
          if
            src_ed.FStar_Syntax_Syntax.is_layered ||
              dst_ed.FStar_Syntax_Syntax.is_layered
          then
            let edge =
              {
                msource = (sub1.FStar_Syntax_Syntax.source);
                mtarget = (sub1.FStar_Syntax_Syntax.target);
                mlift =
                  {
                    mlift_t = (sub1.FStar_Syntax_Syntax.lift_wp);
                    mlift_wp =
                      (fun uu____21859  ->
                         fun uu____21860  ->
                           fun uu____21861  -> FStar_Syntax_Syntax.tun);
                    mlift_term = FStar_Pervasives_Native.None
                  }
              }  in
            let dummy_mlift =
              {
                mlift_t = FStar_Pervasives_Native.None;
                mlift_wp =
                  (fun uu____21878  ->
                     fun uu____21879  ->
                       fun uu____21880  -> FStar_Syntax_Syntax.tun);
                mlift_term = FStar_Pervasives_Native.None
              }  in
            let n_join1 =
              ((src_ed.FStar_Syntax_Syntax.mname),
                (dst_ed.FStar_Syntax_Syntax.mname),
                (dst_ed.FStar_Syntax_Syntax.mname), dummy_mlift, dummy_mlift)
               in
            let n_join2 =
              ((dst_ed.FStar_Syntax_Syntax.mname),
                (src_ed.FStar_Syntax_Syntax.mname),
                (dst_ed.FStar_Syntax_Syntax.mname), dummy_mlift, dummy_mlift)
               in
            let uu___1522_21915 = env  in
            {
              solver = (uu___1522_21915.solver);
              range = (uu___1522_21915.range);
              curmodule = (uu___1522_21915.curmodule);
              gamma = (uu___1522_21915.gamma);
              gamma_sig = (uu___1522_21915.gamma_sig);
              gamma_cache = (uu___1522_21915.gamma_cache);
              modules = (uu___1522_21915.modules);
              expected_typ = (uu___1522_21915.expected_typ);
              sigtab = (uu___1522_21915.sigtab);
              attrtab = (uu___1522_21915.attrtab);
              is_pattern = (uu___1522_21915.is_pattern);
              instantiate_imp = (uu___1522_21915.instantiate_imp);
              effects =
                (let uu___1524_21917 = env.effects  in
                 {
                   decls = (uu___1524_21917.decls);
                   order = (edge :: ((env.effects).order));
                   joins = (n_join1 :: n_join2 :: ((env.effects).joins))
                 });
              generalize = (uu___1522_21915.generalize);
              letrecs = (uu___1522_21915.letrecs);
              top_level = (uu___1522_21915.top_level);
              check_uvars = (uu___1522_21915.check_uvars);
              use_eq = (uu___1522_21915.use_eq);
              is_iface = (uu___1522_21915.is_iface);
              admit = (uu___1522_21915.admit);
              lax = (uu___1522_21915.lax);
              lax_universes = (uu___1522_21915.lax_universes);
              phase1 = (uu___1522_21915.phase1);
              failhard = (uu___1522_21915.failhard);
              nosynth = (uu___1522_21915.nosynth);
              uvar_subtyping = (uu___1522_21915.uvar_subtyping);
              tc_term = (uu___1522_21915.tc_term);
              type_of = (uu___1522_21915.type_of);
              universe_of = (uu___1522_21915.universe_of);
              check_type_of = (uu___1522_21915.check_type_of);
              use_bv_sorts = (uu___1522_21915.use_bv_sorts);
              qtbl_name_and_index = (uu___1522_21915.qtbl_name_and_index);
              normalized_eff_names = (uu___1522_21915.normalized_eff_names);
              fv_delta_depths = (uu___1522_21915.fv_delta_depths);
              proof_ns = (uu___1522_21915.proof_ns);
              synth_hook = (uu___1522_21915.synth_hook);
              try_solve_implicits_hook =
                (uu___1522_21915.try_solve_implicits_hook);
              splice = (uu___1522_21915.splice);
              postprocess = (uu___1522_21915.postprocess);
              is_native_tactic = (uu___1522_21915.is_native_tactic);
              identifier_info = (uu___1522_21915.identifier_info);
              tc_hooks = (uu___1522_21915.tc_hooks);
              dsenv = (uu___1522_21915.dsenv);
              nbe = (uu___1522_21915.nbe);
              strict_args_tab = (uu___1522_21915.strict_args_tab)
            }
          else
            (let compose_edges e1 e2 =
               let composed_lift =
                 let mlift_wp u r wp1 =
                   let uu____21968 = (e1.mlift).mlift_wp u r wp1  in
                   (e2.mlift).mlift_wp u r uu____21968  in
                 let mlift_term =
                   match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term))
                   with
                   | (FStar_Pervasives_Native.Some
                      l1,FStar_Pervasives_Native.Some l2) ->
                       FStar_Pervasives_Native.Some
                         ((fun u  ->
                             fun t  ->
                               fun wp  ->
                                 fun e  ->
                                   let uu____22126 =
                                     (e1.mlift).mlift_wp u t wp  in
                                   let uu____22127 = l1 u t wp e  in
                                   l2 u t uu____22126 uu____22127))
                   | uu____22128 -> FStar_Pervasives_Native.None  in
                 {
                   mlift_t = FStar_Pervasives_Native.None;
                   mlift_wp;
                   mlift_term
                 }  in
               {
                 msource = (e1.msource);
                 mtarget = (e2.mtarget);
                 mlift = composed_lift
               }  in
             let mk_mlift_wp lift_t u r wp1 =
               let uu____22200 = inst_tscheme_with lift_t [u]  in
               match uu____22200 with
               | (uu____22207,lift_t1) ->
                   let uu____22209 =
                     let uu____22216 =
                       let uu____22217 =
                         let uu____22234 =
                           let uu____22245 = FStar_Syntax_Syntax.as_arg r  in
                           let uu____22254 =
                             let uu____22265 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             [uu____22265]  in
                           uu____22245 :: uu____22254  in
                         (lift_t1, uu____22234)  in
                       FStar_Syntax_Syntax.Tm_app uu____22217  in
                     FStar_Syntax_Syntax.mk uu____22216  in
                   uu____22209 FStar_Pervasives_Native.None
                     wp1.FStar_Syntax_Syntax.pos
                in
             let sub_mlift_wp =
               match sub1.FStar_Syntax_Syntax.lift_wp with
               | FStar_Pervasives_Native.Some sub_lift_wp ->
                   mk_mlift_wp sub_lift_wp
               | FStar_Pervasives_Native.None  ->
                   failwith
                     "sub effect should've been elaborated at this stage"
                in
             let mk_mlift_term lift_t u r wp1 e =
               let uu____22375 = inst_tscheme_with lift_t [u]  in
               match uu____22375 with
               | (uu____22382,lift_t1) ->
                   let uu____22384 =
                     let uu____22391 =
                       let uu____22392 =
                         let uu____22409 =
                           let uu____22420 = FStar_Syntax_Syntax.as_arg r  in
                           let uu____22429 =
                             let uu____22440 = FStar_Syntax_Syntax.as_arg wp1
                                in
                             let uu____22449 =
                               let uu____22460 = FStar_Syntax_Syntax.as_arg e
                                  in
                               [uu____22460]  in
                             uu____22440 :: uu____22449  in
                           uu____22420 :: uu____22429  in
                         (lift_t1, uu____22409)  in
                       FStar_Syntax_Syntax.Tm_app uu____22392  in
                     FStar_Syntax_Syntax.mk uu____22391  in
                   uu____22384 FStar_Pervasives_Native.None
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
                   {
                     mlift_t = FStar_Pervasives_Native.None;
                     mlift_wp = sub_mlift_wp;
                     mlift_term = sub_mlift_term
                   }
               }  in
             let id_edge l =
               {
                 msource = (sub1.FStar_Syntax_Syntax.source);
                 mtarget = (sub1.FStar_Syntax_Syntax.target);
                 mlift = identity_mlift
               }  in
             let print_mlift l =
               let bogus_term s =
                 let uu____22562 =
                   let uu____22563 =
                     FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                   FStar_Syntax_Syntax.lid_as_fv uu____22563
                     FStar_Syntax_Syntax.delta_constant
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____22562  in
               let arg = bogus_term "ARG"  in
               let wp = bogus_term "WP"  in
               let e = bogus_term "COMP"  in
               let uu____22572 =
                 let uu____22574 =
                   l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp  in
                 FStar_Syntax_Print.term_to_string uu____22574  in
               let uu____22575 =
                 let uu____22577 =
                   FStar_Util.map_opt l.mlift_term
                     (fun l1  ->
                        let uu____22605 =
                          l1 FStar_Syntax_Syntax.U_zero arg wp e  in
                        FStar_Syntax_Print.term_to_string uu____22605)
                    in
                 FStar_Util.dflt "none" uu____22577  in
               FStar_Util.format2 "{ wp : %s ; term : %s }" uu____22572
                 uu____22575
                in
             let order = edge :: ((env.effects).order)  in
             let ms =
               FStar_All.pipe_right (env.effects).decls
                 (FStar_List.map
                    (fun uu____22634  ->
                       match uu____22634 with
                       | (e,uu____22642) -> e.FStar_Syntax_Syntax.mname))
                in
             let find_edge order1 uu____22665 =
               match uu____22665 with
               | (i,j) ->
                   let uu____22676 = FStar_Ident.lid_equals i j  in
                   if uu____22676
                   then
                     FStar_All.pipe_right (id_edge i)
                       (fun _22683  -> FStar_Pervasives_Native.Some _22683)
                   else
                     FStar_All.pipe_right order1
                       (FStar_Util.find_opt
                          (fun e  ->
                             (FStar_Ident.lid_equals e.msource i) &&
                               (FStar_Ident.lid_equals e.mtarget j)))
                in
             let order1 =
               let fold_fun order1 k =
                 let uu____22712 =
                   FStar_All.pipe_right ms
                     (FStar_List.collect
                        (fun i  ->
                           let uu____22722 = FStar_Ident.lid_equals i k  in
                           if uu____22722
                           then []
                           else
                             FStar_All.pipe_right ms
                               (FStar_List.collect
                                  (fun j  ->
                                     let uu____22736 =
                                       FStar_Ident.lid_equals j k  in
                                     if uu____22736
                                     then []
                                     else
                                       (let uu____22743 =
                                          let uu____22752 =
                                            find_edge order1 (i, k)  in
                                          let uu____22755 =
                                            find_edge order1 (k, j)  in
                                          (uu____22752, uu____22755)  in
                                        match uu____22743 with
                                        | (FStar_Pervasives_Native.Some
                                           e1,FStar_Pervasives_Native.Some
                                           e2) ->
                                            let uu____22770 =
                                              compose_edges e1 e2  in
                                            [uu____22770]
                                        | uu____22771 -> [])))))
                    in
                 FStar_List.append order1 uu____22712  in
               FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)
                in
             let order2 =
               FStar_Util.remove_dups
                 (fun e1  ->
                    fun e2  ->
                      (FStar_Ident.lid_equals e1.msource e2.msource) &&
                        (FStar_Ident.lid_equals e1.mtarget e2.mtarget))
                 order1
                in
             FStar_All.pipe_right order2
               (FStar_List.iter
                  (fun edge1  ->
                     let uu____22801 =
                       (FStar_Ident.lid_equals edge1.msource
                          FStar_Parser_Const.effect_DIV_lid)
                         &&
                         (let uu____22804 =
                            lookup_effect_quals env edge1.mtarget  in
                          FStar_All.pipe_right uu____22804
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect))
                        in
                     if uu____22801
                     then
                       let uu____22811 =
                         let uu____22817 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                           uu____22817)
                          in
                       let uu____22821 = get_range env  in
                       FStar_Errors.raise_error uu____22811 uu____22821
                     else ()));
             (let joins =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        FStar_All.pipe_right ms
                          (FStar_List.collect
                             (fun j  ->
                                let join_opt =
                                  let uu____22899 =
                                    FStar_Ident.lid_equals i j  in
                                  if uu____22899
                                  then
                                    FStar_Pervasives_Native.Some
                                      (i, (id_edge i), (id_edge i))
                                  else
                                    FStar_All.pipe_right ms
                                      (FStar_List.fold_left
                                         (fun bopt  ->
                                            fun k  ->
                                              let uu____22951 =
                                                let uu____22960 =
                                                  find_edge order2 (i, k)  in
                                                let uu____22963 =
                                                  find_edge order2 (j, k)  in
                                                (uu____22960, uu____22963)
                                                 in
                                              match uu____22951 with
                                              | (FStar_Pervasives_Native.Some
                                                 ik,FStar_Pervasives_Native.Some
                                                 jk) ->
                                                  (match bopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.Some
                                                         (k, ik, jk)
                                                   | FStar_Pervasives_Native.Some
                                                       (ub,uu____23005,uu____23006)
                                                       ->
                                                       let uu____23013 =
                                                         let uu____23020 =
                                                           let uu____23022 =
                                                             find_edge order2
                                                               (k, ub)
                                                              in
                                                           FStar_Util.is_some
                                                             uu____23022
                                                            in
                                                         let uu____23025 =
                                                           let uu____23027 =
                                                             find_edge order2
                                                               (ub, k)
                                                              in
                                                           FStar_Util.is_some
                                                             uu____23027
                                                            in
                                                         (uu____23020,
                                                           uu____23025)
                                                          in
                                                       (match uu____23013
                                                        with
                                                        | (true ,true ) ->
                                                            let uu____23044 =
                                                              FStar_Ident.lid_equals
                                                                k ub
                                                               in
                                                            if uu____23044
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
                                              | uu____23087 -> bopt)
                                         FStar_Pervasives_Native.None)
                                   in
                                match join_opt with
                                | FStar_Pervasives_Native.None  -> []
                                | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                    [(i, j, k, (e1.mlift), (e2.mlift))]))))
                 in
              let effects =
                let uu___1649_23160 = env.effects  in
                { decls = (uu___1649_23160.decls); order = order2; joins }
                 in
              let uu___1652_23161 = env  in
              {
                solver = (uu___1652_23161.solver);
                range = (uu___1652_23161.range);
                curmodule = (uu___1652_23161.curmodule);
                gamma = (uu___1652_23161.gamma);
                gamma_sig = (uu___1652_23161.gamma_sig);
                gamma_cache = (uu___1652_23161.gamma_cache);
                modules = (uu___1652_23161.modules);
                expected_typ = (uu___1652_23161.expected_typ);
                sigtab = (uu___1652_23161.sigtab);
                attrtab = (uu___1652_23161.attrtab);
                is_pattern = (uu___1652_23161.is_pattern);
                instantiate_imp = (uu___1652_23161.instantiate_imp);
                effects;
                generalize = (uu___1652_23161.generalize);
                letrecs = (uu___1652_23161.letrecs);
                top_level = (uu___1652_23161.top_level);
                check_uvars = (uu___1652_23161.check_uvars);
                use_eq = (uu___1652_23161.use_eq);
                is_iface = (uu___1652_23161.is_iface);
                admit = (uu___1652_23161.admit);
                lax = (uu___1652_23161.lax);
                lax_universes = (uu___1652_23161.lax_universes);
                phase1 = (uu___1652_23161.phase1);
                failhard = (uu___1652_23161.failhard);
                nosynth = (uu___1652_23161.nosynth);
                uvar_subtyping = (uu___1652_23161.uvar_subtyping);
                tc_term = (uu___1652_23161.tc_term);
                type_of = (uu___1652_23161.type_of);
                universe_of = (uu___1652_23161.universe_of);
                check_type_of = (uu___1652_23161.check_type_of);
                use_bv_sorts = (uu___1652_23161.use_bv_sorts);
                qtbl_name_and_index = (uu___1652_23161.qtbl_name_and_index);
                normalized_eff_names = (uu___1652_23161.normalized_eff_names);
                fv_delta_depths = (uu___1652_23161.fv_delta_depths);
                proof_ns = (uu___1652_23161.proof_ns);
                synth_hook = (uu___1652_23161.synth_hook);
                try_solve_implicits_hook =
                  (uu___1652_23161.try_solve_implicits_hook);
                splice = (uu___1652_23161.splice);
                postprocess = (uu___1652_23161.postprocess);
                is_native_tactic = (uu___1652_23161.is_native_tactic);
                identifier_info = (uu___1652_23161.identifier_info);
                tc_hooks = (uu___1652_23161.tc_hooks);
                dsenv = (uu___1652_23161.dsenv);
                nbe = (uu___1652_23161.nbe);
                strict_args_tab = (uu___1652_23161.strict_args_tab)
              }))
      | uu____23162 -> env
  
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
        | uu____23191 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____23204 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____23204 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____23221 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____23221 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       Prims.int_one)
                then
                  (let uu____23246 =
                     let uu____23252 =
                       let uu____23254 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____23262 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + Prims.int_one)
                          in
                       let uu____23273 =
                         let uu____23275 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____23275  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____23254 uu____23262 uu____23273
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____23252)
                      in
                   FStar_Errors.raise_error uu____23246
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____23283 =
                     let uu____23294 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____23294 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____23331  ->
                        fun uu____23332  ->
                          match (uu____23331, uu____23332) with
                          | ((x,uu____23362),(t,uu____23364)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____23283
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____23395 =
                     let uu___1690_23396 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1690_23396.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1690_23396.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1690_23396.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1690_23396.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____23395
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____23408 .
    'Auu____23408 ->
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
          let uu____23438 = effect_decl_opt env effect_name  in
          match uu____23438 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____23481 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____23504 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____23543 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____23543
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____23548 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____23548
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ed.FStar_Syntax_Syntax.repr
                      in
                   let uu____23559 =
                     let uu____23562 = get_range env  in
                     let uu____23563 =
                       let uu____23570 =
                         let uu____23571 =
                           let uu____23588 =
                             let uu____23599 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____23599; wp]  in
                           (repr, uu____23588)  in
                         FStar_Syntax_Syntax.Tm_app uu____23571  in
                       FStar_Syntax_Syntax.mk uu____23570  in
                     uu____23563 FStar_Pervasives_Native.None uu____23562  in
                   FStar_Pervasives_Native.Some uu____23559)
  
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
      | uu____23743 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____23758 =
        let uu____23759 = FStar_Syntax_Subst.compress t  in
        uu____23759.FStar_Syntax_Syntax.n  in
      match uu____23758 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____23763,c) ->
          is_reifiable_comp env c
      | uu____23785 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____23805 =
           let uu____23807 = is_reifiable_effect env l  in
           Prims.op_Negation uu____23807  in
         if uu____23805
         then
           let uu____23810 =
             let uu____23816 =
               let uu____23818 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____23818
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____23816)  in
           let uu____23822 = get_range env  in
           FStar_Errors.raise_error uu____23810 uu____23822
         else ());
        (let uu____23825 = effect_repr_aux true env c u_c  in
         match uu____23825 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1755_23861 = env  in
        {
          solver = (uu___1755_23861.solver);
          range = (uu___1755_23861.range);
          curmodule = (uu___1755_23861.curmodule);
          gamma = (uu___1755_23861.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1755_23861.gamma_cache);
          modules = (uu___1755_23861.modules);
          expected_typ = (uu___1755_23861.expected_typ);
          sigtab = (uu___1755_23861.sigtab);
          attrtab = (uu___1755_23861.attrtab);
          is_pattern = (uu___1755_23861.is_pattern);
          instantiate_imp = (uu___1755_23861.instantiate_imp);
          effects = (uu___1755_23861.effects);
          generalize = (uu___1755_23861.generalize);
          letrecs = (uu___1755_23861.letrecs);
          top_level = (uu___1755_23861.top_level);
          check_uvars = (uu___1755_23861.check_uvars);
          use_eq = (uu___1755_23861.use_eq);
          is_iface = (uu___1755_23861.is_iface);
          admit = (uu___1755_23861.admit);
          lax = (uu___1755_23861.lax);
          lax_universes = (uu___1755_23861.lax_universes);
          phase1 = (uu___1755_23861.phase1);
          failhard = (uu___1755_23861.failhard);
          nosynth = (uu___1755_23861.nosynth);
          uvar_subtyping = (uu___1755_23861.uvar_subtyping);
          tc_term = (uu___1755_23861.tc_term);
          type_of = (uu___1755_23861.type_of);
          universe_of = (uu___1755_23861.universe_of);
          check_type_of = (uu___1755_23861.check_type_of);
          use_bv_sorts = (uu___1755_23861.use_bv_sorts);
          qtbl_name_and_index = (uu___1755_23861.qtbl_name_and_index);
          normalized_eff_names = (uu___1755_23861.normalized_eff_names);
          fv_delta_depths = (uu___1755_23861.fv_delta_depths);
          proof_ns = (uu___1755_23861.proof_ns);
          synth_hook = (uu___1755_23861.synth_hook);
          try_solve_implicits_hook =
            (uu___1755_23861.try_solve_implicits_hook);
          splice = (uu___1755_23861.splice);
          postprocess = (uu___1755_23861.postprocess);
          is_native_tactic = (uu___1755_23861.is_native_tactic);
          identifier_info = (uu___1755_23861.identifier_info);
          tc_hooks = (uu___1755_23861.tc_hooks);
          dsenv = (uu___1755_23861.dsenv);
          nbe = (uu___1755_23861.nbe);
          strict_args_tab = (uu___1755_23861.strict_args_tab)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1762_23875 = env  in
      {
        solver = (uu___1762_23875.solver);
        range = (uu___1762_23875.range);
        curmodule = (uu___1762_23875.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1762_23875.gamma_sig);
        gamma_cache = (uu___1762_23875.gamma_cache);
        modules = (uu___1762_23875.modules);
        expected_typ = (uu___1762_23875.expected_typ);
        sigtab = (uu___1762_23875.sigtab);
        attrtab = (uu___1762_23875.attrtab);
        is_pattern = (uu___1762_23875.is_pattern);
        instantiate_imp = (uu___1762_23875.instantiate_imp);
        effects = (uu___1762_23875.effects);
        generalize = (uu___1762_23875.generalize);
        letrecs = (uu___1762_23875.letrecs);
        top_level = (uu___1762_23875.top_level);
        check_uvars = (uu___1762_23875.check_uvars);
        use_eq = (uu___1762_23875.use_eq);
        is_iface = (uu___1762_23875.is_iface);
        admit = (uu___1762_23875.admit);
        lax = (uu___1762_23875.lax);
        lax_universes = (uu___1762_23875.lax_universes);
        phase1 = (uu___1762_23875.phase1);
        failhard = (uu___1762_23875.failhard);
        nosynth = (uu___1762_23875.nosynth);
        uvar_subtyping = (uu___1762_23875.uvar_subtyping);
        tc_term = (uu___1762_23875.tc_term);
        type_of = (uu___1762_23875.type_of);
        universe_of = (uu___1762_23875.universe_of);
        check_type_of = (uu___1762_23875.check_type_of);
        use_bv_sorts = (uu___1762_23875.use_bv_sorts);
        qtbl_name_and_index = (uu___1762_23875.qtbl_name_and_index);
        normalized_eff_names = (uu___1762_23875.normalized_eff_names);
        fv_delta_depths = (uu___1762_23875.fv_delta_depths);
        proof_ns = (uu___1762_23875.proof_ns);
        synth_hook = (uu___1762_23875.synth_hook);
        try_solve_implicits_hook = (uu___1762_23875.try_solve_implicits_hook);
        splice = (uu___1762_23875.splice);
        postprocess = (uu___1762_23875.postprocess);
        is_native_tactic = (uu___1762_23875.is_native_tactic);
        identifier_info = (uu___1762_23875.identifier_info);
        tc_hooks = (uu___1762_23875.tc_hooks);
        dsenv = (uu___1762_23875.dsenv);
        nbe = (uu___1762_23875.nbe);
        strict_args_tab = (uu___1762_23875.strict_args_tab)
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
            (let uu___1775_23933 = env  in
             {
               solver = (uu___1775_23933.solver);
               range = (uu___1775_23933.range);
               curmodule = (uu___1775_23933.curmodule);
               gamma = rest;
               gamma_sig = (uu___1775_23933.gamma_sig);
               gamma_cache = (uu___1775_23933.gamma_cache);
               modules = (uu___1775_23933.modules);
               expected_typ = (uu___1775_23933.expected_typ);
               sigtab = (uu___1775_23933.sigtab);
               attrtab = (uu___1775_23933.attrtab);
               is_pattern = (uu___1775_23933.is_pattern);
               instantiate_imp = (uu___1775_23933.instantiate_imp);
               effects = (uu___1775_23933.effects);
               generalize = (uu___1775_23933.generalize);
               letrecs = (uu___1775_23933.letrecs);
               top_level = (uu___1775_23933.top_level);
               check_uvars = (uu___1775_23933.check_uvars);
               use_eq = (uu___1775_23933.use_eq);
               is_iface = (uu___1775_23933.is_iface);
               admit = (uu___1775_23933.admit);
               lax = (uu___1775_23933.lax);
               lax_universes = (uu___1775_23933.lax_universes);
               phase1 = (uu___1775_23933.phase1);
               failhard = (uu___1775_23933.failhard);
               nosynth = (uu___1775_23933.nosynth);
               uvar_subtyping = (uu___1775_23933.uvar_subtyping);
               tc_term = (uu___1775_23933.tc_term);
               type_of = (uu___1775_23933.type_of);
               universe_of = (uu___1775_23933.universe_of);
               check_type_of = (uu___1775_23933.check_type_of);
               use_bv_sorts = (uu___1775_23933.use_bv_sorts);
               qtbl_name_and_index = (uu___1775_23933.qtbl_name_and_index);
               normalized_eff_names = (uu___1775_23933.normalized_eff_names);
               fv_delta_depths = (uu___1775_23933.fv_delta_depths);
               proof_ns = (uu___1775_23933.proof_ns);
               synth_hook = (uu___1775_23933.synth_hook);
               try_solve_implicits_hook =
                 (uu___1775_23933.try_solve_implicits_hook);
               splice = (uu___1775_23933.splice);
               postprocess = (uu___1775_23933.postprocess);
               is_native_tactic = (uu___1775_23933.is_native_tactic);
               identifier_info = (uu___1775_23933.identifier_info);
               tc_hooks = (uu___1775_23933.tc_hooks);
               dsenv = (uu___1775_23933.dsenv);
               nbe = (uu___1775_23933.nbe);
               strict_args_tab = (uu___1775_23933.strict_args_tab)
             }))
    | uu____23934 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____23963  ->
             match uu____23963 with | (x,uu____23971) -> push_bv env1 x) env
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
            let uu___1789_24006 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1789_24006.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1789_24006.FStar_Syntax_Syntax.index);
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
      (let uu___1800_24048 = env  in
       {
         solver = (uu___1800_24048.solver);
         range = (uu___1800_24048.range);
         curmodule = (uu___1800_24048.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1800_24048.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1800_24048.sigtab);
         attrtab = (uu___1800_24048.attrtab);
         is_pattern = (uu___1800_24048.is_pattern);
         instantiate_imp = (uu___1800_24048.instantiate_imp);
         effects = (uu___1800_24048.effects);
         generalize = (uu___1800_24048.generalize);
         letrecs = (uu___1800_24048.letrecs);
         top_level = (uu___1800_24048.top_level);
         check_uvars = (uu___1800_24048.check_uvars);
         use_eq = (uu___1800_24048.use_eq);
         is_iface = (uu___1800_24048.is_iface);
         admit = (uu___1800_24048.admit);
         lax = (uu___1800_24048.lax);
         lax_universes = (uu___1800_24048.lax_universes);
         phase1 = (uu___1800_24048.phase1);
         failhard = (uu___1800_24048.failhard);
         nosynth = (uu___1800_24048.nosynth);
         uvar_subtyping = (uu___1800_24048.uvar_subtyping);
         tc_term = (uu___1800_24048.tc_term);
         type_of = (uu___1800_24048.type_of);
         universe_of = (uu___1800_24048.universe_of);
         check_type_of = (uu___1800_24048.check_type_of);
         use_bv_sorts = (uu___1800_24048.use_bv_sorts);
         qtbl_name_and_index = (uu___1800_24048.qtbl_name_and_index);
         normalized_eff_names = (uu___1800_24048.normalized_eff_names);
         fv_delta_depths = (uu___1800_24048.fv_delta_depths);
         proof_ns = (uu___1800_24048.proof_ns);
         synth_hook = (uu___1800_24048.synth_hook);
         try_solve_implicits_hook =
           (uu___1800_24048.try_solve_implicits_hook);
         splice = (uu___1800_24048.splice);
         postprocess = (uu___1800_24048.postprocess);
         is_native_tactic = (uu___1800_24048.is_native_tactic);
         identifier_info = (uu___1800_24048.identifier_info);
         tc_hooks = (uu___1800_24048.tc_hooks);
         dsenv = (uu___1800_24048.dsenv);
         nbe = (uu___1800_24048.nbe);
         strict_args_tab = (uu___1800_24048.strict_args_tab)
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
        let uu____24092 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____24092 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____24120 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____24120)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1815_24136 = env  in
      {
        solver = (uu___1815_24136.solver);
        range = (uu___1815_24136.range);
        curmodule = (uu___1815_24136.curmodule);
        gamma = (uu___1815_24136.gamma);
        gamma_sig = (uu___1815_24136.gamma_sig);
        gamma_cache = (uu___1815_24136.gamma_cache);
        modules = (uu___1815_24136.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1815_24136.sigtab);
        attrtab = (uu___1815_24136.attrtab);
        is_pattern = (uu___1815_24136.is_pattern);
        instantiate_imp = (uu___1815_24136.instantiate_imp);
        effects = (uu___1815_24136.effects);
        generalize = (uu___1815_24136.generalize);
        letrecs = (uu___1815_24136.letrecs);
        top_level = (uu___1815_24136.top_level);
        check_uvars = (uu___1815_24136.check_uvars);
        use_eq = false;
        is_iface = (uu___1815_24136.is_iface);
        admit = (uu___1815_24136.admit);
        lax = (uu___1815_24136.lax);
        lax_universes = (uu___1815_24136.lax_universes);
        phase1 = (uu___1815_24136.phase1);
        failhard = (uu___1815_24136.failhard);
        nosynth = (uu___1815_24136.nosynth);
        uvar_subtyping = (uu___1815_24136.uvar_subtyping);
        tc_term = (uu___1815_24136.tc_term);
        type_of = (uu___1815_24136.type_of);
        universe_of = (uu___1815_24136.universe_of);
        check_type_of = (uu___1815_24136.check_type_of);
        use_bv_sorts = (uu___1815_24136.use_bv_sorts);
        qtbl_name_and_index = (uu___1815_24136.qtbl_name_and_index);
        normalized_eff_names = (uu___1815_24136.normalized_eff_names);
        fv_delta_depths = (uu___1815_24136.fv_delta_depths);
        proof_ns = (uu___1815_24136.proof_ns);
        synth_hook = (uu___1815_24136.synth_hook);
        try_solve_implicits_hook = (uu___1815_24136.try_solve_implicits_hook);
        splice = (uu___1815_24136.splice);
        postprocess = (uu___1815_24136.postprocess);
        is_native_tactic = (uu___1815_24136.is_native_tactic);
        identifier_info = (uu___1815_24136.identifier_info);
        tc_hooks = (uu___1815_24136.tc_hooks);
        dsenv = (uu___1815_24136.dsenv);
        nbe = (uu___1815_24136.nbe);
        strict_args_tab = (uu___1815_24136.strict_args_tab)
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
    let uu____24167 = expected_typ env_  in
    ((let uu___1822_24173 = env_  in
      {
        solver = (uu___1822_24173.solver);
        range = (uu___1822_24173.range);
        curmodule = (uu___1822_24173.curmodule);
        gamma = (uu___1822_24173.gamma);
        gamma_sig = (uu___1822_24173.gamma_sig);
        gamma_cache = (uu___1822_24173.gamma_cache);
        modules = (uu___1822_24173.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1822_24173.sigtab);
        attrtab = (uu___1822_24173.attrtab);
        is_pattern = (uu___1822_24173.is_pattern);
        instantiate_imp = (uu___1822_24173.instantiate_imp);
        effects = (uu___1822_24173.effects);
        generalize = (uu___1822_24173.generalize);
        letrecs = (uu___1822_24173.letrecs);
        top_level = (uu___1822_24173.top_level);
        check_uvars = (uu___1822_24173.check_uvars);
        use_eq = false;
        is_iface = (uu___1822_24173.is_iface);
        admit = (uu___1822_24173.admit);
        lax = (uu___1822_24173.lax);
        lax_universes = (uu___1822_24173.lax_universes);
        phase1 = (uu___1822_24173.phase1);
        failhard = (uu___1822_24173.failhard);
        nosynth = (uu___1822_24173.nosynth);
        uvar_subtyping = (uu___1822_24173.uvar_subtyping);
        tc_term = (uu___1822_24173.tc_term);
        type_of = (uu___1822_24173.type_of);
        universe_of = (uu___1822_24173.universe_of);
        check_type_of = (uu___1822_24173.check_type_of);
        use_bv_sorts = (uu___1822_24173.use_bv_sorts);
        qtbl_name_and_index = (uu___1822_24173.qtbl_name_and_index);
        normalized_eff_names = (uu___1822_24173.normalized_eff_names);
        fv_delta_depths = (uu___1822_24173.fv_delta_depths);
        proof_ns = (uu___1822_24173.proof_ns);
        synth_hook = (uu___1822_24173.synth_hook);
        try_solve_implicits_hook = (uu___1822_24173.try_solve_implicits_hook);
        splice = (uu___1822_24173.splice);
        postprocess = (uu___1822_24173.postprocess);
        is_native_tactic = (uu___1822_24173.is_native_tactic);
        identifier_info = (uu___1822_24173.identifier_info);
        tc_hooks = (uu___1822_24173.tc_hooks);
        dsenv = (uu___1822_24173.dsenv);
        nbe = (uu___1822_24173.nbe);
        strict_args_tab = (uu___1822_24173.strict_args_tab)
      }), uu____24167)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____24185 =
      let uu____24188 = FStar_Ident.id_of_text ""  in [uu____24188]  in
    FStar_Ident.lid_of_ids uu____24185  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____24195 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____24195
        then
          let uu____24200 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____24200 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1830_24228 = env  in
       {
         solver = (uu___1830_24228.solver);
         range = (uu___1830_24228.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1830_24228.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1830_24228.expected_typ);
         sigtab = (uu___1830_24228.sigtab);
         attrtab = (uu___1830_24228.attrtab);
         is_pattern = (uu___1830_24228.is_pattern);
         instantiate_imp = (uu___1830_24228.instantiate_imp);
         effects = (uu___1830_24228.effects);
         generalize = (uu___1830_24228.generalize);
         letrecs = (uu___1830_24228.letrecs);
         top_level = (uu___1830_24228.top_level);
         check_uvars = (uu___1830_24228.check_uvars);
         use_eq = (uu___1830_24228.use_eq);
         is_iface = (uu___1830_24228.is_iface);
         admit = (uu___1830_24228.admit);
         lax = (uu___1830_24228.lax);
         lax_universes = (uu___1830_24228.lax_universes);
         phase1 = (uu___1830_24228.phase1);
         failhard = (uu___1830_24228.failhard);
         nosynth = (uu___1830_24228.nosynth);
         uvar_subtyping = (uu___1830_24228.uvar_subtyping);
         tc_term = (uu___1830_24228.tc_term);
         type_of = (uu___1830_24228.type_of);
         universe_of = (uu___1830_24228.universe_of);
         check_type_of = (uu___1830_24228.check_type_of);
         use_bv_sorts = (uu___1830_24228.use_bv_sorts);
         qtbl_name_and_index = (uu___1830_24228.qtbl_name_and_index);
         normalized_eff_names = (uu___1830_24228.normalized_eff_names);
         fv_delta_depths = (uu___1830_24228.fv_delta_depths);
         proof_ns = (uu___1830_24228.proof_ns);
         synth_hook = (uu___1830_24228.synth_hook);
         try_solve_implicits_hook =
           (uu___1830_24228.try_solve_implicits_hook);
         splice = (uu___1830_24228.splice);
         postprocess = (uu___1830_24228.postprocess);
         is_native_tactic = (uu___1830_24228.is_native_tactic);
         identifier_info = (uu___1830_24228.identifier_info);
         tc_hooks = (uu___1830_24228.tc_hooks);
         dsenv = (uu___1830_24228.dsenv);
         nbe = (uu___1830_24228.nbe);
         strict_args_tab = (uu___1830_24228.strict_args_tab)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24280)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24284,(uu____24285,t)))::tl1
          ->
          let uu____24306 =
            let uu____24309 = FStar_Syntax_Free.uvars t  in
            ext out uu____24309  in
          aux uu____24306 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24312;
            FStar_Syntax_Syntax.index = uu____24313;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24321 =
            let uu____24324 = FStar_Syntax_Free.uvars t  in
            ext out uu____24324  in
          aux uu____24321 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____24382)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24386,(uu____24387,t)))::tl1
          ->
          let uu____24408 =
            let uu____24411 = FStar_Syntax_Free.univs t  in
            ext out uu____24411  in
          aux uu____24408 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24414;
            FStar_Syntax_Syntax.index = uu____24415;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24423 =
            let uu____24426 = FStar_Syntax_Free.univs t  in
            ext out uu____24426  in
          aux uu____24423 tl1
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
          let uu____24488 = FStar_Util.set_add uname out  in
          aux uu____24488 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____24491,(uu____24492,t)))::tl1
          ->
          let uu____24513 =
            let uu____24516 = FStar_Syntax_Free.univnames t  in
            ext out uu____24516  in
          aux uu____24513 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____24519;
            FStar_Syntax_Syntax.index = uu____24520;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____24528 =
            let uu____24531 = FStar_Syntax_Free.univnames t  in
            ext out uu____24531  in
          aux uu____24528 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___11_24552  ->
            match uu___11_24552 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____24556 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____24569 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____24580 =
      let uu____24589 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____24589
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____24580 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____24637 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___12_24650  ->
              match uu___12_24650 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____24653 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____24653
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____24659) ->
                  let uu____24676 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____24676))
       in
    FStar_All.pipe_right uu____24637 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___13_24690  ->
    match uu___13_24690 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____24696 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____24696
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____24719  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____24774) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____24807,uu____24808) -> false  in
      let uu____24822 =
        FStar_List.tryFind
          (fun uu____24844  ->
             match uu____24844 with | (p,uu____24855) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____24822 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____24874,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____24904 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____24904
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1973_24926 = e  in
        {
          solver = (uu___1973_24926.solver);
          range = (uu___1973_24926.range);
          curmodule = (uu___1973_24926.curmodule);
          gamma = (uu___1973_24926.gamma);
          gamma_sig = (uu___1973_24926.gamma_sig);
          gamma_cache = (uu___1973_24926.gamma_cache);
          modules = (uu___1973_24926.modules);
          expected_typ = (uu___1973_24926.expected_typ);
          sigtab = (uu___1973_24926.sigtab);
          attrtab = (uu___1973_24926.attrtab);
          is_pattern = (uu___1973_24926.is_pattern);
          instantiate_imp = (uu___1973_24926.instantiate_imp);
          effects = (uu___1973_24926.effects);
          generalize = (uu___1973_24926.generalize);
          letrecs = (uu___1973_24926.letrecs);
          top_level = (uu___1973_24926.top_level);
          check_uvars = (uu___1973_24926.check_uvars);
          use_eq = (uu___1973_24926.use_eq);
          is_iface = (uu___1973_24926.is_iface);
          admit = (uu___1973_24926.admit);
          lax = (uu___1973_24926.lax);
          lax_universes = (uu___1973_24926.lax_universes);
          phase1 = (uu___1973_24926.phase1);
          failhard = (uu___1973_24926.failhard);
          nosynth = (uu___1973_24926.nosynth);
          uvar_subtyping = (uu___1973_24926.uvar_subtyping);
          tc_term = (uu___1973_24926.tc_term);
          type_of = (uu___1973_24926.type_of);
          universe_of = (uu___1973_24926.universe_of);
          check_type_of = (uu___1973_24926.check_type_of);
          use_bv_sorts = (uu___1973_24926.use_bv_sorts);
          qtbl_name_and_index = (uu___1973_24926.qtbl_name_and_index);
          normalized_eff_names = (uu___1973_24926.normalized_eff_names);
          fv_delta_depths = (uu___1973_24926.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1973_24926.synth_hook);
          try_solve_implicits_hook =
            (uu___1973_24926.try_solve_implicits_hook);
          splice = (uu___1973_24926.splice);
          postprocess = (uu___1973_24926.postprocess);
          is_native_tactic = (uu___1973_24926.is_native_tactic);
          identifier_info = (uu___1973_24926.identifier_info);
          tc_hooks = (uu___1973_24926.tc_hooks);
          dsenv = (uu___1973_24926.dsenv);
          nbe = (uu___1973_24926.nbe);
          strict_args_tab = (uu___1973_24926.strict_args_tab)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1982_24974 = e  in
      {
        solver = (uu___1982_24974.solver);
        range = (uu___1982_24974.range);
        curmodule = (uu___1982_24974.curmodule);
        gamma = (uu___1982_24974.gamma);
        gamma_sig = (uu___1982_24974.gamma_sig);
        gamma_cache = (uu___1982_24974.gamma_cache);
        modules = (uu___1982_24974.modules);
        expected_typ = (uu___1982_24974.expected_typ);
        sigtab = (uu___1982_24974.sigtab);
        attrtab = (uu___1982_24974.attrtab);
        is_pattern = (uu___1982_24974.is_pattern);
        instantiate_imp = (uu___1982_24974.instantiate_imp);
        effects = (uu___1982_24974.effects);
        generalize = (uu___1982_24974.generalize);
        letrecs = (uu___1982_24974.letrecs);
        top_level = (uu___1982_24974.top_level);
        check_uvars = (uu___1982_24974.check_uvars);
        use_eq = (uu___1982_24974.use_eq);
        is_iface = (uu___1982_24974.is_iface);
        admit = (uu___1982_24974.admit);
        lax = (uu___1982_24974.lax);
        lax_universes = (uu___1982_24974.lax_universes);
        phase1 = (uu___1982_24974.phase1);
        failhard = (uu___1982_24974.failhard);
        nosynth = (uu___1982_24974.nosynth);
        uvar_subtyping = (uu___1982_24974.uvar_subtyping);
        tc_term = (uu___1982_24974.tc_term);
        type_of = (uu___1982_24974.type_of);
        universe_of = (uu___1982_24974.universe_of);
        check_type_of = (uu___1982_24974.check_type_of);
        use_bv_sorts = (uu___1982_24974.use_bv_sorts);
        qtbl_name_and_index = (uu___1982_24974.qtbl_name_and_index);
        normalized_eff_names = (uu___1982_24974.normalized_eff_names);
        fv_delta_depths = (uu___1982_24974.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1982_24974.synth_hook);
        try_solve_implicits_hook = (uu___1982_24974.try_solve_implicits_hook);
        splice = (uu___1982_24974.splice);
        postprocess = (uu___1982_24974.postprocess);
        is_native_tactic = (uu___1982_24974.is_native_tactic);
        identifier_info = (uu___1982_24974.identifier_info);
        tc_hooks = (uu___1982_24974.tc_hooks);
        dsenv = (uu___1982_24974.dsenv);
        nbe = (uu___1982_24974.nbe);
        strict_args_tab = (uu___1982_24974.strict_args_tab)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24990 = FStar_Syntax_Free.names t  in
      let uu____24993 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24990 uu____24993
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____25016 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____25016
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____25026 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____25026
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____25047 =
      match uu____25047 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____25067 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____25067)
       in
    let uu____25075 =
      let uu____25079 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____25079 FStar_List.rev  in
    FStar_All.pipe_right uu____25075 (FStar_String.concat " ")
  
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
                  (let uu____25147 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____25147 with
                   | FStar_Pervasives_Native.Some uu____25151 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____25154 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Common.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Common.deferred = uu____25164;
        FStar_TypeChecker_Common.univ_ineqs = uu____25165;
        FStar_TypeChecker_Common.implicits = uu____25166;_} -> true
    | uu____25176 -> false
  
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
          let uu___2026_25198 = g  in
          {
            FStar_TypeChecker_Common.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Common.deferred =
              (uu___2026_25198.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2026_25198.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2026_25198.FStar_TypeChecker_Common.implicits)
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
          let uu____25237 = FStar_Options.defensive ()  in
          if uu____25237
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____25243 =
              let uu____25245 =
                let uu____25247 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____25247  in
              Prims.op_Negation uu____25245  in
            (if uu____25243
             then
               let uu____25254 =
                 let uu____25260 =
                   let uu____25262 = FStar_Syntax_Print.term_to_string t  in
                   let uu____25264 =
                     let uu____25266 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____25266
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____25262 uu____25264
                    in
                 (FStar_Errors.Warning_Defensive, uu____25260)  in
               FStar_Errors.log_issue rng uu____25254
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
          let uu____25306 =
            let uu____25308 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25308  in
          if uu____25306
          then ()
          else
            (let uu____25313 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____25313 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____25339 =
            let uu____25341 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____25341  in
          if uu____25339
          then ()
          else
            (let uu____25346 = bound_vars e  in
             def_check_closed_in rng msg uu____25346 t)
  
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
          let uu___2063_25385 = g  in
          let uu____25386 =
            let uu____25387 =
              let uu____25388 =
                let uu____25395 =
                  let uu____25396 =
                    let uu____25413 =
                      let uu____25424 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____25424]  in
                    (f, uu____25413)  in
                  FStar_Syntax_Syntax.Tm_app uu____25396  in
                FStar_Syntax_Syntax.mk uu____25395  in
              uu____25388 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _25461  -> FStar_TypeChecker_Common.NonTrivial _25461)
              uu____25387
             in
          {
            FStar_TypeChecker_Common.guard_f = uu____25386;
            FStar_TypeChecker_Common.deferred =
              (uu___2063_25385.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2063_25385.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2063_25385.FStar_TypeChecker_Common.implicits)
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
          let uu___2070_25479 = g  in
          let uu____25480 =
            let uu____25481 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25481  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25480;
            FStar_TypeChecker_Common.deferred =
              (uu___2070_25479.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2070_25479.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2070_25479.FStar_TypeChecker_Common.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2075_25498 = g  in
          let uu____25499 =
            let uu____25500 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____25500  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25499;
            FStar_TypeChecker_Common.deferred =
              (uu___2075_25498.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2075_25498.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2075_25498.FStar_TypeChecker_Common.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2079_25502 = g  in
          let uu____25503 =
            let uu____25504 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____25504  in
          {
            FStar_TypeChecker_Common.guard_f = uu____25503;
            FStar_TypeChecker_Common.deferred =
              (uu___2079_25502.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___2079_25502.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits =
              (uu___2079_25502.FStar_TypeChecker_Common.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____25511 ->
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
          let uu____25528 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____25528
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____25535 =
      let uu____25536 = FStar_Syntax_Util.unmeta t  in
      uu____25536.FStar_Syntax_Syntax.n  in
    match uu____25535 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____25540 -> FStar_TypeChecker_Common.NonTrivial t
  
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
    ->
    FStar_TypeChecker_Common.guard_t ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____25583 =
          f g1.FStar_TypeChecker_Common.guard_f
            g2.FStar_TypeChecker_Common.guard_f
           in
        {
          FStar_TypeChecker_Common.guard_f = uu____25583;
          FStar_TypeChecker_Common.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Common.deferred
               g2.FStar_TypeChecker_Common.deferred);
          FStar_TypeChecker_Common.univ_ineqs =
            ((FStar_List.append
                (FStar_Pervasives_Native.fst
                   g1.FStar_TypeChecker_Common.univ_ineqs)
                (FStar_Pervasives_Native.fst
                   g2.FStar_TypeChecker_Common.univ_ineqs)),
              (FStar_List.append
                 (FStar_Pervasives_Native.snd
                    g1.FStar_TypeChecker_Common.univ_ineqs)
                 (FStar_Pervasives_Native.snd
                    g2.FStar_TypeChecker_Common.univ_ineqs)));
          FStar_TypeChecker_Common.implicits =
            (FStar_List.append g1.FStar_TypeChecker_Common.implicits
               g2.FStar_TypeChecker_Common.implicits)
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
        match g.FStar_TypeChecker_Common.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____25678 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____25678
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2134_25685 = g  in
            {
              FStar_TypeChecker_Common.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Common.deferred =
                (uu___2134_25685.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2134_25685.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2134_25685.FStar_TypeChecker_Common.implicits)
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
               let uu____25719 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____25719
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
            let uu___2149_25746 = g  in
            let uu____25747 =
              let uu____25748 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____25748  in
            {
              FStar_TypeChecker_Common.guard_f = uu____25747;
              FStar_TypeChecker_Common.deferred =
                (uu___2149_25746.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___2149_25746.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___2149_25746.FStar_TypeChecker_Common.implicits)
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
              let uu____25806 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____25806 with
              | FStar_Pervasives_Native.Some
                  (uu____25831::(tm,uu____25833)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____25897 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____25915 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____25915;
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
                      let uu___2171_25947 = trivial_guard  in
                      {
                        FStar_TypeChecker_Common.guard_f =
                          (uu___2171_25947.FStar_TypeChecker_Common.guard_f);
                        FStar_TypeChecker_Common.deferred =
                          (uu___2171_25947.FStar_TypeChecker_Common.deferred);
                        FStar_TypeChecker_Common.univ_ineqs =
                          (uu___2171_25947.FStar_TypeChecker_Common.univ_ineqs);
                        FStar_TypeChecker_Common.implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (lift_to_layered_effect :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Ident.lident -> (FStar_Syntax_Syntax.comp * guard_t))
  =
  fun env  ->
    fun c  ->
      fun eff_name  ->
        (let uu____25987 =
           FStar_All.pipe_left (debug env)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____25987
         then
           let uu____25992 = FStar_Syntax_Print.comp_to_string c  in
           let uu____25994 = FStar_Syntax_Print.lid_to_string eff_name  in
           FStar_Util.print2 "Lifting comp %s to layered effect %s {\n"
             uu____25992 uu____25994
         else ());
        (let ct = unfold_effect_abbrev env c  in
         let uu____26000 =
           FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name eff_name
            in
         if uu____26000
         then (c, trivial_guard)
         else
           (let src_ed =
              get_effect_decl env ct.FStar_Syntax_Syntax.effect_name  in
            let dst_ed = get_effect_decl env eff_name  in
            if
              src_ed.FStar_Syntax_Syntax.is_layered ||
                (Prims.op_Negation dst_ed.FStar_Syntax_Syntax.is_layered)
            then
              failwith
                "lift_to_layered_effect called with layered src or non-layered dst"
            else ();
            (let lift_t =
               let uu____26017 =
                 monad_leq env src_ed.FStar_Syntax_Syntax.mname
                   dst_ed.FStar_Syntax_Syntax.mname
                  in
               match uu____26017 with
               | FStar_Pervasives_Native.None  ->
                   failwith
                     (Prims.op_Hat "Could not find an edge from "
                        (Prims.op_Hat
                           (src_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                           (Prims.op_Hat " to "
                              (dst_ed.FStar_Syntax_Syntax.mname).FStar_Ident.str)))
               | FStar_Pervasives_Native.Some lift ->
                   FStar_All.pipe_right (lift.mlift).mlift_t FStar_Util.must
                in
             let uu____26025 = FStar_Syntax_Util.destruct_comp ct  in
             match uu____26025 with
             | (u,a,wp) ->
                 let uu____26039 = inst_tscheme_with lift_t [u]  in
                 (match uu____26039 with
                  | (uu____26048,lift_t1) ->
                      let uu____26050 =
                        let uu____26063 =
                          let uu____26064 =
                            FStar_Syntax_Subst.compress lift_t1  in
                          uu____26064.FStar_Syntax_Syntax.n  in
                        match uu____26063 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs,c1) ->
                            let uu____26101 =
                              FStar_Syntax_Subst.open_comp bs c1  in
                            FStar_All.pipe_right uu____26101
                              (fun uu____26118  ->
                                 match uu____26118 with
                                 | (bs1,c2) ->
                                     let uu____26129 =
                                       FStar_Syntax_Util.comp_to_comp_typ c2
                                        in
                                     (bs1, uu____26129))
                        | uu____26130 ->
                            let uu____26131 =
                              let uu____26133 =
                                let uu____26135 =
                                  FStar_Syntax_Print.term_to_string lift_t1
                                   in
                                Prims.op_Hat uu____26135
                                  " is not an arrow type"
                                 in
                              Prims.op_Hat "lift_t: " uu____26133  in
                            failwith uu____26131
                         in
                      (match uu____26050 with
                       | (lift_bs,lift_ct) ->
                           let uu____26173 =
                             match lift_bs with
                             | a_b::wp_b::bs when
                                 (FStar_List.length bs) >= Prims.int_one ->
                                 let uu____26252 =
                                   let uu____26253 =
                                     FStar_List.splitAt
                                       ((FStar_List.length bs) -
                                          Prims.int_one) bs
                                      in
                                   FStar_All.pipe_right uu____26253
                                     FStar_Pervasives_Native.fst
                                    in
                                 (a_b, wp_b, uu____26252)
                             | uu____26311 ->
                                 let uu____26320 =
                                   let uu____26322 =
                                     let uu____26324 =
                                       FStar_Syntax_Print.term_to_string
                                         lift_t1
                                        in
                                     Prims.op_Hat uu____26324
                                       " does not have enough binders"
                                      in
                                   Prims.op_Hat "lift_t: " uu____26322  in
                                 failwith uu____26320
                              in
                           (match uu____26173 with
                            | (a_b,wp_b,rest_bs) ->
                                let rest_bs1 =
                                  let uu____26378 =
                                    let uu____26381 =
                                      let uu____26382 =
                                        let uu____26389 =
                                          FStar_All.pipe_right a_b
                                            FStar_Pervasives_Native.fst
                                           in
                                        (uu____26389, a)  in
                                      FStar_Syntax_Syntax.NT uu____26382  in
                                    let uu____26400 =
                                      let uu____26403 =
                                        let uu____26404 =
                                          let uu____26411 =
                                            FStar_All.pipe_right wp_b
                                              FStar_Pervasives_Native.fst
                                             in
                                          (uu____26411, wp)  in
                                        FStar_Syntax_Syntax.NT uu____26404
                                         in
                                      [uu____26403]  in
                                    uu____26381 :: uu____26400  in
                                  FStar_Syntax_Subst.subst_binders
                                    uu____26378 rest_bs
                                   in
                                let uu____26422 =
                                  let uu____26429 =
                                    let uu____26430 =
                                      FStar_Syntax_Subst.compress
                                        lift_ct.FStar_Syntax_Syntax.result_typ
                                       in
                                    uu____26430.FStar_Syntax_Syntax.n  in
                                  match uu____26429 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____26439,uu____26440::is) ->
                                      let uu____26482 =
                                        FStar_List.map
                                          FStar_Pervasives_Native.fst is
                                         in
                                      ((lift_ct.FStar_Syntax_Syntax.comp_univs),
                                        uu____26482)
                                  | uu____26499 ->
                                      let uu____26500 =
                                        let uu____26502 =
                                          let uu____26504 =
                                            FStar_Syntax_Print.term_to_string
                                              lift_t1
                                             in
                                          Prims.op_Hat uu____26504
                                            " does not have a repr return type"
                                           in
                                        Prims.op_Hat "lift_t: " uu____26502
                                         in
                                      failwith uu____26500
                                   in
                                (match uu____26422 with
                                 | (u_m,is) ->
                                     let uu____26524 =
                                       let uu____26533 =
                                         FStar_List.fold_left
                                           (fun uu____26573  ->
                                              fun b  ->
                                                match uu____26573 with
                                                | (substs,is_uvars,g) ->
                                                    let sort =
                                                      FStar_Syntax_Subst.subst
                                                        substs
                                                        (FStar_Pervasives_Native.fst
                                                           b).FStar_Syntax_Syntax.sort
                                                       in
                                                    let uu____26615 =
                                                      new_implicit_var_aux ""
                                                        FStar_Range.dummyRange
                                                        env sort
                                                        FStar_Syntax_Syntax.Strict
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    (match uu____26615 with
                                                     | (t,uu____26644,g_t) ->
                                                         ((let uu____26659 =
                                                             FStar_All.pipe_left
                                                               (debug env)
                                                               (FStar_Options.Other
                                                                  "LayeredEffects")
                                                              in
                                                           if uu____26659
                                                           then
                                                             let uu____26664
                                                               =
                                                               FStar_Syntax_Print.term_to_string
                                                                 t
                                                                in
                                                             let uu____26666
                                                               =
                                                               FStar_Syntax_Print.binder_to_string
                                                                 b
                                                                in
                                                             FStar_Util.print2
                                                               "lift_to_layered_effect: introduced uvar %s for binder %s\n"
                                                               uu____26664
                                                               uu____26666
                                                           else ());
                                                          (let uu____26671 =
                                                             let uu____26674
                                                               =
                                                               let uu____26677
                                                                 =
                                                                 let uu____26678
                                                                   =
                                                                   let uu____26685
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    b
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                   (uu____26685,
                                                                    t)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____26678
                                                                  in
                                                               [uu____26677]
                                                                in
                                                             FStar_List.append
                                                               substs
                                                               uu____26674
                                                              in
                                                           let uu____26696 =
                                                             conj_guard g g_t
                                                              in
                                                           (uu____26671,
                                                             (FStar_List.append
                                                                is_uvars 
                                                                [t]),
                                                             uu____26696)))))
                                           ([], [], trivial_guard) rest_bs1
                                          in
                                       match uu____26533 with
                                       | (uu____26713,rest_bs_uvars,g) ->
                                           (rest_bs_uvars, g)
                                        in
                                     (match uu____26524 with
                                      | (rest_bs_uvars,g) ->
                                          let subst_for_is =
                                            FStar_List.map2
                                              (fun b  ->
                                                 fun t  ->
                                                   let uu____26766 =
                                                     let uu____26773 =
                                                       FStar_All.pipe_right b
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     (uu____26773, t)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____26766) (a_b ::
                                              wp_b :: rest_bs1) (a :: wp ::
                                              rest_bs_uvars)
                                             in
                                          let is1 =
                                            FStar_List.map
                                              (FStar_Syntax_Subst.subst
                                                 subst_for_is) is
                                             in
                                          let c1 =
                                            let uu____26804 =
                                              let uu____26805 =
                                                FStar_List.map
                                                  FStar_Syntax_Syntax.as_arg
                                                  is1
                                                 in
                                              {
                                                FStar_Syntax_Syntax.comp_univs
                                                  = u_m;
                                                FStar_Syntax_Syntax.effect_name
                                                  = eff_name;
                                                FStar_Syntax_Syntax.result_typ
                                                  = a;
                                                FStar_Syntax_Syntax.effect_args
                                                  = uu____26805;
                                                FStar_Syntax_Syntax.flags =
                                                  []
                                              }  in
                                            FStar_Syntax_Syntax.mk_Comp
                                              uu____26804
                                             in
                                          ((let uu____26825 =
                                              FStar_All.pipe_left (debug env)
                                                (FStar_Options.Other
                                                   "LayeredEffects")
                                               in
                                            if uu____26825
                                            then
                                              let uu____26830 =
                                                FStar_Syntax_Print.comp_to_string
                                                  c1
                                                 in
                                              FStar_Util.print1
                                                "} Lifted comp: %s\n"
                                                uu____26830
                                            else ());
                                           (c1, g))))))))))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____26838  -> ());
    push = (fun uu____26840  -> ());
    pop = (fun uu____26843  -> ());
    snapshot =
      (fun uu____26846  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    rollback = (fun uu____26865  -> fun uu____26866  -> ());
    encode_sig = (fun uu____26881  -> fun uu____26882  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____26888 =
             let uu____26895 = FStar_Options.peek ()  in (e, g, uu____26895)
              in
           [uu____26888]);
    solve = (fun uu____26911  -> fun uu____26912  -> fun uu____26913  -> ());
    finish = (fun uu____26920  -> ());
    refresh = (fun uu____26922  -> ())
  } 