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
  fun projectee  -> match projectee with | Beta  -> true | uu____40 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____51 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____62 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____74 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____93 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____104 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____115 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____126 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____137 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____148 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____160 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____182 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____210 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____238 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____263 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____274 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____285 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____296 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____307 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____318 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____329 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____340 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____351 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____362 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____373 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____384 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____395 -> false
  
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
      | uu____455 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____481 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____492 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____503 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____515 -> false
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> solver
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> range
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> curmodule
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> gamma
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> gamma_sig
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> gamma_cache
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> modules
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> expected_typ
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> sigtab
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> attrtab
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> is_pattern
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> instantiate_imp
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> effects
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> generalize
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> letrecs
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> top_level
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> check_uvars
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> use_eq
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> is_iface
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> admit1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> lax1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> lax_universes
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> phase1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> failhard
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> nosynth
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> uvar_subtyping
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> tc_term
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> type_of
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> universe_of
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> check_type_of
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> use_bv_sorts
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> qtbl_name_and_index
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> normalized_eff_names
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> fv_delta_depths
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> proof_ns
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> synth_hook
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> splice1
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> postprocess
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> is_native_tactic
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> identifier_info
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> tc_hooks
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> dsenv
  
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
        splice = splice1; postprocess; is_native_tactic; identifier_info;
        tc_hooks; dsenv; nbe = nbe1;_} -> nbe1
  
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
           (fun uu___1_11777  ->
              match uu___1_11777 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____11780 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____11780  in
                  let uu____11781 =
                    let uu____11782 = FStar_Syntax_Subst.compress y  in
                    uu____11782.FStar_Syntax_Syntax.n  in
                  (match uu____11781 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____11786 =
                         let uu___15_11787 = y1  in
                         let uu____11788 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___15_11787.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___15_11787.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____11788
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____11786
                   | uu____11791 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___16_11805 = env  in
      let uu____11806 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___16_11805.solver);
        range = (uu___16_11805.range);
        curmodule = (uu___16_11805.curmodule);
        gamma = uu____11806;
        gamma_sig = (uu___16_11805.gamma_sig);
        gamma_cache = (uu___16_11805.gamma_cache);
        modules = (uu___16_11805.modules);
        expected_typ = (uu___16_11805.expected_typ);
        sigtab = (uu___16_11805.sigtab);
        attrtab = (uu___16_11805.attrtab);
        is_pattern = (uu___16_11805.is_pattern);
        instantiate_imp = (uu___16_11805.instantiate_imp);
        effects = (uu___16_11805.effects);
        generalize = (uu___16_11805.generalize);
        letrecs = (uu___16_11805.letrecs);
        top_level = (uu___16_11805.top_level);
        check_uvars = (uu___16_11805.check_uvars);
        use_eq = (uu___16_11805.use_eq);
        is_iface = (uu___16_11805.is_iface);
        admit = (uu___16_11805.admit);
        lax = (uu___16_11805.lax);
        lax_universes = (uu___16_11805.lax_universes);
        phase1 = (uu___16_11805.phase1);
        failhard = (uu___16_11805.failhard);
        nosynth = (uu___16_11805.nosynth);
        uvar_subtyping = (uu___16_11805.uvar_subtyping);
        tc_term = (uu___16_11805.tc_term);
        type_of = (uu___16_11805.type_of);
        universe_of = (uu___16_11805.universe_of);
        check_type_of = (uu___16_11805.check_type_of);
        use_bv_sorts = (uu___16_11805.use_bv_sorts);
        qtbl_name_and_index = (uu___16_11805.qtbl_name_and_index);
        normalized_eff_names = (uu___16_11805.normalized_eff_names);
        fv_delta_depths = (uu___16_11805.fv_delta_depths);
        proof_ns = (uu___16_11805.proof_ns);
        synth_hook = (uu___16_11805.synth_hook);
        splice = (uu___16_11805.splice);
        postprocess = (uu___16_11805.postprocess);
        is_native_tactic = (uu___16_11805.is_native_tactic);
        identifier_info = (uu___16_11805.identifier_info);
        tc_hooks = (uu___16_11805.tc_hooks);
        dsenv = (uu___16_11805.dsenv);
        nbe = (uu___16_11805.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____11814  -> fun uu____11815  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___17_11837 = env  in
      {
        solver = (uu___17_11837.solver);
        range = (uu___17_11837.range);
        curmodule = (uu___17_11837.curmodule);
        gamma = (uu___17_11837.gamma);
        gamma_sig = (uu___17_11837.gamma_sig);
        gamma_cache = (uu___17_11837.gamma_cache);
        modules = (uu___17_11837.modules);
        expected_typ = (uu___17_11837.expected_typ);
        sigtab = (uu___17_11837.sigtab);
        attrtab = (uu___17_11837.attrtab);
        is_pattern = (uu___17_11837.is_pattern);
        instantiate_imp = (uu___17_11837.instantiate_imp);
        effects = (uu___17_11837.effects);
        generalize = (uu___17_11837.generalize);
        letrecs = (uu___17_11837.letrecs);
        top_level = (uu___17_11837.top_level);
        check_uvars = (uu___17_11837.check_uvars);
        use_eq = (uu___17_11837.use_eq);
        is_iface = (uu___17_11837.is_iface);
        admit = (uu___17_11837.admit);
        lax = (uu___17_11837.lax);
        lax_universes = (uu___17_11837.lax_universes);
        phase1 = (uu___17_11837.phase1);
        failhard = (uu___17_11837.failhard);
        nosynth = (uu___17_11837.nosynth);
        uvar_subtyping = (uu___17_11837.uvar_subtyping);
        tc_term = (uu___17_11837.tc_term);
        type_of = (uu___17_11837.type_of);
        universe_of = (uu___17_11837.universe_of);
        check_type_of = (uu___17_11837.check_type_of);
        use_bv_sorts = (uu___17_11837.use_bv_sorts);
        qtbl_name_and_index = (uu___17_11837.qtbl_name_and_index);
        normalized_eff_names = (uu___17_11837.normalized_eff_names);
        fv_delta_depths = (uu___17_11837.fv_delta_depths);
        proof_ns = (uu___17_11837.proof_ns);
        synth_hook = (uu___17_11837.synth_hook);
        splice = (uu___17_11837.splice);
        postprocess = (uu___17_11837.postprocess);
        is_native_tactic = (uu___17_11837.is_native_tactic);
        identifier_info = (uu___17_11837.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___17_11837.dsenv);
        nbe = (uu___17_11837.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___18_11849 = e  in
      let uu____11850 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___18_11849.solver);
        range = (uu___18_11849.range);
        curmodule = (uu___18_11849.curmodule);
        gamma = (uu___18_11849.gamma);
        gamma_sig = (uu___18_11849.gamma_sig);
        gamma_cache = (uu___18_11849.gamma_cache);
        modules = (uu___18_11849.modules);
        expected_typ = (uu___18_11849.expected_typ);
        sigtab = (uu___18_11849.sigtab);
        attrtab = (uu___18_11849.attrtab);
        is_pattern = (uu___18_11849.is_pattern);
        instantiate_imp = (uu___18_11849.instantiate_imp);
        effects = (uu___18_11849.effects);
        generalize = (uu___18_11849.generalize);
        letrecs = (uu___18_11849.letrecs);
        top_level = (uu___18_11849.top_level);
        check_uvars = (uu___18_11849.check_uvars);
        use_eq = (uu___18_11849.use_eq);
        is_iface = (uu___18_11849.is_iface);
        admit = (uu___18_11849.admit);
        lax = (uu___18_11849.lax);
        lax_universes = (uu___18_11849.lax_universes);
        phase1 = (uu___18_11849.phase1);
        failhard = (uu___18_11849.failhard);
        nosynth = (uu___18_11849.nosynth);
        uvar_subtyping = (uu___18_11849.uvar_subtyping);
        tc_term = (uu___18_11849.tc_term);
        type_of = (uu___18_11849.type_of);
        universe_of = (uu___18_11849.universe_of);
        check_type_of = (uu___18_11849.check_type_of);
        use_bv_sorts = (uu___18_11849.use_bv_sorts);
        qtbl_name_and_index = (uu___18_11849.qtbl_name_and_index);
        normalized_eff_names = (uu___18_11849.normalized_eff_names);
        fv_delta_depths = (uu___18_11849.fv_delta_depths);
        proof_ns = (uu___18_11849.proof_ns);
        synth_hook = (uu___18_11849.synth_hook);
        splice = (uu___18_11849.splice);
        postprocess = (uu___18_11849.postprocess);
        is_native_tactic = (uu___18_11849.is_native_tactic);
        identifier_info = (uu___18_11849.identifier_info);
        tc_hooks = (uu___18_11849.tc_hooks);
        dsenv = uu____11850;
        nbe = (uu___18_11849.nbe)
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
      | (NoDelta ,uu____11879) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____11882,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____11884,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____11887 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____11901 . unit -> 'Auu____11901 FStar_Util.smap =
  fun uu____11908  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____11914 . unit -> 'Auu____11914 FStar_Util.smap =
  fun uu____11921  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____12059 = new_gamma_cache ()  in
                  let uu____12062 = new_sigtab ()  in
                  let uu____12065 = new_sigtab ()  in
                  let uu____12072 =
                    let uu____12087 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12087, FStar_Pervasives_Native.None)  in
                  let uu____12108 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12112 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12116 = FStar_Options.using_facts_from ()  in
                  let uu____12117 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12120 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12059;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12062;
                    attrtab = uu____12065;
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
                    qtbl_name_and_index = uu____12072;
                    normalized_eff_names = uu____12108;
                    fv_delta_depths = uu____12112;
                    proof_ns = uu____12116;
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
                    is_native_tactic = (fun uu____12182  -> false);
                    identifier_info = uu____12117;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12120;
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
  fun uu____12294  ->
    let uu____12295 = FStar_ST.op_Bang query_indices  in
    match uu____12295 with
    | [] -> failwith "Empty query indices!"
    | uu____12350 ->
        let uu____12360 =
          let uu____12370 =
            let uu____12378 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12378  in
          let uu____12432 = FStar_ST.op_Bang query_indices  in uu____12370 ::
            uu____12432
           in
        FStar_ST.op_Colon_Equals query_indices uu____12360
  
let (pop_query_indices : unit -> unit) =
  fun uu____12528  ->
    let uu____12529 = FStar_ST.op_Bang query_indices  in
    match uu____12529 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____12656  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____12693  ->
    match uu____12693 with
    | (l,n1) ->
        let uu____12703 = FStar_ST.op_Bang query_indices  in
        (match uu____12703 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____12825 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____12848  ->
    let uu____12849 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____12849
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____12928 =
       let uu____12931 = FStar_ST.op_Bang stack  in env :: uu____12931  in
     FStar_ST.op_Colon_Equals stack uu____12928);
    (let uu___19_12980 = env  in
     let uu____12981 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____12984 = FStar_Util.smap_copy (sigtab env)  in
     let uu____12987 = FStar_Util.smap_copy (attrtab env)  in
     let uu____12994 =
       let uu____13009 =
         let uu____13013 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13013  in
       let uu____13045 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13009, uu____13045)  in
     let uu____13094 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13097 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13100 =
       let uu____13103 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13103  in
     {
       solver = (uu___19_12980.solver);
       range = (uu___19_12980.range);
       curmodule = (uu___19_12980.curmodule);
       gamma = (uu___19_12980.gamma);
       gamma_sig = (uu___19_12980.gamma_sig);
       gamma_cache = uu____12981;
       modules = (uu___19_12980.modules);
       expected_typ = (uu___19_12980.expected_typ);
       sigtab = uu____12984;
       attrtab = uu____12987;
       is_pattern = (uu___19_12980.is_pattern);
       instantiate_imp = (uu___19_12980.instantiate_imp);
       effects = (uu___19_12980.effects);
       generalize = (uu___19_12980.generalize);
       letrecs = (uu___19_12980.letrecs);
       top_level = (uu___19_12980.top_level);
       check_uvars = (uu___19_12980.check_uvars);
       use_eq = (uu___19_12980.use_eq);
       is_iface = (uu___19_12980.is_iface);
       admit = (uu___19_12980.admit);
       lax = (uu___19_12980.lax);
       lax_universes = (uu___19_12980.lax_universes);
       phase1 = (uu___19_12980.phase1);
       failhard = (uu___19_12980.failhard);
       nosynth = (uu___19_12980.nosynth);
       uvar_subtyping = (uu___19_12980.uvar_subtyping);
       tc_term = (uu___19_12980.tc_term);
       type_of = (uu___19_12980.type_of);
       universe_of = (uu___19_12980.universe_of);
       check_type_of = (uu___19_12980.check_type_of);
       use_bv_sorts = (uu___19_12980.use_bv_sorts);
       qtbl_name_and_index = uu____12994;
       normalized_eff_names = uu____13094;
       fv_delta_depths = uu____13097;
       proof_ns = (uu___19_12980.proof_ns);
       synth_hook = (uu___19_12980.synth_hook);
       splice = (uu___19_12980.splice);
       postprocess = (uu___19_12980.postprocess);
       is_native_tactic = (uu___19_12980.is_native_tactic);
       identifier_info = uu____13100;
       tc_hooks = (uu___19_12980.tc_hooks);
       dsenv = (uu___19_12980.dsenv);
       nbe = (uu___19_12980.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13150  ->
    let uu____13151 = FStar_ST.op_Bang stack  in
    match uu____13151 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13205 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13295  ->
           let uu____13296 = snapshot_stack env  in
           match uu____13296 with
           | (stack_depth,env1) ->
               let uu____13330 = snapshot_query_indices ()  in
               (match uu____13330 with
                | (query_indices_depth,()) ->
                    let uu____13363 = (env1.solver).snapshot msg  in
                    (match uu____13363 with
                     | (solver_depth,()) ->
                         let uu____13420 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13420 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___20_13487 = env1  in
                                 {
                                   solver = (uu___20_13487.solver);
                                   range = (uu___20_13487.range);
                                   curmodule = (uu___20_13487.curmodule);
                                   gamma = (uu___20_13487.gamma);
                                   gamma_sig = (uu___20_13487.gamma_sig);
                                   gamma_cache = (uu___20_13487.gamma_cache);
                                   modules = (uu___20_13487.modules);
                                   expected_typ =
                                     (uu___20_13487.expected_typ);
                                   sigtab = (uu___20_13487.sigtab);
                                   attrtab = (uu___20_13487.attrtab);
                                   is_pattern = (uu___20_13487.is_pattern);
                                   instantiate_imp =
                                     (uu___20_13487.instantiate_imp);
                                   effects = (uu___20_13487.effects);
                                   generalize = (uu___20_13487.generalize);
                                   letrecs = (uu___20_13487.letrecs);
                                   top_level = (uu___20_13487.top_level);
                                   check_uvars = (uu___20_13487.check_uvars);
                                   use_eq = (uu___20_13487.use_eq);
                                   is_iface = (uu___20_13487.is_iface);
                                   admit = (uu___20_13487.admit);
                                   lax = (uu___20_13487.lax);
                                   lax_universes =
                                     (uu___20_13487.lax_universes);
                                   phase1 = (uu___20_13487.phase1);
                                   failhard = (uu___20_13487.failhard);
                                   nosynth = (uu___20_13487.nosynth);
                                   uvar_subtyping =
                                     (uu___20_13487.uvar_subtyping);
                                   tc_term = (uu___20_13487.tc_term);
                                   type_of = (uu___20_13487.type_of);
                                   universe_of = (uu___20_13487.universe_of);
                                   check_type_of =
                                     (uu___20_13487.check_type_of);
                                   use_bv_sorts =
                                     (uu___20_13487.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___20_13487.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___20_13487.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___20_13487.fv_delta_depths);
                                   proof_ns = (uu___20_13487.proof_ns);
                                   synth_hook = (uu___20_13487.synth_hook);
                                   splice = (uu___20_13487.splice);
                                   postprocess = (uu___20_13487.postprocess);
                                   is_native_tactic =
                                     (uu___20_13487.is_native_tactic);
                                   identifier_info =
                                     (uu___20_13487.identifier_info);
                                   tc_hooks = (uu___20_13487.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___20_13487.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13521  ->
             let uu____13522 =
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
             match uu____13522 with
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
                             ((let uu____13702 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13702
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13718 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13718
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____13750,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____13792 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____13822  ->
                  match uu____13822 with
                  | (m,uu____13830) -> FStar_Ident.lid_equals l m))
           in
        (match uu____13792 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___21_13845 = env  in
               {
                 solver = (uu___21_13845.solver);
                 range = (uu___21_13845.range);
                 curmodule = (uu___21_13845.curmodule);
                 gamma = (uu___21_13845.gamma);
                 gamma_sig = (uu___21_13845.gamma_sig);
                 gamma_cache = (uu___21_13845.gamma_cache);
                 modules = (uu___21_13845.modules);
                 expected_typ = (uu___21_13845.expected_typ);
                 sigtab = (uu___21_13845.sigtab);
                 attrtab = (uu___21_13845.attrtab);
                 is_pattern = (uu___21_13845.is_pattern);
                 instantiate_imp = (uu___21_13845.instantiate_imp);
                 effects = (uu___21_13845.effects);
                 generalize = (uu___21_13845.generalize);
                 letrecs = (uu___21_13845.letrecs);
                 top_level = (uu___21_13845.top_level);
                 check_uvars = (uu___21_13845.check_uvars);
                 use_eq = (uu___21_13845.use_eq);
                 is_iface = (uu___21_13845.is_iface);
                 admit = (uu___21_13845.admit);
                 lax = (uu___21_13845.lax);
                 lax_universes = (uu___21_13845.lax_universes);
                 phase1 = (uu___21_13845.phase1);
                 failhard = (uu___21_13845.failhard);
                 nosynth = (uu___21_13845.nosynth);
                 uvar_subtyping = (uu___21_13845.uvar_subtyping);
                 tc_term = (uu___21_13845.tc_term);
                 type_of = (uu___21_13845.type_of);
                 universe_of = (uu___21_13845.universe_of);
                 check_type_of = (uu___21_13845.check_type_of);
                 use_bv_sorts = (uu___21_13845.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___21_13845.normalized_eff_names);
                 fv_delta_depths = (uu___21_13845.fv_delta_depths);
                 proof_ns = (uu___21_13845.proof_ns);
                 synth_hook = (uu___21_13845.synth_hook);
                 splice = (uu___21_13845.splice);
                 postprocess = (uu___21_13845.postprocess);
                 is_native_tactic = (uu___21_13845.is_native_tactic);
                 identifier_info = (uu___21_13845.identifier_info);
                 tc_hooks = (uu___21_13845.tc_hooks);
                 dsenv = (uu___21_13845.dsenv);
                 nbe = (uu___21_13845.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____13862,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___22_13878 = env  in
               {
                 solver = (uu___22_13878.solver);
                 range = (uu___22_13878.range);
                 curmodule = (uu___22_13878.curmodule);
                 gamma = (uu___22_13878.gamma);
                 gamma_sig = (uu___22_13878.gamma_sig);
                 gamma_cache = (uu___22_13878.gamma_cache);
                 modules = (uu___22_13878.modules);
                 expected_typ = (uu___22_13878.expected_typ);
                 sigtab = (uu___22_13878.sigtab);
                 attrtab = (uu___22_13878.attrtab);
                 is_pattern = (uu___22_13878.is_pattern);
                 instantiate_imp = (uu___22_13878.instantiate_imp);
                 effects = (uu___22_13878.effects);
                 generalize = (uu___22_13878.generalize);
                 letrecs = (uu___22_13878.letrecs);
                 top_level = (uu___22_13878.top_level);
                 check_uvars = (uu___22_13878.check_uvars);
                 use_eq = (uu___22_13878.use_eq);
                 is_iface = (uu___22_13878.is_iface);
                 admit = (uu___22_13878.admit);
                 lax = (uu___22_13878.lax);
                 lax_universes = (uu___22_13878.lax_universes);
                 phase1 = (uu___22_13878.phase1);
                 failhard = (uu___22_13878.failhard);
                 nosynth = (uu___22_13878.nosynth);
                 uvar_subtyping = (uu___22_13878.uvar_subtyping);
                 tc_term = (uu___22_13878.tc_term);
                 type_of = (uu___22_13878.type_of);
                 universe_of = (uu___22_13878.universe_of);
                 check_type_of = (uu___22_13878.check_type_of);
                 use_bv_sorts = (uu___22_13878.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___22_13878.normalized_eff_names);
                 fv_delta_depths = (uu___22_13878.fv_delta_depths);
                 proof_ns = (uu___22_13878.proof_ns);
                 synth_hook = (uu___22_13878.synth_hook);
                 splice = (uu___22_13878.splice);
                 postprocess = (uu___22_13878.postprocess);
                 is_native_tactic = (uu___22_13878.is_native_tactic);
                 identifier_info = (uu___22_13878.identifier_info);
                 tc_hooks = (uu___22_13878.tc_hooks);
                 dsenv = (uu___22_13878.dsenv);
                 nbe = (uu___22_13878.nbe)
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
        (let uu___23_13921 = e  in
         {
           solver = (uu___23_13921.solver);
           range = r;
           curmodule = (uu___23_13921.curmodule);
           gamma = (uu___23_13921.gamma);
           gamma_sig = (uu___23_13921.gamma_sig);
           gamma_cache = (uu___23_13921.gamma_cache);
           modules = (uu___23_13921.modules);
           expected_typ = (uu___23_13921.expected_typ);
           sigtab = (uu___23_13921.sigtab);
           attrtab = (uu___23_13921.attrtab);
           is_pattern = (uu___23_13921.is_pattern);
           instantiate_imp = (uu___23_13921.instantiate_imp);
           effects = (uu___23_13921.effects);
           generalize = (uu___23_13921.generalize);
           letrecs = (uu___23_13921.letrecs);
           top_level = (uu___23_13921.top_level);
           check_uvars = (uu___23_13921.check_uvars);
           use_eq = (uu___23_13921.use_eq);
           is_iface = (uu___23_13921.is_iface);
           admit = (uu___23_13921.admit);
           lax = (uu___23_13921.lax);
           lax_universes = (uu___23_13921.lax_universes);
           phase1 = (uu___23_13921.phase1);
           failhard = (uu___23_13921.failhard);
           nosynth = (uu___23_13921.nosynth);
           uvar_subtyping = (uu___23_13921.uvar_subtyping);
           tc_term = (uu___23_13921.tc_term);
           type_of = (uu___23_13921.type_of);
           universe_of = (uu___23_13921.universe_of);
           check_type_of = (uu___23_13921.check_type_of);
           use_bv_sorts = (uu___23_13921.use_bv_sorts);
           qtbl_name_and_index = (uu___23_13921.qtbl_name_and_index);
           normalized_eff_names = (uu___23_13921.normalized_eff_names);
           fv_delta_depths = (uu___23_13921.fv_delta_depths);
           proof_ns = (uu___23_13921.proof_ns);
           synth_hook = (uu___23_13921.synth_hook);
           splice = (uu___23_13921.splice);
           postprocess = (uu___23_13921.postprocess);
           is_native_tactic = (uu___23_13921.is_native_tactic);
           identifier_info = (uu___23_13921.identifier_info);
           tc_hooks = (uu___23_13921.tc_hooks);
           dsenv = (uu___23_13921.dsenv);
           nbe = (uu___23_13921.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____13941 =
        let uu____13942 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____13942 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____13941
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____13997 =
          let uu____13998 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____13998 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____13997
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14053 =
          let uu____14054 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14054 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14053
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14109 =
        let uu____14110 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14110 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14109
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___24_14174 = env  in
      {
        solver = (uu___24_14174.solver);
        range = (uu___24_14174.range);
        curmodule = lid;
        gamma = (uu___24_14174.gamma);
        gamma_sig = (uu___24_14174.gamma_sig);
        gamma_cache = (uu___24_14174.gamma_cache);
        modules = (uu___24_14174.modules);
        expected_typ = (uu___24_14174.expected_typ);
        sigtab = (uu___24_14174.sigtab);
        attrtab = (uu___24_14174.attrtab);
        is_pattern = (uu___24_14174.is_pattern);
        instantiate_imp = (uu___24_14174.instantiate_imp);
        effects = (uu___24_14174.effects);
        generalize = (uu___24_14174.generalize);
        letrecs = (uu___24_14174.letrecs);
        top_level = (uu___24_14174.top_level);
        check_uvars = (uu___24_14174.check_uvars);
        use_eq = (uu___24_14174.use_eq);
        is_iface = (uu___24_14174.is_iface);
        admit = (uu___24_14174.admit);
        lax = (uu___24_14174.lax);
        lax_universes = (uu___24_14174.lax_universes);
        phase1 = (uu___24_14174.phase1);
        failhard = (uu___24_14174.failhard);
        nosynth = (uu___24_14174.nosynth);
        uvar_subtyping = (uu___24_14174.uvar_subtyping);
        tc_term = (uu___24_14174.tc_term);
        type_of = (uu___24_14174.type_of);
        universe_of = (uu___24_14174.universe_of);
        check_type_of = (uu___24_14174.check_type_of);
        use_bv_sorts = (uu___24_14174.use_bv_sorts);
        qtbl_name_and_index = (uu___24_14174.qtbl_name_and_index);
        normalized_eff_names = (uu___24_14174.normalized_eff_names);
        fv_delta_depths = (uu___24_14174.fv_delta_depths);
        proof_ns = (uu___24_14174.proof_ns);
        synth_hook = (uu___24_14174.synth_hook);
        splice = (uu___24_14174.splice);
        postprocess = (uu___24_14174.postprocess);
        is_native_tactic = (uu___24_14174.is_native_tactic);
        identifier_info = (uu___24_14174.identifier_info);
        tc_hooks = (uu___24_14174.tc_hooks);
        dsenv = (uu___24_14174.dsenv);
        nbe = (uu___24_14174.nbe)
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
      let uu____14205 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14205
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14218 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14218)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14233 =
      let uu____14235 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14235  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14233)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14244  ->
    let uu____14245 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14245
  
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
      | ((formals,t),uu____14345) ->
          let vs = mk_univ_subst formals us  in
          let uu____14369 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14369)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___2_14386  ->
    match uu___2_14386 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14412  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14432 = inst_tscheme t  in
      match uu____14432 with
      | (us,t1) ->
          let uu____14443 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14443)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14464  ->
          match uu____14464 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____14486 =
                         let uu____14488 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____14492 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____14496 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____14498 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____14488 uu____14492 uu____14496 uu____14498
                          in
                       failwith uu____14486)
                    else ();
                    (let uu____14503 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____14503))
               | uu____14512 ->
                   let uu____14513 =
                     let uu____14515 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____14515
                      in
                   failwith uu____14513)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14527 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14538 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14549 -> false
  
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
             | ([],uu____14597) -> Maybe
             | (uu____14604,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14624 -> No  in
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
          let uu____14718 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14718 with
          | FStar_Pervasives_Native.None  ->
              let uu____14741 =
                FStar_Util.find_map env.gamma
                  (fun uu___3_14785  ->
                     match uu___3_14785 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____14824 = FStar_Ident.lid_equals lid l  in
                         if uu____14824
                         then
                           let uu____14847 =
                             let uu____14866 =
                               let uu____14881 = inst_tscheme t  in
                               FStar_Util.Inl uu____14881  in
                             let uu____14896 = FStar_Ident.range_of_lid l  in
                             (uu____14866, uu____14896)  in
                           FStar_Pervasives_Native.Some uu____14847
                         else FStar_Pervasives_Native.None
                     | uu____14949 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____14741
                (fun uu____14987  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___4_14996  ->
                        match uu___4_14996 with
                        | (uu____14999,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15001);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15002;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15003;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15004;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15005;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15025 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15025
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
                                  uu____15077 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15084 -> cache t  in
                            let uu____15085 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15085 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15091 =
                                   let uu____15092 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15092)
                                    in
                                 maybe_cache uu____15091)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15163 = find_in_sigtab env lid  in
         match uu____15163 with
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
      let uu____15244 = lookup_qname env lid  in
      match uu____15244 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15265,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15379 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15379 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15424 =
          let uu____15427 = lookup_attr env1 attr  in se1 :: uu____15427  in
        FStar_Util.smap_add (attrtab env1) attr uu____15424  in
      FStar_List.iter
        (fun attr  ->
           let uu____15437 =
             let uu____15438 = FStar_Syntax_Subst.compress attr  in
             uu____15438.FStar_Syntax_Syntax.n  in
           match uu____15437 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15442 =
                 let uu____15444 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15444.FStar_Ident.str  in
               add_one1 env se uu____15442
           | uu____15445 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15468) ->
          add_sigelts env ses
      | uu____15477 ->
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
            | uu____15492 -> ()))

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
        (fun uu___5_15524  ->
           match uu___5_15524 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15542 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____15604,lb::[]),uu____15606) ->
            let uu____15615 =
              let uu____15624 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15633 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15624, uu____15633)  in
            FStar_Pervasives_Native.Some uu____15615
        | FStar_Syntax_Syntax.Sig_let ((uu____15646,lbs),uu____15648) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15680 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15693 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15693
                     then
                       let uu____15706 =
                         let uu____15715 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____15724 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15715, uu____15724)  in
                       FStar_Pervasives_Native.Some uu____15706
                     else FStar_Pervasives_Native.None)
        | uu____15747 -> FStar_Pervasives_Native.None
  
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
          let uu____15807 =
            let uu____15816 =
              let uu____15821 =
                let uu____15822 =
                  let uu____15825 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____15825
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____15822)  in
              inst_tscheme1 uu____15821  in
            (uu____15816, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15807
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____15847,uu____15848) ->
          let uu____15853 =
            let uu____15862 =
              let uu____15867 =
                let uu____15868 =
                  let uu____15871 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____15871  in
                (us, uu____15868)  in
              inst_tscheme1 uu____15867  in
            (uu____15862, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15853
      | uu____15890 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____15979 =
          match uu____15979 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16075,uvs,t,uu____16078,uu____16079,uu____16080);
                      FStar_Syntax_Syntax.sigrng = uu____16081;
                      FStar_Syntax_Syntax.sigquals = uu____16082;
                      FStar_Syntax_Syntax.sigmeta = uu____16083;
                      FStar_Syntax_Syntax.sigattrs = uu____16084;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16107 =
                     let uu____16116 = inst_tscheme1 (uvs, t)  in
                     (uu____16116, rng)  in
                   FStar_Pervasives_Native.Some uu____16107
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16140;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16142;
                      FStar_Syntax_Syntax.sigattrs = uu____16143;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16160 =
                     let uu____16162 = in_cur_mod env l  in uu____16162 = Yes
                      in
                   if uu____16160
                   then
                     let uu____16174 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16174
                      then
                        let uu____16190 =
                          let uu____16199 = inst_tscheme1 (uvs, t)  in
                          (uu____16199, rng)  in
                        FStar_Pervasives_Native.Some uu____16190
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16232 =
                        let uu____16241 = inst_tscheme1 (uvs, t)  in
                        (uu____16241, rng)  in
                      FStar_Pervasives_Native.Some uu____16232)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16266,uu____16267);
                      FStar_Syntax_Syntax.sigrng = uu____16268;
                      FStar_Syntax_Syntax.sigquals = uu____16269;
                      FStar_Syntax_Syntax.sigmeta = uu____16270;
                      FStar_Syntax_Syntax.sigattrs = uu____16271;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16312 =
                          let uu____16321 = inst_tscheme1 (uvs, k)  in
                          (uu____16321, rng)  in
                        FStar_Pervasives_Native.Some uu____16312
                    | uu____16342 ->
                        let uu____16343 =
                          let uu____16352 =
                            let uu____16357 =
                              let uu____16358 =
                                let uu____16361 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16361
                                 in
                              (uvs, uu____16358)  in
                            inst_tscheme1 uu____16357  in
                          (uu____16352, rng)  in
                        FStar_Pervasives_Native.Some uu____16343)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16384,uu____16385);
                      FStar_Syntax_Syntax.sigrng = uu____16386;
                      FStar_Syntax_Syntax.sigquals = uu____16387;
                      FStar_Syntax_Syntax.sigmeta = uu____16388;
                      FStar_Syntax_Syntax.sigattrs = uu____16389;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16431 =
                          let uu____16440 = inst_tscheme_with (uvs, k) us  in
                          (uu____16440, rng)  in
                        FStar_Pervasives_Native.Some uu____16431
                    | uu____16461 ->
                        let uu____16462 =
                          let uu____16471 =
                            let uu____16476 =
                              let uu____16477 =
                                let uu____16480 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16480
                                 in
                              (uvs, uu____16477)  in
                            inst_tscheme_with uu____16476 us  in
                          (uu____16471, rng)  in
                        FStar_Pervasives_Native.Some uu____16462)
               | FStar_Util.Inr se ->
                   let uu____16516 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16537;
                          FStar_Syntax_Syntax.sigrng = uu____16538;
                          FStar_Syntax_Syntax.sigquals = uu____16539;
                          FStar_Syntax_Syntax.sigmeta = uu____16540;
                          FStar_Syntax_Syntax.sigattrs = uu____16541;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16556 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____16516
                     (FStar_Util.map_option
                        (fun uu____16604  ->
                           match uu____16604 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16635 =
          let uu____16646 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16646 mapper  in
        match uu____16635 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____16720 =
              let uu____16731 =
                let uu____16738 =
                  let uu___25_16741 = t  in
                  let uu____16742 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___25_16741.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____16742;
                    FStar_Syntax_Syntax.vars =
                      (uu___25_16741.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____16738)  in
              (uu____16731, r)  in
            FStar_Pervasives_Native.Some uu____16720
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16791 = lookup_qname env l  in
      match uu____16791 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____16812 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____16866 = try_lookup_bv env bv  in
      match uu____16866 with
      | FStar_Pervasives_Native.None  ->
          let uu____16881 = variable_not_found bv  in
          FStar_Errors.raise_error uu____16881 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____16897 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____16898 =
            let uu____16899 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____16899  in
          (uu____16897, uu____16898)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____16921 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____16921 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____16987 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____16987  in
          let uu____16988 =
            let uu____16997 =
              let uu____17002 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17002)  in
            (uu____16997, r1)  in
          FStar_Pervasives_Native.Some uu____16988
  
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
        let uu____17037 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17037 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17070,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17095 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17095  in
            let uu____17096 =
              let uu____17101 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17101, r1)  in
            FStar_Pervasives_Native.Some uu____17096
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17125 = try_lookup_lid env l  in
      match uu____17125 with
      | FStar_Pervasives_Native.None  ->
          let uu____17152 = name_not_found l  in
          let uu____17158 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17152 uu____17158
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___6_17201  ->
              match uu___6_17201 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17205 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17226 = lookup_qname env lid  in
      match uu____17226 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17235,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17238;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17240;
              FStar_Syntax_Syntax.sigattrs = uu____17241;_},FStar_Pervasives_Native.None
            ),uu____17242)
          ->
          let uu____17291 =
            let uu____17298 =
              let uu____17299 =
                let uu____17302 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17302 t  in
              (uvs, uu____17299)  in
            (uu____17298, q)  in
          FStar_Pervasives_Native.Some uu____17291
      | uu____17315 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17337 = lookup_qname env lid  in
      match uu____17337 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17342,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17345;
              FStar_Syntax_Syntax.sigquals = uu____17346;
              FStar_Syntax_Syntax.sigmeta = uu____17347;
              FStar_Syntax_Syntax.sigattrs = uu____17348;_},FStar_Pervasives_Native.None
            ),uu____17349)
          ->
          let uu____17398 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17398 (uvs, t)
      | uu____17403 ->
          let uu____17404 = name_not_found lid  in
          let uu____17410 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17404 uu____17410
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17430 = lookup_qname env lid  in
      match uu____17430 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17435,uvs,t,uu____17438,uu____17439,uu____17440);
              FStar_Syntax_Syntax.sigrng = uu____17441;
              FStar_Syntax_Syntax.sigquals = uu____17442;
              FStar_Syntax_Syntax.sigmeta = uu____17443;
              FStar_Syntax_Syntax.sigattrs = uu____17444;_},FStar_Pervasives_Native.None
            ),uu____17445)
          ->
          let uu____17500 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17500 (uvs, t)
      | uu____17505 ->
          let uu____17506 = name_not_found lid  in
          let uu____17512 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17506 uu____17512
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17535 = lookup_qname env lid  in
      match uu____17535 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17543,uu____17544,uu____17545,uu____17546,uu____17547,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17549;
              FStar_Syntax_Syntax.sigquals = uu____17550;
              FStar_Syntax_Syntax.sigmeta = uu____17551;
              FStar_Syntax_Syntax.sigattrs = uu____17552;_},uu____17553),uu____17554)
          -> (true, dcs)
      | uu____17617 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17633 = lookup_qname env lid  in
      match uu____17633 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17634,uu____17635,uu____17636,l,uu____17638,uu____17639);
              FStar_Syntax_Syntax.sigrng = uu____17640;
              FStar_Syntax_Syntax.sigquals = uu____17641;
              FStar_Syntax_Syntax.sigmeta = uu____17642;
              FStar_Syntax_Syntax.sigattrs = uu____17643;_},uu____17644),uu____17645)
          -> l
      | uu____17702 ->
          let uu____17703 =
            let uu____17705 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____17705  in
          failwith uu____17703
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____17775)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____17832) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____17856 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____17856
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____17891 -> FStar_Pervasives_Native.None)
          | uu____17900 -> FStar_Pervasives_Native.None
  
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
        let uu____17962 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____17962
  
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
        let uu____17995 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____17995
  
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
             (FStar_Util.Inl uu____18047,uu____18048) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18097),uu____18098) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18147 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18165 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18175 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18192 ->
                  let uu____18199 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18199
              | FStar_Syntax_Syntax.Sig_let ((uu____18200,lbs),uu____18202)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18218 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18218
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18225 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18233 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18234 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18241 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18242 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18243 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18244 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18257 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18275 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18275
           (fun d_opt  ->
              let uu____18288 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18288
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18298 =
                   let uu____18301 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18301  in
                 match uu____18298 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18302 =
                       let uu____18304 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18304
                        in
                     failwith uu____18302
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18309 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18309
                       then
                         let uu____18312 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18314 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18316 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18312 uu____18314 uu____18316
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
        (FStar_Util.Inr (se,uu____18341),uu____18342) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18391 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18413),uu____18414) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18463 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18485 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18485
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____18508 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____18508 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18532 =
                      let uu____18533 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18533.FStar_Syntax_Syntax.n  in
                    match uu____18532 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____18538 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____18555 = lookup_qname env ftv  in
      match uu____18555 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18559) ->
          let uu____18604 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____18604 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____18625,t),r) ->
               let uu____18640 =
                 let uu____18641 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____18641 t  in
               FStar_Pervasives_Native.Some uu____18640)
      | uu____18642 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____18654 = try_lookup_effect_lid env ftv  in
      match uu____18654 with
      | FStar_Pervasives_Native.None  ->
          let uu____18657 = name_not_found ftv  in
          let uu____18663 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____18657 uu____18663
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
        let uu____18687 = lookup_qname env lid0  in
        match uu____18687 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____18698);
                FStar_Syntax_Syntax.sigrng = uu____18699;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____18701;
                FStar_Syntax_Syntax.sigattrs = uu____18702;_},FStar_Pervasives_Native.None
              ),uu____18703)
            ->
            let lid1 =
              let uu____18757 =
                let uu____18758 = FStar_Ident.range_of_lid lid  in
                let uu____18759 =
                  let uu____18760 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____18760  in
                FStar_Range.set_use_range uu____18758 uu____18759  in
              FStar_Ident.set_lid_range lid uu____18757  in
            let uu____18761 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___7_18767  ->
                      match uu___7_18767 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____18770 -> false))
               in
            if uu____18761
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____18789 =
                      let uu____18791 =
                        let uu____18793 = get_range env  in
                        FStar_Range.string_of_range uu____18793  in
                      let uu____18794 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____18796 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____18791 uu____18794 uu____18796
                       in
                    failwith uu____18789)
                  in
               match (binders, univs1) with
               | ([],uu____18817) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____18843,uu____18844::uu____18845::uu____18846) ->
                   let uu____18867 =
                     let uu____18869 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____18871 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____18869 uu____18871
                      in
                   failwith uu____18867
               | uu____18882 ->
                   let uu____18897 =
                     let uu____18902 =
                       let uu____18903 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____18903)  in
                     inst_tscheme_with uu____18902 insts  in
                   (match uu____18897 with
                    | (uu____18916,t) ->
                        let t1 =
                          let uu____18919 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____18919 t  in
                        let uu____18920 =
                          let uu____18921 = FStar_Syntax_Subst.compress t1
                             in
                          uu____18921.FStar_Syntax_Syntax.n  in
                        (match uu____18920 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____18956 -> failwith "Impossible")))
        | uu____18964 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____18988 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____18988 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19001,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19008 = find1 l2  in
            (match uu____19008 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19015 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19015 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19019 = find1 l  in
            (match uu____19019 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19024 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19024
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19039 = lookup_qname env l1  in
      match uu____19039 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19042;
              FStar_Syntax_Syntax.sigrng = uu____19043;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19045;
              FStar_Syntax_Syntax.sigattrs = uu____19046;_},uu____19047),uu____19048)
          -> q
      | uu____19099 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19123 =
          let uu____19124 =
            let uu____19126 = FStar_Util.string_of_int i  in
            let uu____19128 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19126 uu____19128
             in
          failwith uu____19124  in
        let uu____19131 = lookup_datacon env lid  in
        match uu____19131 with
        | (uu____19136,t) ->
            let uu____19138 =
              let uu____19139 = FStar_Syntax_Subst.compress t  in
              uu____19139.FStar_Syntax_Syntax.n  in
            (match uu____19138 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19143) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19187 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19187
                      FStar_Pervasives_Native.fst)
             | uu____19198 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19212 = lookup_qname env l  in
      match uu____19212 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19214,uu____19215,uu____19216);
              FStar_Syntax_Syntax.sigrng = uu____19217;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19219;
              FStar_Syntax_Syntax.sigattrs = uu____19220;_},uu____19221),uu____19222)
          ->
          FStar_Util.for_some
            (fun uu___8_19275  ->
               match uu___8_19275 with
               | FStar_Syntax_Syntax.Projector uu____19277 -> true
               | uu____19283 -> false) quals
      | uu____19285 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19299 = lookup_qname env lid  in
      match uu____19299 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19301,uu____19302,uu____19303,uu____19304,uu____19305,uu____19306);
              FStar_Syntax_Syntax.sigrng = uu____19307;
              FStar_Syntax_Syntax.sigquals = uu____19308;
              FStar_Syntax_Syntax.sigmeta = uu____19309;
              FStar_Syntax_Syntax.sigattrs = uu____19310;_},uu____19311),uu____19312)
          -> true
      | uu____19370 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19384 = lookup_qname env lid  in
      match uu____19384 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19386,uu____19387,uu____19388,uu____19389,uu____19390,uu____19391);
              FStar_Syntax_Syntax.sigrng = uu____19392;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19394;
              FStar_Syntax_Syntax.sigattrs = uu____19395;_},uu____19396),uu____19397)
          ->
          FStar_Util.for_some
            (fun uu___9_19458  ->
               match uu___9_19458 with
               | FStar_Syntax_Syntax.RecordType uu____19460 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19470 -> true
               | uu____19480 -> false) quals
      | uu____19482 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19492,uu____19493);
            FStar_Syntax_Syntax.sigrng = uu____19494;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19496;
            FStar_Syntax_Syntax.sigattrs = uu____19497;_},uu____19498),uu____19499)
        ->
        FStar_Util.for_some
          (fun uu___10_19556  ->
             match uu___10_19556 with
             | FStar_Syntax_Syntax.Action uu____19558 -> true
             | uu____19560 -> false) quals
    | uu____19562 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19576 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____19576
  
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
      let uu____19593 =
        let uu____19594 = FStar_Syntax_Util.un_uinst head1  in
        uu____19594.FStar_Syntax_Syntax.n  in
      match uu____19593 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____19600 ->
               true
           | uu____19603 -> false)
      | uu____19605 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19619 = lookup_qname env l  in
      match uu____19619 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____19622),uu____19623) ->
          FStar_Util.for_some
            (fun uu___11_19671  ->
               match uu___11_19671 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____19674 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____19676 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____19752 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____19770) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____19788 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____19796 ->
                 FStar_Pervasives_Native.Some true
             | uu____19815 -> FStar_Pervasives_Native.Some false)
         in
      let uu____19818 =
        let uu____19822 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____19822 mapper  in
      match uu____19818 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____19882 = lookup_qname env lid  in
      match uu____19882 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19886,uu____19887,tps,uu____19889,uu____19890,uu____19891);
              FStar_Syntax_Syntax.sigrng = uu____19892;
              FStar_Syntax_Syntax.sigquals = uu____19893;
              FStar_Syntax_Syntax.sigmeta = uu____19894;
              FStar_Syntax_Syntax.sigattrs = uu____19895;_},uu____19896),uu____19897)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____19963 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20009  ->
              match uu____20009 with
              | (d,uu____20018) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20034 = effect_decl_opt env l  in
      match uu____20034 with
      | FStar_Pervasives_Native.None  ->
          let uu____20049 = name_not_found l  in
          let uu____20055 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20049 uu____20055
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20078  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20097  ->
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
        let uu____20129 = FStar_Ident.lid_equals l1 l2  in
        if uu____20129
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20140 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20140
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20151 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20204  ->
                        match uu____20204 with
                        | (m1,m2,uu____20218,uu____20219,uu____20220) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20151 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20237 =
                    let uu____20243 =
                      let uu____20245 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20247 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20245
                        uu____20247
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20243)
                     in
                  FStar_Errors.raise_error uu____20237 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20257,uu____20258,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20292 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20292
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
  'Auu____20312 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20312) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20341 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20367  ->
                match uu____20367 with
                | (d,uu____20374) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20341 with
      | FStar_Pervasives_Native.None  ->
          let uu____20385 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20385
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20400 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____20400 with
           | (uu____20415,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20433)::(wp,uu____20435)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20491 -> failwith "Impossible"))
  
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
          let uu____20549 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____20549
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____20554 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____20554
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
                  let uu____20565 = get_range env  in
                  let uu____20566 =
                    let uu____20573 =
                      let uu____20574 =
                        let uu____20591 =
                          let uu____20602 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____20602]  in
                        (null_wp, uu____20591)  in
                      FStar_Syntax_Syntax.Tm_app uu____20574  in
                    FStar_Syntax_Syntax.mk uu____20573  in
                  uu____20566 FStar_Pervasives_Native.None uu____20565  in
                let uu____20642 =
                  let uu____20643 =
                    let uu____20654 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____20654]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____20643;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____20642))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___26_20692 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___26_20692.order);
              joins = (uu___26_20692.joins)
            }  in
          let uu___27_20701 = env  in
          {
            solver = (uu___27_20701.solver);
            range = (uu___27_20701.range);
            curmodule = (uu___27_20701.curmodule);
            gamma = (uu___27_20701.gamma);
            gamma_sig = (uu___27_20701.gamma_sig);
            gamma_cache = (uu___27_20701.gamma_cache);
            modules = (uu___27_20701.modules);
            expected_typ = (uu___27_20701.expected_typ);
            sigtab = (uu___27_20701.sigtab);
            attrtab = (uu___27_20701.attrtab);
            is_pattern = (uu___27_20701.is_pattern);
            instantiate_imp = (uu___27_20701.instantiate_imp);
            effects;
            generalize = (uu___27_20701.generalize);
            letrecs = (uu___27_20701.letrecs);
            top_level = (uu___27_20701.top_level);
            check_uvars = (uu___27_20701.check_uvars);
            use_eq = (uu___27_20701.use_eq);
            is_iface = (uu___27_20701.is_iface);
            admit = (uu___27_20701.admit);
            lax = (uu___27_20701.lax);
            lax_universes = (uu___27_20701.lax_universes);
            phase1 = (uu___27_20701.phase1);
            failhard = (uu___27_20701.failhard);
            nosynth = (uu___27_20701.nosynth);
            uvar_subtyping = (uu___27_20701.uvar_subtyping);
            tc_term = (uu___27_20701.tc_term);
            type_of = (uu___27_20701.type_of);
            universe_of = (uu___27_20701.universe_of);
            check_type_of = (uu___27_20701.check_type_of);
            use_bv_sorts = (uu___27_20701.use_bv_sorts);
            qtbl_name_and_index = (uu___27_20701.qtbl_name_and_index);
            normalized_eff_names = (uu___27_20701.normalized_eff_names);
            fv_delta_depths = (uu___27_20701.fv_delta_depths);
            proof_ns = (uu___27_20701.proof_ns);
            synth_hook = (uu___27_20701.synth_hook);
            splice = (uu___27_20701.splice);
            postprocess = (uu___27_20701.postprocess);
            is_native_tactic = (uu___27_20701.is_native_tactic);
            identifier_info = (uu___27_20701.identifier_info);
            tc_hooks = (uu___27_20701.tc_hooks);
            dsenv = (uu___27_20701.dsenv);
            nbe = (uu___27_20701.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____20731 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____20731  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____20889 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____20890 = l1 u t wp e  in
                                l2 u t uu____20889 uu____20890))
                | uu____20891 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____20963 = inst_tscheme_with lift_t [u]  in
            match uu____20963 with
            | (uu____20970,lift_t1) ->
                let uu____20972 =
                  let uu____20979 =
                    let uu____20980 =
                      let uu____20997 =
                        let uu____21008 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21017 =
                          let uu____21028 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21028]  in
                        uu____21008 :: uu____21017  in
                      (lift_t1, uu____20997)  in
                    FStar_Syntax_Syntax.Tm_app uu____20980  in
                  FStar_Syntax_Syntax.mk uu____20979  in
                uu____20972 FStar_Pervasives_Native.None
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
            let uu____21141 = inst_tscheme_with lift_t [u]  in
            match uu____21141 with
            | (uu____21148,lift_t1) ->
                let uu____21150 =
                  let uu____21157 =
                    let uu____21158 =
                      let uu____21175 =
                        let uu____21186 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21195 =
                          let uu____21206 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21215 =
                            let uu____21226 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21226]  in
                          uu____21206 :: uu____21215  in
                        uu____21186 :: uu____21195  in
                      (lift_t1, uu____21175)  in
                    FStar_Syntax_Syntax.Tm_app uu____21158  in
                  FStar_Syntax_Syntax.mk uu____21157  in
                uu____21150 FStar_Pervasives_Native.None
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
              let uu____21331 =
                let uu____21332 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21332
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21331  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21341 =
              let uu____21343 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21343  in
            let uu____21344 =
              let uu____21346 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21374 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21374)
                 in
              FStar_Util.dflt "none" uu____21346  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21341
              uu____21344
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21403  ->
                    match uu____21403 with
                    | (e,uu____21411) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21434 =
            match uu____21434 with
            | (i,j) ->
                let uu____21445 = FStar_Ident.lid_equals i j  in
                if uu____21445
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____21480 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____21490 = FStar_Ident.lid_equals i k  in
                        if uu____21490
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____21504 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____21504
                                  then []
                                  else
                                    (let uu____21511 =
                                       let uu____21520 =
                                         find_edge order1 (i, k)  in
                                       let uu____21523 =
                                         find_edge order1 (k, j)  in
                                       (uu____21520, uu____21523)  in
                                     match uu____21511 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____21538 =
                                           compose_edges e1 e2  in
                                         [uu____21538]
                                     | uu____21539 -> [])))))
                 in
              FStar_List.append order1 uu____21480  in
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
                   let uu____21569 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____21572 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____21572
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____21569
                   then
                     let uu____21579 =
                       let uu____21585 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____21585)
                        in
                     let uu____21589 = get_range env  in
                     FStar_Errors.raise_error uu____21579 uu____21589
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____21667 = FStar_Ident.lid_equals i j
                                   in
                                if uu____21667
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____21719 =
                                              let uu____21728 =
                                                find_edge order2 (i, k)  in
                                              let uu____21731 =
                                                find_edge order2 (j, k)  in
                                              (uu____21728, uu____21731)  in
                                            match uu____21719 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____21773,uu____21774)
                                                     ->
                                                     let uu____21781 =
                                                       let uu____21788 =
                                                         let uu____21790 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21790
                                                          in
                                                       let uu____21793 =
                                                         let uu____21795 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21795
                                                          in
                                                       (uu____21788,
                                                         uu____21793)
                                                        in
                                                     (match uu____21781 with
                                                      | (true ,true ) ->
                                                          let uu____21812 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____21812
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
                                            | uu____21855 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___28_21928 = env.effects  in
              { decls = (uu___28_21928.decls); order = order2; joins }  in
            let uu___29_21929 = env  in
            {
              solver = (uu___29_21929.solver);
              range = (uu___29_21929.range);
              curmodule = (uu___29_21929.curmodule);
              gamma = (uu___29_21929.gamma);
              gamma_sig = (uu___29_21929.gamma_sig);
              gamma_cache = (uu___29_21929.gamma_cache);
              modules = (uu___29_21929.modules);
              expected_typ = (uu___29_21929.expected_typ);
              sigtab = (uu___29_21929.sigtab);
              attrtab = (uu___29_21929.attrtab);
              is_pattern = (uu___29_21929.is_pattern);
              instantiate_imp = (uu___29_21929.instantiate_imp);
              effects;
              generalize = (uu___29_21929.generalize);
              letrecs = (uu___29_21929.letrecs);
              top_level = (uu___29_21929.top_level);
              check_uvars = (uu___29_21929.check_uvars);
              use_eq = (uu___29_21929.use_eq);
              is_iface = (uu___29_21929.is_iface);
              admit = (uu___29_21929.admit);
              lax = (uu___29_21929.lax);
              lax_universes = (uu___29_21929.lax_universes);
              phase1 = (uu___29_21929.phase1);
              failhard = (uu___29_21929.failhard);
              nosynth = (uu___29_21929.nosynth);
              uvar_subtyping = (uu___29_21929.uvar_subtyping);
              tc_term = (uu___29_21929.tc_term);
              type_of = (uu___29_21929.type_of);
              universe_of = (uu___29_21929.universe_of);
              check_type_of = (uu___29_21929.check_type_of);
              use_bv_sorts = (uu___29_21929.use_bv_sorts);
              qtbl_name_and_index = (uu___29_21929.qtbl_name_and_index);
              normalized_eff_names = (uu___29_21929.normalized_eff_names);
              fv_delta_depths = (uu___29_21929.fv_delta_depths);
              proof_ns = (uu___29_21929.proof_ns);
              synth_hook = (uu___29_21929.synth_hook);
              splice = (uu___29_21929.splice);
              postprocess = (uu___29_21929.postprocess);
              is_native_tactic = (uu___29_21929.is_native_tactic);
              identifier_info = (uu___29_21929.identifier_info);
              tc_hooks = (uu___29_21929.tc_hooks);
              dsenv = (uu___29_21929.dsenv);
              nbe = (uu___29_21929.nbe)
            }))
      | uu____21930 -> env
  
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
        | uu____21959 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____21972 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____21972 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____21989 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____21989 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____22014 =
                     let uu____22020 =
                       let uu____22022 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22030 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22041 =
                         let uu____22043 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22043  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22022 uu____22030 uu____22041
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22020)
                      in
                   FStar_Errors.raise_error uu____22014
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22051 =
                     let uu____22062 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22062 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22099  ->
                        fun uu____22100  ->
                          match (uu____22099, uu____22100) with
                          | ((x,uu____22130),(t,uu____22132)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22051
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22163 =
                     let uu___30_22164 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___30_22164.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___30_22164.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___30_22164.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___30_22164.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22163
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22176 .
    'Auu____22176 ->
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
          let uu____22206 = effect_decl_opt env effect_name  in
          match uu____22206 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22245 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22268 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22307 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22307
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22312 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22312
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22327 =
                     let uu____22330 = get_range env  in
                     let uu____22331 =
                       let uu____22338 =
                         let uu____22339 =
                           let uu____22356 =
                             let uu____22367 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22367; wp]  in
                           (repr, uu____22356)  in
                         FStar_Syntax_Syntax.Tm_app uu____22339  in
                       FStar_Syntax_Syntax.mk uu____22338  in
                     uu____22331 FStar_Pervasives_Native.None uu____22330  in
                   FStar_Pervasives_Native.Some uu____22327)
  
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
      | uu____22514 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22529 =
        let uu____22530 = FStar_Syntax_Subst.compress t  in
        uu____22530.FStar_Syntax_Syntax.n  in
      match uu____22529 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22534,c) ->
          is_reifiable_comp env c
      | uu____22556 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22576 =
           let uu____22578 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22578  in
         if uu____22576
         then
           let uu____22581 =
             let uu____22587 =
               let uu____22589 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22589
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22587)  in
           let uu____22593 = get_range env  in
           FStar_Errors.raise_error uu____22581 uu____22593
         else ());
        (let uu____22596 = effect_repr_aux true env c u_c  in
         match uu____22596 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___31_22632 = env  in
        {
          solver = (uu___31_22632.solver);
          range = (uu___31_22632.range);
          curmodule = (uu___31_22632.curmodule);
          gamma = (uu___31_22632.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___31_22632.gamma_cache);
          modules = (uu___31_22632.modules);
          expected_typ = (uu___31_22632.expected_typ);
          sigtab = (uu___31_22632.sigtab);
          attrtab = (uu___31_22632.attrtab);
          is_pattern = (uu___31_22632.is_pattern);
          instantiate_imp = (uu___31_22632.instantiate_imp);
          effects = (uu___31_22632.effects);
          generalize = (uu___31_22632.generalize);
          letrecs = (uu___31_22632.letrecs);
          top_level = (uu___31_22632.top_level);
          check_uvars = (uu___31_22632.check_uvars);
          use_eq = (uu___31_22632.use_eq);
          is_iface = (uu___31_22632.is_iface);
          admit = (uu___31_22632.admit);
          lax = (uu___31_22632.lax);
          lax_universes = (uu___31_22632.lax_universes);
          phase1 = (uu___31_22632.phase1);
          failhard = (uu___31_22632.failhard);
          nosynth = (uu___31_22632.nosynth);
          uvar_subtyping = (uu___31_22632.uvar_subtyping);
          tc_term = (uu___31_22632.tc_term);
          type_of = (uu___31_22632.type_of);
          universe_of = (uu___31_22632.universe_of);
          check_type_of = (uu___31_22632.check_type_of);
          use_bv_sorts = (uu___31_22632.use_bv_sorts);
          qtbl_name_and_index = (uu___31_22632.qtbl_name_and_index);
          normalized_eff_names = (uu___31_22632.normalized_eff_names);
          fv_delta_depths = (uu___31_22632.fv_delta_depths);
          proof_ns = (uu___31_22632.proof_ns);
          synth_hook = (uu___31_22632.synth_hook);
          splice = (uu___31_22632.splice);
          postprocess = (uu___31_22632.postprocess);
          is_native_tactic = (uu___31_22632.is_native_tactic);
          identifier_info = (uu___31_22632.identifier_info);
          tc_hooks = (uu___31_22632.tc_hooks);
          dsenv = (uu___31_22632.dsenv);
          nbe = (uu___31_22632.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___32_22646 = env  in
      {
        solver = (uu___32_22646.solver);
        range = (uu___32_22646.range);
        curmodule = (uu___32_22646.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___32_22646.gamma_sig);
        gamma_cache = (uu___32_22646.gamma_cache);
        modules = (uu___32_22646.modules);
        expected_typ = (uu___32_22646.expected_typ);
        sigtab = (uu___32_22646.sigtab);
        attrtab = (uu___32_22646.attrtab);
        is_pattern = (uu___32_22646.is_pattern);
        instantiate_imp = (uu___32_22646.instantiate_imp);
        effects = (uu___32_22646.effects);
        generalize = (uu___32_22646.generalize);
        letrecs = (uu___32_22646.letrecs);
        top_level = (uu___32_22646.top_level);
        check_uvars = (uu___32_22646.check_uvars);
        use_eq = (uu___32_22646.use_eq);
        is_iface = (uu___32_22646.is_iface);
        admit = (uu___32_22646.admit);
        lax = (uu___32_22646.lax);
        lax_universes = (uu___32_22646.lax_universes);
        phase1 = (uu___32_22646.phase1);
        failhard = (uu___32_22646.failhard);
        nosynth = (uu___32_22646.nosynth);
        uvar_subtyping = (uu___32_22646.uvar_subtyping);
        tc_term = (uu___32_22646.tc_term);
        type_of = (uu___32_22646.type_of);
        universe_of = (uu___32_22646.universe_of);
        check_type_of = (uu___32_22646.check_type_of);
        use_bv_sorts = (uu___32_22646.use_bv_sorts);
        qtbl_name_and_index = (uu___32_22646.qtbl_name_and_index);
        normalized_eff_names = (uu___32_22646.normalized_eff_names);
        fv_delta_depths = (uu___32_22646.fv_delta_depths);
        proof_ns = (uu___32_22646.proof_ns);
        synth_hook = (uu___32_22646.synth_hook);
        splice = (uu___32_22646.splice);
        postprocess = (uu___32_22646.postprocess);
        is_native_tactic = (uu___32_22646.is_native_tactic);
        identifier_info = (uu___32_22646.identifier_info);
        tc_hooks = (uu___32_22646.tc_hooks);
        dsenv = (uu___32_22646.dsenv);
        nbe = (uu___32_22646.nbe)
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
            (let uu___33_22704 = env  in
             {
               solver = (uu___33_22704.solver);
               range = (uu___33_22704.range);
               curmodule = (uu___33_22704.curmodule);
               gamma = rest;
               gamma_sig = (uu___33_22704.gamma_sig);
               gamma_cache = (uu___33_22704.gamma_cache);
               modules = (uu___33_22704.modules);
               expected_typ = (uu___33_22704.expected_typ);
               sigtab = (uu___33_22704.sigtab);
               attrtab = (uu___33_22704.attrtab);
               is_pattern = (uu___33_22704.is_pattern);
               instantiate_imp = (uu___33_22704.instantiate_imp);
               effects = (uu___33_22704.effects);
               generalize = (uu___33_22704.generalize);
               letrecs = (uu___33_22704.letrecs);
               top_level = (uu___33_22704.top_level);
               check_uvars = (uu___33_22704.check_uvars);
               use_eq = (uu___33_22704.use_eq);
               is_iface = (uu___33_22704.is_iface);
               admit = (uu___33_22704.admit);
               lax = (uu___33_22704.lax);
               lax_universes = (uu___33_22704.lax_universes);
               phase1 = (uu___33_22704.phase1);
               failhard = (uu___33_22704.failhard);
               nosynth = (uu___33_22704.nosynth);
               uvar_subtyping = (uu___33_22704.uvar_subtyping);
               tc_term = (uu___33_22704.tc_term);
               type_of = (uu___33_22704.type_of);
               universe_of = (uu___33_22704.universe_of);
               check_type_of = (uu___33_22704.check_type_of);
               use_bv_sorts = (uu___33_22704.use_bv_sorts);
               qtbl_name_and_index = (uu___33_22704.qtbl_name_and_index);
               normalized_eff_names = (uu___33_22704.normalized_eff_names);
               fv_delta_depths = (uu___33_22704.fv_delta_depths);
               proof_ns = (uu___33_22704.proof_ns);
               synth_hook = (uu___33_22704.synth_hook);
               splice = (uu___33_22704.splice);
               postprocess = (uu___33_22704.postprocess);
               is_native_tactic = (uu___33_22704.is_native_tactic);
               identifier_info = (uu___33_22704.identifier_info);
               tc_hooks = (uu___33_22704.tc_hooks);
               dsenv = (uu___33_22704.dsenv);
               nbe = (uu___33_22704.nbe)
             }))
    | uu____22705 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____22734  ->
             match uu____22734 with | (x,uu____22742) -> push_bv env1 x) env
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
            let uu___34_22777 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___34_22777.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___34_22777.FStar_Syntax_Syntax.index);
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
      (let uu___35_22819 = env  in
       {
         solver = (uu___35_22819.solver);
         range = (uu___35_22819.range);
         curmodule = (uu___35_22819.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___35_22819.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___35_22819.sigtab);
         attrtab = (uu___35_22819.attrtab);
         is_pattern = (uu___35_22819.is_pattern);
         instantiate_imp = (uu___35_22819.instantiate_imp);
         effects = (uu___35_22819.effects);
         generalize = (uu___35_22819.generalize);
         letrecs = (uu___35_22819.letrecs);
         top_level = (uu___35_22819.top_level);
         check_uvars = (uu___35_22819.check_uvars);
         use_eq = (uu___35_22819.use_eq);
         is_iface = (uu___35_22819.is_iface);
         admit = (uu___35_22819.admit);
         lax = (uu___35_22819.lax);
         lax_universes = (uu___35_22819.lax_universes);
         phase1 = (uu___35_22819.phase1);
         failhard = (uu___35_22819.failhard);
         nosynth = (uu___35_22819.nosynth);
         uvar_subtyping = (uu___35_22819.uvar_subtyping);
         tc_term = (uu___35_22819.tc_term);
         type_of = (uu___35_22819.type_of);
         universe_of = (uu___35_22819.universe_of);
         check_type_of = (uu___35_22819.check_type_of);
         use_bv_sorts = (uu___35_22819.use_bv_sorts);
         qtbl_name_and_index = (uu___35_22819.qtbl_name_and_index);
         normalized_eff_names = (uu___35_22819.normalized_eff_names);
         fv_delta_depths = (uu___35_22819.fv_delta_depths);
         proof_ns = (uu___35_22819.proof_ns);
         synth_hook = (uu___35_22819.synth_hook);
         splice = (uu___35_22819.splice);
         postprocess = (uu___35_22819.postprocess);
         is_native_tactic = (uu___35_22819.is_native_tactic);
         identifier_info = (uu___35_22819.identifier_info);
         tc_hooks = (uu___35_22819.tc_hooks);
         dsenv = (uu___35_22819.dsenv);
         nbe = (uu___35_22819.nbe)
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
        let uu____22863 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____22863 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____22891 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____22891)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___36_22907 = env  in
      {
        solver = (uu___36_22907.solver);
        range = (uu___36_22907.range);
        curmodule = (uu___36_22907.curmodule);
        gamma = (uu___36_22907.gamma);
        gamma_sig = (uu___36_22907.gamma_sig);
        gamma_cache = (uu___36_22907.gamma_cache);
        modules = (uu___36_22907.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___36_22907.sigtab);
        attrtab = (uu___36_22907.attrtab);
        is_pattern = (uu___36_22907.is_pattern);
        instantiate_imp = (uu___36_22907.instantiate_imp);
        effects = (uu___36_22907.effects);
        generalize = (uu___36_22907.generalize);
        letrecs = (uu___36_22907.letrecs);
        top_level = (uu___36_22907.top_level);
        check_uvars = (uu___36_22907.check_uvars);
        use_eq = false;
        is_iface = (uu___36_22907.is_iface);
        admit = (uu___36_22907.admit);
        lax = (uu___36_22907.lax);
        lax_universes = (uu___36_22907.lax_universes);
        phase1 = (uu___36_22907.phase1);
        failhard = (uu___36_22907.failhard);
        nosynth = (uu___36_22907.nosynth);
        uvar_subtyping = (uu___36_22907.uvar_subtyping);
        tc_term = (uu___36_22907.tc_term);
        type_of = (uu___36_22907.type_of);
        universe_of = (uu___36_22907.universe_of);
        check_type_of = (uu___36_22907.check_type_of);
        use_bv_sorts = (uu___36_22907.use_bv_sorts);
        qtbl_name_and_index = (uu___36_22907.qtbl_name_and_index);
        normalized_eff_names = (uu___36_22907.normalized_eff_names);
        fv_delta_depths = (uu___36_22907.fv_delta_depths);
        proof_ns = (uu___36_22907.proof_ns);
        synth_hook = (uu___36_22907.synth_hook);
        splice = (uu___36_22907.splice);
        postprocess = (uu___36_22907.postprocess);
        is_native_tactic = (uu___36_22907.is_native_tactic);
        identifier_info = (uu___36_22907.identifier_info);
        tc_hooks = (uu___36_22907.tc_hooks);
        dsenv = (uu___36_22907.dsenv);
        nbe = (uu___36_22907.nbe)
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
    let uu____22938 = expected_typ env_  in
    ((let uu___37_22944 = env_  in
      {
        solver = (uu___37_22944.solver);
        range = (uu___37_22944.range);
        curmodule = (uu___37_22944.curmodule);
        gamma = (uu___37_22944.gamma);
        gamma_sig = (uu___37_22944.gamma_sig);
        gamma_cache = (uu___37_22944.gamma_cache);
        modules = (uu___37_22944.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___37_22944.sigtab);
        attrtab = (uu___37_22944.attrtab);
        is_pattern = (uu___37_22944.is_pattern);
        instantiate_imp = (uu___37_22944.instantiate_imp);
        effects = (uu___37_22944.effects);
        generalize = (uu___37_22944.generalize);
        letrecs = (uu___37_22944.letrecs);
        top_level = (uu___37_22944.top_level);
        check_uvars = (uu___37_22944.check_uvars);
        use_eq = false;
        is_iface = (uu___37_22944.is_iface);
        admit = (uu___37_22944.admit);
        lax = (uu___37_22944.lax);
        lax_universes = (uu___37_22944.lax_universes);
        phase1 = (uu___37_22944.phase1);
        failhard = (uu___37_22944.failhard);
        nosynth = (uu___37_22944.nosynth);
        uvar_subtyping = (uu___37_22944.uvar_subtyping);
        tc_term = (uu___37_22944.tc_term);
        type_of = (uu___37_22944.type_of);
        universe_of = (uu___37_22944.universe_of);
        check_type_of = (uu___37_22944.check_type_of);
        use_bv_sorts = (uu___37_22944.use_bv_sorts);
        qtbl_name_and_index = (uu___37_22944.qtbl_name_and_index);
        normalized_eff_names = (uu___37_22944.normalized_eff_names);
        fv_delta_depths = (uu___37_22944.fv_delta_depths);
        proof_ns = (uu___37_22944.proof_ns);
        synth_hook = (uu___37_22944.synth_hook);
        splice = (uu___37_22944.splice);
        postprocess = (uu___37_22944.postprocess);
        is_native_tactic = (uu___37_22944.is_native_tactic);
        identifier_info = (uu___37_22944.identifier_info);
        tc_hooks = (uu___37_22944.tc_hooks);
        dsenv = (uu___37_22944.dsenv);
        nbe = (uu___37_22944.nbe)
      }), uu____22938)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____22956 =
      let uu____22959 = FStar_Ident.id_of_text ""  in [uu____22959]  in
    FStar_Ident.lid_of_ids uu____22956  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____22966 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____22966
        then
          let uu____22971 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____22971 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___38_22999 = env  in
       {
         solver = (uu___38_22999.solver);
         range = (uu___38_22999.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___38_22999.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___38_22999.expected_typ);
         sigtab = (uu___38_22999.sigtab);
         attrtab = (uu___38_22999.attrtab);
         is_pattern = (uu___38_22999.is_pattern);
         instantiate_imp = (uu___38_22999.instantiate_imp);
         effects = (uu___38_22999.effects);
         generalize = (uu___38_22999.generalize);
         letrecs = (uu___38_22999.letrecs);
         top_level = (uu___38_22999.top_level);
         check_uvars = (uu___38_22999.check_uvars);
         use_eq = (uu___38_22999.use_eq);
         is_iface = (uu___38_22999.is_iface);
         admit = (uu___38_22999.admit);
         lax = (uu___38_22999.lax);
         lax_universes = (uu___38_22999.lax_universes);
         phase1 = (uu___38_22999.phase1);
         failhard = (uu___38_22999.failhard);
         nosynth = (uu___38_22999.nosynth);
         uvar_subtyping = (uu___38_22999.uvar_subtyping);
         tc_term = (uu___38_22999.tc_term);
         type_of = (uu___38_22999.type_of);
         universe_of = (uu___38_22999.universe_of);
         check_type_of = (uu___38_22999.check_type_of);
         use_bv_sorts = (uu___38_22999.use_bv_sorts);
         qtbl_name_and_index = (uu___38_22999.qtbl_name_and_index);
         normalized_eff_names = (uu___38_22999.normalized_eff_names);
         fv_delta_depths = (uu___38_22999.fv_delta_depths);
         proof_ns = (uu___38_22999.proof_ns);
         synth_hook = (uu___38_22999.synth_hook);
         splice = (uu___38_22999.splice);
         postprocess = (uu___38_22999.postprocess);
         is_native_tactic = (uu___38_22999.is_native_tactic);
         identifier_info = (uu___38_22999.identifier_info);
         tc_hooks = (uu___38_22999.tc_hooks);
         dsenv = (uu___38_22999.dsenv);
         nbe = (uu___38_22999.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23051)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23055,(uu____23056,t)))::tl1
          ->
          let uu____23077 =
            let uu____23080 = FStar_Syntax_Free.uvars t  in
            ext out uu____23080  in
          aux uu____23077 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23083;
            FStar_Syntax_Syntax.index = uu____23084;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23092 =
            let uu____23095 = FStar_Syntax_Free.uvars t  in
            ext out uu____23095  in
          aux uu____23092 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23153)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23157,(uu____23158,t)))::tl1
          ->
          let uu____23179 =
            let uu____23182 = FStar_Syntax_Free.univs t  in
            ext out uu____23182  in
          aux uu____23179 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23185;
            FStar_Syntax_Syntax.index = uu____23186;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23194 =
            let uu____23197 = FStar_Syntax_Free.univs t  in
            ext out uu____23197  in
          aux uu____23194 tl1
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
          let uu____23259 = FStar_Util.set_add uname out  in
          aux uu____23259 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23262,(uu____23263,t)))::tl1
          ->
          let uu____23284 =
            let uu____23287 = FStar_Syntax_Free.univnames t  in
            ext out uu____23287  in
          aux uu____23284 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23290;
            FStar_Syntax_Syntax.index = uu____23291;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23299 =
            let uu____23302 = FStar_Syntax_Free.univnames t  in
            ext out uu____23302  in
          aux uu____23299 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_23323  ->
            match uu___12_23323 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23327 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23340 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23351 =
      let uu____23360 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23360
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23351 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23408 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_23421  ->
              match uu___13_23421 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23424 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____23424
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23430) ->
                  let uu____23447 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____23447))
       in
    FStar_All.pipe_right uu____23408 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_23461  ->
    match uu___14_23461 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23467 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____23467
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23490  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23545) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____23578,uu____23579) -> false  in
      let uu____23593 =
        FStar_List.tryFind
          (fun uu____23615  ->
             match uu____23615 with | (p,uu____23626) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____23593 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23645,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23675 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23675
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___39_23697 = e  in
        {
          solver = (uu___39_23697.solver);
          range = (uu___39_23697.range);
          curmodule = (uu___39_23697.curmodule);
          gamma = (uu___39_23697.gamma);
          gamma_sig = (uu___39_23697.gamma_sig);
          gamma_cache = (uu___39_23697.gamma_cache);
          modules = (uu___39_23697.modules);
          expected_typ = (uu___39_23697.expected_typ);
          sigtab = (uu___39_23697.sigtab);
          attrtab = (uu___39_23697.attrtab);
          is_pattern = (uu___39_23697.is_pattern);
          instantiate_imp = (uu___39_23697.instantiate_imp);
          effects = (uu___39_23697.effects);
          generalize = (uu___39_23697.generalize);
          letrecs = (uu___39_23697.letrecs);
          top_level = (uu___39_23697.top_level);
          check_uvars = (uu___39_23697.check_uvars);
          use_eq = (uu___39_23697.use_eq);
          is_iface = (uu___39_23697.is_iface);
          admit = (uu___39_23697.admit);
          lax = (uu___39_23697.lax);
          lax_universes = (uu___39_23697.lax_universes);
          phase1 = (uu___39_23697.phase1);
          failhard = (uu___39_23697.failhard);
          nosynth = (uu___39_23697.nosynth);
          uvar_subtyping = (uu___39_23697.uvar_subtyping);
          tc_term = (uu___39_23697.tc_term);
          type_of = (uu___39_23697.type_of);
          universe_of = (uu___39_23697.universe_of);
          check_type_of = (uu___39_23697.check_type_of);
          use_bv_sorts = (uu___39_23697.use_bv_sorts);
          qtbl_name_and_index = (uu___39_23697.qtbl_name_and_index);
          normalized_eff_names = (uu___39_23697.normalized_eff_names);
          fv_delta_depths = (uu___39_23697.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___39_23697.synth_hook);
          splice = (uu___39_23697.splice);
          postprocess = (uu___39_23697.postprocess);
          is_native_tactic = (uu___39_23697.is_native_tactic);
          identifier_info = (uu___39_23697.identifier_info);
          tc_hooks = (uu___39_23697.tc_hooks);
          dsenv = (uu___39_23697.dsenv);
          nbe = (uu___39_23697.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___40_23745 = e  in
      {
        solver = (uu___40_23745.solver);
        range = (uu___40_23745.range);
        curmodule = (uu___40_23745.curmodule);
        gamma = (uu___40_23745.gamma);
        gamma_sig = (uu___40_23745.gamma_sig);
        gamma_cache = (uu___40_23745.gamma_cache);
        modules = (uu___40_23745.modules);
        expected_typ = (uu___40_23745.expected_typ);
        sigtab = (uu___40_23745.sigtab);
        attrtab = (uu___40_23745.attrtab);
        is_pattern = (uu___40_23745.is_pattern);
        instantiate_imp = (uu___40_23745.instantiate_imp);
        effects = (uu___40_23745.effects);
        generalize = (uu___40_23745.generalize);
        letrecs = (uu___40_23745.letrecs);
        top_level = (uu___40_23745.top_level);
        check_uvars = (uu___40_23745.check_uvars);
        use_eq = (uu___40_23745.use_eq);
        is_iface = (uu___40_23745.is_iface);
        admit = (uu___40_23745.admit);
        lax = (uu___40_23745.lax);
        lax_universes = (uu___40_23745.lax_universes);
        phase1 = (uu___40_23745.phase1);
        failhard = (uu___40_23745.failhard);
        nosynth = (uu___40_23745.nosynth);
        uvar_subtyping = (uu___40_23745.uvar_subtyping);
        tc_term = (uu___40_23745.tc_term);
        type_of = (uu___40_23745.type_of);
        universe_of = (uu___40_23745.universe_of);
        check_type_of = (uu___40_23745.check_type_of);
        use_bv_sorts = (uu___40_23745.use_bv_sorts);
        qtbl_name_and_index = (uu___40_23745.qtbl_name_and_index);
        normalized_eff_names = (uu___40_23745.normalized_eff_names);
        fv_delta_depths = (uu___40_23745.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___40_23745.synth_hook);
        splice = (uu___40_23745.splice);
        postprocess = (uu___40_23745.postprocess);
        is_native_tactic = (uu___40_23745.is_native_tactic);
        identifier_info = (uu___40_23745.identifier_info);
        tc_hooks = (uu___40_23745.tc_hooks);
        dsenv = (uu___40_23745.dsenv);
        nbe = (uu___40_23745.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____23761 = FStar_Syntax_Free.names t  in
      let uu____23764 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____23761 uu____23764
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____23787 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____23787
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____23797 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____23797
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____23818 =
      match uu____23818 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____23838 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____23838)
       in
    let uu____23846 =
      let uu____23850 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____23850 FStar_List.rev  in
    FStar_All.pipe_right uu____23846 (FStar_String.concat " ")
  
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
                  (let uu____23920 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____23920 with
                   | FStar_Pervasives_Native.Some uu____23924 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____23927 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____23937;
        univ_ineqs = uu____23938; implicits = uu____23939;_} -> true
    | uu____23951 -> false
  
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
          let uu___41_23982 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___41_23982.deferred);
            univ_ineqs = (uu___41_23982.univ_ineqs);
            implicits = (uu___41_23982.implicits)
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
          let uu____24021 = FStar_Options.defensive ()  in
          if uu____24021
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24027 =
              let uu____24029 =
                let uu____24031 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24031  in
              Prims.op_Negation uu____24029  in
            (if uu____24027
             then
               let uu____24038 =
                 let uu____24044 =
                   let uu____24046 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24048 =
                     let uu____24050 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24050
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24046 uu____24048
                    in
                 (FStar_Errors.Warning_Defensive, uu____24044)  in
               FStar_Errors.log_issue rng uu____24038
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
          let uu____24090 =
            let uu____24092 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24092  in
          if uu____24090
          then ()
          else
            (let uu____24097 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24097 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24123 =
            let uu____24125 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24125  in
          if uu____24123
          then ()
          else
            (let uu____24130 = bound_vars e  in
             def_check_closed_in rng msg uu____24130 t)
  
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
          let uu___42_24169 = g  in
          let uu____24170 =
            let uu____24171 =
              let uu____24172 =
                let uu____24179 =
                  let uu____24180 =
                    let uu____24197 =
                      let uu____24208 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24208]  in
                    (f, uu____24197)  in
                  FStar_Syntax_Syntax.Tm_app uu____24180  in
                FStar_Syntax_Syntax.mk uu____24179  in
              uu____24172 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_2  -> FStar_TypeChecker_Common.NonTrivial _0_2)
              uu____24171
             in
          {
            guard_f = uu____24170;
            deferred = (uu___42_24169.deferred);
            univ_ineqs = (uu___42_24169.univ_ineqs);
            implicits = (uu___42_24169.implicits)
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
          let uu___43_24265 = g  in
          let uu____24266 =
            let uu____24267 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24267  in
          {
            guard_f = uu____24266;
            deferred = (uu___43_24265.deferred);
            univ_ineqs = (uu___43_24265.univ_ineqs);
            implicits = (uu___43_24265.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___44_24284 = g  in
          let uu____24285 =
            let uu____24286 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24286  in
          {
            guard_f = uu____24285;
            deferred = (uu___44_24284.deferred);
            univ_ineqs = (uu___44_24284.univ_ineqs);
            implicits = (uu___44_24284.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___45_24288 = g  in
          let uu____24289 =
            let uu____24290 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24290  in
          {
            guard_f = uu____24289;
            deferred = (uu___45_24288.deferred);
            univ_ineqs = (uu___45_24288.univ_ineqs);
            implicits = (uu___45_24288.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24297 ->
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
          let uu____24314 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24314
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24321 =
      let uu____24322 = FStar_Syntax_Util.unmeta t  in
      uu____24322.FStar_Syntax_Syntax.n  in
    match uu____24321 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24326 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24369 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24369;
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
                       let uu____24464 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24464
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___46_24471 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___46_24471.deferred);
              univ_ineqs = (uu___46_24471.univ_ineqs);
              implicits = (uu___46_24471.implicits)
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
               let uu____24505 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24505
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
            let uu___47_24532 = g  in
            let uu____24533 =
              let uu____24534 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24534  in
            {
              guard_f = uu____24533;
              deferred = (uu___47_24532.deferred);
              univ_ineqs = (uu___47_24532.univ_ineqs);
              implicits = (uu___47_24532.implicits)
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
              let uu____24592 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____24592 with
              | FStar_Pervasives_Native.Some
                  (uu____24617::(tm,uu____24619)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____24683 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____24701 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____24701;
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
                      let uu___48_24733 = trivial_guard  in
                      {
                        guard_f = (uu___48_24733.guard_f);
                        deferred = (uu___48_24733.deferred);
                        univ_ineqs = (uu___48_24733.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____24751  -> ());
    push = (fun uu____24753  -> ());
    pop = (fun uu____24756  -> ());
    snapshot =
      (fun uu____24759  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____24778  -> fun uu____24779  -> ());
    encode_sig = (fun uu____24794  -> fun uu____24795  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____24801 =
             let uu____24808 = FStar_Options.peek ()  in (e, g, uu____24808)
              in
           [uu____24801]);
    solve = (fun uu____24824  -> fun uu____24825  -> fun uu____24826  -> ());
    finish = (fun uu____24833  -> ());
    refresh = (fun uu____24835  -> ())
  } 