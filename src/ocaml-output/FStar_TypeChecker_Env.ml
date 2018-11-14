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
  encode_modul: env -> FStar_Syntax_Syntax.modul -> unit ;
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
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> init1
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> push1
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> pop1
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t -> Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit)) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
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
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> rollback1
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> encode_sig
  
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env -> goal -> (env * goal * FStar_Options.optionstate) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> preprocess
  
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> finish1
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
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
           (fun uu___277_11986  ->
              match uu___277_11986 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____11989 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____11989  in
                  let uu____11990 =
                    let uu____11991 = FStar_Syntax_Subst.compress y  in
                    uu____11991.FStar_Syntax_Syntax.n  in
                  (match uu____11990 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____11995 =
                         let uu___291_11996 = y1  in
                         let uu____11997 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___291_11996.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___291_11996.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____11997
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____11995
                   | uu____12000 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___292_12014 = env  in
      let uu____12015 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___292_12014.solver);
        range = (uu___292_12014.range);
        curmodule = (uu___292_12014.curmodule);
        gamma = uu____12015;
        gamma_sig = (uu___292_12014.gamma_sig);
        gamma_cache = (uu___292_12014.gamma_cache);
        modules = (uu___292_12014.modules);
        expected_typ = (uu___292_12014.expected_typ);
        sigtab = (uu___292_12014.sigtab);
        attrtab = (uu___292_12014.attrtab);
        is_pattern = (uu___292_12014.is_pattern);
        instantiate_imp = (uu___292_12014.instantiate_imp);
        effects = (uu___292_12014.effects);
        generalize = (uu___292_12014.generalize);
        letrecs = (uu___292_12014.letrecs);
        top_level = (uu___292_12014.top_level);
        check_uvars = (uu___292_12014.check_uvars);
        use_eq = (uu___292_12014.use_eq);
        is_iface = (uu___292_12014.is_iface);
        admit = (uu___292_12014.admit);
        lax = (uu___292_12014.lax);
        lax_universes = (uu___292_12014.lax_universes);
        phase1 = (uu___292_12014.phase1);
        failhard = (uu___292_12014.failhard);
        nosynth = (uu___292_12014.nosynth);
        uvar_subtyping = (uu___292_12014.uvar_subtyping);
        tc_term = (uu___292_12014.tc_term);
        type_of = (uu___292_12014.type_of);
        universe_of = (uu___292_12014.universe_of);
        check_type_of = (uu___292_12014.check_type_of);
        use_bv_sorts = (uu___292_12014.use_bv_sorts);
        qtbl_name_and_index = (uu___292_12014.qtbl_name_and_index);
        normalized_eff_names = (uu___292_12014.normalized_eff_names);
        fv_delta_depths = (uu___292_12014.fv_delta_depths);
        proof_ns = (uu___292_12014.proof_ns);
        synth_hook = (uu___292_12014.synth_hook);
        splice = (uu___292_12014.splice);
        postprocess = (uu___292_12014.postprocess);
        is_native_tactic = (uu___292_12014.is_native_tactic);
        identifier_info = (uu___292_12014.identifier_info);
        tc_hooks = (uu___292_12014.tc_hooks);
        dsenv = (uu___292_12014.dsenv);
        nbe = (uu___292_12014.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12023  -> fun uu____12024  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___293_12046 = env  in
      {
        solver = (uu___293_12046.solver);
        range = (uu___293_12046.range);
        curmodule = (uu___293_12046.curmodule);
        gamma = (uu___293_12046.gamma);
        gamma_sig = (uu___293_12046.gamma_sig);
        gamma_cache = (uu___293_12046.gamma_cache);
        modules = (uu___293_12046.modules);
        expected_typ = (uu___293_12046.expected_typ);
        sigtab = (uu___293_12046.sigtab);
        attrtab = (uu___293_12046.attrtab);
        is_pattern = (uu___293_12046.is_pattern);
        instantiate_imp = (uu___293_12046.instantiate_imp);
        effects = (uu___293_12046.effects);
        generalize = (uu___293_12046.generalize);
        letrecs = (uu___293_12046.letrecs);
        top_level = (uu___293_12046.top_level);
        check_uvars = (uu___293_12046.check_uvars);
        use_eq = (uu___293_12046.use_eq);
        is_iface = (uu___293_12046.is_iface);
        admit = (uu___293_12046.admit);
        lax = (uu___293_12046.lax);
        lax_universes = (uu___293_12046.lax_universes);
        phase1 = (uu___293_12046.phase1);
        failhard = (uu___293_12046.failhard);
        nosynth = (uu___293_12046.nosynth);
        uvar_subtyping = (uu___293_12046.uvar_subtyping);
        tc_term = (uu___293_12046.tc_term);
        type_of = (uu___293_12046.type_of);
        universe_of = (uu___293_12046.universe_of);
        check_type_of = (uu___293_12046.check_type_of);
        use_bv_sorts = (uu___293_12046.use_bv_sorts);
        qtbl_name_and_index = (uu___293_12046.qtbl_name_and_index);
        normalized_eff_names = (uu___293_12046.normalized_eff_names);
        fv_delta_depths = (uu___293_12046.fv_delta_depths);
        proof_ns = (uu___293_12046.proof_ns);
        synth_hook = (uu___293_12046.synth_hook);
        splice = (uu___293_12046.splice);
        postprocess = (uu___293_12046.postprocess);
        is_native_tactic = (uu___293_12046.is_native_tactic);
        identifier_info = (uu___293_12046.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___293_12046.dsenv);
        nbe = (uu___293_12046.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___294_12058 = e  in
      let uu____12059 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___294_12058.solver);
        range = (uu___294_12058.range);
        curmodule = (uu___294_12058.curmodule);
        gamma = (uu___294_12058.gamma);
        gamma_sig = (uu___294_12058.gamma_sig);
        gamma_cache = (uu___294_12058.gamma_cache);
        modules = (uu___294_12058.modules);
        expected_typ = (uu___294_12058.expected_typ);
        sigtab = (uu___294_12058.sigtab);
        attrtab = (uu___294_12058.attrtab);
        is_pattern = (uu___294_12058.is_pattern);
        instantiate_imp = (uu___294_12058.instantiate_imp);
        effects = (uu___294_12058.effects);
        generalize = (uu___294_12058.generalize);
        letrecs = (uu___294_12058.letrecs);
        top_level = (uu___294_12058.top_level);
        check_uvars = (uu___294_12058.check_uvars);
        use_eq = (uu___294_12058.use_eq);
        is_iface = (uu___294_12058.is_iface);
        admit = (uu___294_12058.admit);
        lax = (uu___294_12058.lax);
        lax_universes = (uu___294_12058.lax_universes);
        phase1 = (uu___294_12058.phase1);
        failhard = (uu___294_12058.failhard);
        nosynth = (uu___294_12058.nosynth);
        uvar_subtyping = (uu___294_12058.uvar_subtyping);
        tc_term = (uu___294_12058.tc_term);
        type_of = (uu___294_12058.type_of);
        universe_of = (uu___294_12058.universe_of);
        check_type_of = (uu___294_12058.check_type_of);
        use_bv_sorts = (uu___294_12058.use_bv_sorts);
        qtbl_name_and_index = (uu___294_12058.qtbl_name_and_index);
        normalized_eff_names = (uu___294_12058.normalized_eff_names);
        fv_delta_depths = (uu___294_12058.fv_delta_depths);
        proof_ns = (uu___294_12058.proof_ns);
        synth_hook = (uu___294_12058.synth_hook);
        splice = (uu___294_12058.splice);
        postprocess = (uu___294_12058.postprocess);
        is_native_tactic = (uu___294_12058.is_native_tactic);
        identifier_info = (uu___294_12058.identifier_info);
        tc_hooks = (uu___294_12058.tc_hooks);
        dsenv = uu____12059;
        nbe = (uu___294_12058.nbe)
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
      | (NoDelta ,uu____12088) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12091,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12093,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12096 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____12110 . unit -> 'Auu____12110 FStar_Util.smap =
  fun uu____12117  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12123 . unit -> 'Auu____12123 FStar_Util.smap =
  fun uu____12130  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____12268 = new_gamma_cache ()  in
                  let uu____12271 = new_sigtab ()  in
                  let uu____12274 = new_sigtab ()  in
                  let uu____12281 =
                    let uu____12296 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12296, FStar_Pervasives_Native.None)  in
                  let uu____12317 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12321 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12325 = FStar_Options.using_facts_from ()  in
                  let uu____12326 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12329 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12268;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12271;
                    attrtab = uu____12274;
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
                    qtbl_name_and_index = uu____12281;
                    normalized_eff_names = uu____12317;
                    fv_delta_depths = uu____12321;
                    proof_ns = uu____12325;
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
                    is_native_tactic = (fun uu____12391  -> false);
                    identifier_info = uu____12326;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12329;
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
  fun uu____12503  ->
    let uu____12504 = FStar_ST.op_Bang query_indices  in
    match uu____12504 with
    | [] -> failwith "Empty query indices!"
    | uu____12559 ->
        let uu____12569 =
          let uu____12579 =
            let uu____12587 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12587  in
          let uu____12641 = FStar_ST.op_Bang query_indices  in uu____12579 ::
            uu____12641
           in
        FStar_ST.op_Colon_Equals query_indices uu____12569
  
let (pop_query_indices : unit -> unit) =
  fun uu____12737  ->
    let uu____12738 = FStar_ST.op_Bang query_indices  in
    match uu____12738 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____12865  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____12902  ->
    match uu____12902 with
    | (l,n1) ->
        let uu____12912 = FStar_ST.op_Bang query_indices  in
        (match uu____12912 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13034 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____13057  ->
    let uu____13058 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13058
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13137 =
       let uu____13140 = FStar_ST.op_Bang stack  in env :: uu____13140  in
     FStar_ST.op_Colon_Equals stack uu____13137);
    (let uu___295_13189 = env  in
     let uu____13190 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13193 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13196 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13203 =
       let uu____13218 =
         let uu____13222 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13222  in
       let uu____13254 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13218, uu____13254)  in
     let uu____13303 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13306 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13309 =
       let uu____13312 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13312  in
     {
       solver = (uu___295_13189.solver);
       range = (uu___295_13189.range);
       curmodule = (uu___295_13189.curmodule);
       gamma = (uu___295_13189.gamma);
       gamma_sig = (uu___295_13189.gamma_sig);
       gamma_cache = uu____13190;
       modules = (uu___295_13189.modules);
       expected_typ = (uu___295_13189.expected_typ);
       sigtab = uu____13193;
       attrtab = uu____13196;
       is_pattern = (uu___295_13189.is_pattern);
       instantiate_imp = (uu___295_13189.instantiate_imp);
       effects = (uu___295_13189.effects);
       generalize = (uu___295_13189.generalize);
       letrecs = (uu___295_13189.letrecs);
       top_level = (uu___295_13189.top_level);
       check_uvars = (uu___295_13189.check_uvars);
       use_eq = (uu___295_13189.use_eq);
       is_iface = (uu___295_13189.is_iface);
       admit = (uu___295_13189.admit);
       lax = (uu___295_13189.lax);
       lax_universes = (uu___295_13189.lax_universes);
       phase1 = (uu___295_13189.phase1);
       failhard = (uu___295_13189.failhard);
       nosynth = (uu___295_13189.nosynth);
       uvar_subtyping = (uu___295_13189.uvar_subtyping);
       tc_term = (uu___295_13189.tc_term);
       type_of = (uu___295_13189.type_of);
       universe_of = (uu___295_13189.universe_of);
       check_type_of = (uu___295_13189.check_type_of);
       use_bv_sorts = (uu___295_13189.use_bv_sorts);
       qtbl_name_and_index = uu____13203;
       normalized_eff_names = uu____13303;
       fv_delta_depths = uu____13306;
       proof_ns = (uu___295_13189.proof_ns);
       synth_hook = (uu___295_13189.synth_hook);
       splice = (uu___295_13189.splice);
       postprocess = (uu___295_13189.postprocess);
       is_native_tactic = (uu___295_13189.is_native_tactic);
       identifier_info = uu____13309;
       tc_hooks = (uu___295_13189.tc_hooks);
       dsenv = (uu___295_13189.dsenv);
       nbe = (uu___295_13189.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13359  ->
    let uu____13360 = FStar_ST.op_Bang stack  in
    match uu____13360 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13414 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13504  ->
           let uu____13505 = snapshot_stack env  in
           match uu____13505 with
           | (stack_depth,env1) ->
               let uu____13539 = snapshot_query_indices ()  in
               (match uu____13539 with
                | (query_indices_depth,()) ->
                    let uu____13572 = (env1.solver).snapshot msg  in
                    (match uu____13572 with
                     | (solver_depth,()) ->
                         let uu____13629 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13629 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___296_13696 = env1  in
                                 {
                                   solver = (uu___296_13696.solver);
                                   range = (uu___296_13696.range);
                                   curmodule = (uu___296_13696.curmodule);
                                   gamma = (uu___296_13696.gamma);
                                   gamma_sig = (uu___296_13696.gamma_sig);
                                   gamma_cache = (uu___296_13696.gamma_cache);
                                   modules = (uu___296_13696.modules);
                                   expected_typ =
                                     (uu___296_13696.expected_typ);
                                   sigtab = (uu___296_13696.sigtab);
                                   attrtab = (uu___296_13696.attrtab);
                                   is_pattern = (uu___296_13696.is_pattern);
                                   instantiate_imp =
                                     (uu___296_13696.instantiate_imp);
                                   effects = (uu___296_13696.effects);
                                   generalize = (uu___296_13696.generalize);
                                   letrecs = (uu___296_13696.letrecs);
                                   top_level = (uu___296_13696.top_level);
                                   check_uvars = (uu___296_13696.check_uvars);
                                   use_eq = (uu___296_13696.use_eq);
                                   is_iface = (uu___296_13696.is_iface);
                                   admit = (uu___296_13696.admit);
                                   lax = (uu___296_13696.lax);
                                   lax_universes =
                                     (uu___296_13696.lax_universes);
                                   phase1 = (uu___296_13696.phase1);
                                   failhard = (uu___296_13696.failhard);
                                   nosynth = (uu___296_13696.nosynth);
                                   uvar_subtyping =
                                     (uu___296_13696.uvar_subtyping);
                                   tc_term = (uu___296_13696.tc_term);
                                   type_of = (uu___296_13696.type_of);
                                   universe_of = (uu___296_13696.universe_of);
                                   check_type_of =
                                     (uu___296_13696.check_type_of);
                                   use_bv_sorts =
                                     (uu___296_13696.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___296_13696.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___296_13696.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___296_13696.fv_delta_depths);
                                   proof_ns = (uu___296_13696.proof_ns);
                                   synth_hook = (uu___296_13696.synth_hook);
                                   splice = (uu___296_13696.splice);
                                   postprocess = (uu___296_13696.postprocess);
                                   is_native_tactic =
                                     (uu___296_13696.is_native_tactic);
                                   identifier_info =
                                     (uu___296_13696.identifier_info);
                                   tc_hooks = (uu___296_13696.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___296_13696.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13730  ->
             let uu____13731 =
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
             match uu____13731 with
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
                             ((let uu____13911 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13911
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13927 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13927
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____13959,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14001 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14031  ->
                  match uu____14031 with
                  | (m,uu____14039) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14001 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___297_14054 = env  in
               {
                 solver = (uu___297_14054.solver);
                 range = (uu___297_14054.range);
                 curmodule = (uu___297_14054.curmodule);
                 gamma = (uu___297_14054.gamma);
                 gamma_sig = (uu___297_14054.gamma_sig);
                 gamma_cache = (uu___297_14054.gamma_cache);
                 modules = (uu___297_14054.modules);
                 expected_typ = (uu___297_14054.expected_typ);
                 sigtab = (uu___297_14054.sigtab);
                 attrtab = (uu___297_14054.attrtab);
                 is_pattern = (uu___297_14054.is_pattern);
                 instantiate_imp = (uu___297_14054.instantiate_imp);
                 effects = (uu___297_14054.effects);
                 generalize = (uu___297_14054.generalize);
                 letrecs = (uu___297_14054.letrecs);
                 top_level = (uu___297_14054.top_level);
                 check_uvars = (uu___297_14054.check_uvars);
                 use_eq = (uu___297_14054.use_eq);
                 is_iface = (uu___297_14054.is_iface);
                 admit = (uu___297_14054.admit);
                 lax = (uu___297_14054.lax);
                 lax_universes = (uu___297_14054.lax_universes);
                 phase1 = (uu___297_14054.phase1);
                 failhard = (uu___297_14054.failhard);
                 nosynth = (uu___297_14054.nosynth);
                 uvar_subtyping = (uu___297_14054.uvar_subtyping);
                 tc_term = (uu___297_14054.tc_term);
                 type_of = (uu___297_14054.type_of);
                 universe_of = (uu___297_14054.universe_of);
                 check_type_of = (uu___297_14054.check_type_of);
                 use_bv_sorts = (uu___297_14054.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___297_14054.normalized_eff_names);
                 fv_delta_depths = (uu___297_14054.fv_delta_depths);
                 proof_ns = (uu___297_14054.proof_ns);
                 synth_hook = (uu___297_14054.synth_hook);
                 splice = (uu___297_14054.splice);
                 postprocess = (uu___297_14054.postprocess);
                 is_native_tactic = (uu___297_14054.is_native_tactic);
                 identifier_info = (uu___297_14054.identifier_info);
                 tc_hooks = (uu___297_14054.tc_hooks);
                 dsenv = (uu___297_14054.dsenv);
                 nbe = (uu___297_14054.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____14071,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___298_14087 = env  in
               {
                 solver = (uu___298_14087.solver);
                 range = (uu___298_14087.range);
                 curmodule = (uu___298_14087.curmodule);
                 gamma = (uu___298_14087.gamma);
                 gamma_sig = (uu___298_14087.gamma_sig);
                 gamma_cache = (uu___298_14087.gamma_cache);
                 modules = (uu___298_14087.modules);
                 expected_typ = (uu___298_14087.expected_typ);
                 sigtab = (uu___298_14087.sigtab);
                 attrtab = (uu___298_14087.attrtab);
                 is_pattern = (uu___298_14087.is_pattern);
                 instantiate_imp = (uu___298_14087.instantiate_imp);
                 effects = (uu___298_14087.effects);
                 generalize = (uu___298_14087.generalize);
                 letrecs = (uu___298_14087.letrecs);
                 top_level = (uu___298_14087.top_level);
                 check_uvars = (uu___298_14087.check_uvars);
                 use_eq = (uu___298_14087.use_eq);
                 is_iface = (uu___298_14087.is_iface);
                 admit = (uu___298_14087.admit);
                 lax = (uu___298_14087.lax);
                 lax_universes = (uu___298_14087.lax_universes);
                 phase1 = (uu___298_14087.phase1);
                 failhard = (uu___298_14087.failhard);
                 nosynth = (uu___298_14087.nosynth);
                 uvar_subtyping = (uu___298_14087.uvar_subtyping);
                 tc_term = (uu___298_14087.tc_term);
                 type_of = (uu___298_14087.type_of);
                 universe_of = (uu___298_14087.universe_of);
                 check_type_of = (uu___298_14087.check_type_of);
                 use_bv_sorts = (uu___298_14087.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___298_14087.normalized_eff_names);
                 fv_delta_depths = (uu___298_14087.fv_delta_depths);
                 proof_ns = (uu___298_14087.proof_ns);
                 synth_hook = (uu___298_14087.synth_hook);
                 splice = (uu___298_14087.splice);
                 postprocess = (uu___298_14087.postprocess);
                 is_native_tactic = (uu___298_14087.is_native_tactic);
                 identifier_info = (uu___298_14087.identifier_info);
                 tc_hooks = (uu___298_14087.tc_hooks);
                 dsenv = (uu___298_14087.dsenv);
                 nbe = (uu___298_14087.nbe)
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
        (let uu___299_14130 = e  in
         {
           solver = (uu___299_14130.solver);
           range = r;
           curmodule = (uu___299_14130.curmodule);
           gamma = (uu___299_14130.gamma);
           gamma_sig = (uu___299_14130.gamma_sig);
           gamma_cache = (uu___299_14130.gamma_cache);
           modules = (uu___299_14130.modules);
           expected_typ = (uu___299_14130.expected_typ);
           sigtab = (uu___299_14130.sigtab);
           attrtab = (uu___299_14130.attrtab);
           is_pattern = (uu___299_14130.is_pattern);
           instantiate_imp = (uu___299_14130.instantiate_imp);
           effects = (uu___299_14130.effects);
           generalize = (uu___299_14130.generalize);
           letrecs = (uu___299_14130.letrecs);
           top_level = (uu___299_14130.top_level);
           check_uvars = (uu___299_14130.check_uvars);
           use_eq = (uu___299_14130.use_eq);
           is_iface = (uu___299_14130.is_iface);
           admit = (uu___299_14130.admit);
           lax = (uu___299_14130.lax);
           lax_universes = (uu___299_14130.lax_universes);
           phase1 = (uu___299_14130.phase1);
           failhard = (uu___299_14130.failhard);
           nosynth = (uu___299_14130.nosynth);
           uvar_subtyping = (uu___299_14130.uvar_subtyping);
           tc_term = (uu___299_14130.tc_term);
           type_of = (uu___299_14130.type_of);
           universe_of = (uu___299_14130.universe_of);
           check_type_of = (uu___299_14130.check_type_of);
           use_bv_sorts = (uu___299_14130.use_bv_sorts);
           qtbl_name_and_index = (uu___299_14130.qtbl_name_and_index);
           normalized_eff_names = (uu___299_14130.normalized_eff_names);
           fv_delta_depths = (uu___299_14130.fv_delta_depths);
           proof_ns = (uu___299_14130.proof_ns);
           synth_hook = (uu___299_14130.synth_hook);
           splice = (uu___299_14130.splice);
           postprocess = (uu___299_14130.postprocess);
           is_native_tactic = (uu___299_14130.is_native_tactic);
           identifier_info = (uu___299_14130.identifier_info);
           tc_hooks = (uu___299_14130.tc_hooks);
           dsenv = (uu___299_14130.dsenv);
           nbe = (uu___299_14130.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14150 =
        let uu____14151 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14151 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14150
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14206 =
          let uu____14207 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14207 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14206
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14262 =
          let uu____14263 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14263 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14262
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14318 =
        let uu____14319 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14319 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14318
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___300_14383 = env  in
      {
        solver = (uu___300_14383.solver);
        range = (uu___300_14383.range);
        curmodule = lid;
        gamma = (uu___300_14383.gamma);
        gamma_sig = (uu___300_14383.gamma_sig);
        gamma_cache = (uu___300_14383.gamma_cache);
        modules = (uu___300_14383.modules);
        expected_typ = (uu___300_14383.expected_typ);
        sigtab = (uu___300_14383.sigtab);
        attrtab = (uu___300_14383.attrtab);
        is_pattern = (uu___300_14383.is_pattern);
        instantiate_imp = (uu___300_14383.instantiate_imp);
        effects = (uu___300_14383.effects);
        generalize = (uu___300_14383.generalize);
        letrecs = (uu___300_14383.letrecs);
        top_level = (uu___300_14383.top_level);
        check_uvars = (uu___300_14383.check_uvars);
        use_eq = (uu___300_14383.use_eq);
        is_iface = (uu___300_14383.is_iface);
        admit = (uu___300_14383.admit);
        lax = (uu___300_14383.lax);
        lax_universes = (uu___300_14383.lax_universes);
        phase1 = (uu___300_14383.phase1);
        failhard = (uu___300_14383.failhard);
        nosynth = (uu___300_14383.nosynth);
        uvar_subtyping = (uu___300_14383.uvar_subtyping);
        tc_term = (uu___300_14383.tc_term);
        type_of = (uu___300_14383.type_of);
        universe_of = (uu___300_14383.universe_of);
        check_type_of = (uu___300_14383.check_type_of);
        use_bv_sorts = (uu___300_14383.use_bv_sorts);
        qtbl_name_and_index = (uu___300_14383.qtbl_name_and_index);
        normalized_eff_names = (uu___300_14383.normalized_eff_names);
        fv_delta_depths = (uu___300_14383.fv_delta_depths);
        proof_ns = (uu___300_14383.proof_ns);
        synth_hook = (uu___300_14383.synth_hook);
        splice = (uu___300_14383.splice);
        postprocess = (uu___300_14383.postprocess);
        is_native_tactic = (uu___300_14383.is_native_tactic);
        identifier_info = (uu___300_14383.identifier_info);
        tc_hooks = (uu___300_14383.tc_hooks);
        dsenv = (uu___300_14383.dsenv);
        nbe = (uu___300_14383.nbe)
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
      let uu____14414 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14414
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14427 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14427)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14442 =
      let uu____14444 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14444  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14442)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14453  ->
    let uu____14454 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14454
  
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
      | ((formals,t),uu____14554) ->
          let vs = mk_univ_subst formals us  in
          let uu____14578 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14578)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___278_14595  ->
    match uu___278_14595 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14621  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14641 = inst_tscheme t  in
      match uu____14641 with
      | (us,t1) ->
          let uu____14652 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14652)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14673  ->
          match uu____14673 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____14695 =
                         let uu____14697 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____14701 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____14705 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____14707 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____14697 uu____14701 uu____14705 uu____14707
                          in
                       failwith uu____14695)
                    else ();
                    (let uu____14712 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____14712))
               | uu____14721 ->
                   let uu____14722 =
                     let uu____14724 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____14724
                      in
                   failwith uu____14722)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14736 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14747 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14758 -> false
  
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
             | ([],uu____14806) -> Maybe
             | (uu____14813,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14833 -> No  in
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
          let uu____14927 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14927 with
          | FStar_Pervasives_Native.None  ->
              let uu____14950 =
                FStar_Util.find_map env.gamma
                  (fun uu___279_14994  ->
                     match uu___279_14994 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15033 = FStar_Ident.lid_equals lid l  in
                         if uu____15033
                         then
                           let uu____15056 =
                             let uu____15075 =
                               let uu____15090 = inst_tscheme t  in
                               FStar_Util.Inl uu____15090  in
                             let uu____15105 = FStar_Ident.range_of_lid l  in
                             (uu____15075, uu____15105)  in
                           FStar_Pervasives_Native.Some uu____15056
                         else FStar_Pervasives_Native.None
                     | uu____15158 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____14950
                (fun uu____15196  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___280_15205  ->
                        match uu___280_15205 with
                        | (uu____15208,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15210);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15211;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15212;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15213;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15214;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15234 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15234
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
                                  uu____15286 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15293 -> cache t  in
                            let uu____15294 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15294 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15300 =
                                   let uu____15301 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15301)
                                    in
                                 maybe_cache uu____15300)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15372 = find_in_sigtab env lid  in
         match uu____15372 with
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
      let uu____15453 = lookup_qname env lid  in
      match uu____15453 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15474,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15588 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15588 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15633 =
          let uu____15636 = lookup_attr env1 attr  in se1 :: uu____15636  in
        FStar_Util.smap_add (attrtab env1) attr uu____15633  in
      FStar_List.iter
        (fun attr  ->
           let uu____15646 =
             let uu____15647 = FStar_Syntax_Subst.compress attr  in
             uu____15647.FStar_Syntax_Syntax.n  in
           match uu____15646 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15651 =
                 let uu____15653 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15653.FStar_Ident.str  in
               add_one1 env se uu____15651
           | uu____15654 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15677) ->
          add_sigelts env ses
      | uu____15686 ->
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
            | uu____15701 -> ()))

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
        (fun uu___281_15733  ->
           match uu___281_15733 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15751 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____15813,lb::[]),uu____15815) ->
            let uu____15824 =
              let uu____15833 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15842 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15833, uu____15842)  in
            FStar_Pervasives_Native.Some uu____15824
        | FStar_Syntax_Syntax.Sig_let ((uu____15855,lbs),uu____15857) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15889 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15902 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15902
                     then
                       let uu____15915 =
                         let uu____15924 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____15933 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15924, uu____15933)  in
                       FStar_Pervasives_Native.Some uu____15915
                     else FStar_Pervasives_Native.None)
        | uu____15956 -> FStar_Pervasives_Native.None
  
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
          let uu____16016 =
            let uu____16025 =
              let uu____16030 =
                let uu____16031 =
                  let uu____16034 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____16034
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____16031)  in
              inst_tscheme1 uu____16030  in
            (uu____16025, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16016
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16056,uu____16057) ->
          let uu____16062 =
            let uu____16071 =
              let uu____16076 =
                let uu____16077 =
                  let uu____16080 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16080  in
                (us, uu____16077)  in
              inst_tscheme1 uu____16076  in
            (uu____16071, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16062
      | uu____16099 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16188 =
          match uu____16188 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16284,uvs,t,uu____16287,uu____16288,uu____16289);
                      FStar_Syntax_Syntax.sigrng = uu____16290;
                      FStar_Syntax_Syntax.sigquals = uu____16291;
                      FStar_Syntax_Syntax.sigmeta = uu____16292;
                      FStar_Syntax_Syntax.sigattrs = uu____16293;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16316 =
                     let uu____16325 = inst_tscheme1 (uvs, t)  in
                     (uu____16325, rng)  in
                   FStar_Pervasives_Native.Some uu____16316
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16349;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16351;
                      FStar_Syntax_Syntax.sigattrs = uu____16352;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16369 =
                     let uu____16371 = in_cur_mod env l  in uu____16371 = Yes
                      in
                   if uu____16369
                   then
                     let uu____16383 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16383
                      then
                        let uu____16399 =
                          let uu____16408 = inst_tscheme1 (uvs, t)  in
                          (uu____16408, rng)  in
                        FStar_Pervasives_Native.Some uu____16399
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16441 =
                        let uu____16450 = inst_tscheme1 (uvs, t)  in
                        (uu____16450, rng)  in
                      FStar_Pervasives_Native.Some uu____16441)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16475,uu____16476);
                      FStar_Syntax_Syntax.sigrng = uu____16477;
                      FStar_Syntax_Syntax.sigquals = uu____16478;
                      FStar_Syntax_Syntax.sigmeta = uu____16479;
                      FStar_Syntax_Syntax.sigattrs = uu____16480;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16521 =
                          let uu____16530 = inst_tscheme1 (uvs, k)  in
                          (uu____16530, rng)  in
                        FStar_Pervasives_Native.Some uu____16521
                    | uu____16551 ->
                        let uu____16552 =
                          let uu____16561 =
                            let uu____16566 =
                              let uu____16567 =
                                let uu____16570 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16570
                                 in
                              (uvs, uu____16567)  in
                            inst_tscheme1 uu____16566  in
                          (uu____16561, rng)  in
                        FStar_Pervasives_Native.Some uu____16552)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16593,uu____16594);
                      FStar_Syntax_Syntax.sigrng = uu____16595;
                      FStar_Syntax_Syntax.sigquals = uu____16596;
                      FStar_Syntax_Syntax.sigmeta = uu____16597;
                      FStar_Syntax_Syntax.sigattrs = uu____16598;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16640 =
                          let uu____16649 = inst_tscheme_with (uvs, k) us  in
                          (uu____16649, rng)  in
                        FStar_Pervasives_Native.Some uu____16640
                    | uu____16670 ->
                        let uu____16671 =
                          let uu____16680 =
                            let uu____16685 =
                              let uu____16686 =
                                let uu____16689 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16689
                                 in
                              (uvs, uu____16686)  in
                            inst_tscheme_with uu____16685 us  in
                          (uu____16680, rng)  in
                        FStar_Pervasives_Native.Some uu____16671)
               | FStar_Util.Inr se ->
                   let uu____16725 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16746;
                          FStar_Syntax_Syntax.sigrng = uu____16747;
                          FStar_Syntax_Syntax.sigquals = uu____16748;
                          FStar_Syntax_Syntax.sigmeta = uu____16749;
                          FStar_Syntax_Syntax.sigattrs = uu____16750;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16765 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____16725
                     (FStar_Util.map_option
                        (fun uu____16813  ->
                           match uu____16813 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16844 =
          let uu____16855 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16855 mapper  in
        match uu____16844 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____16929 =
              let uu____16940 =
                let uu____16947 =
                  let uu___301_16950 = t  in
                  let uu____16951 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___301_16950.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____16951;
                    FStar_Syntax_Syntax.vars =
                      (uu___301_16950.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____16947)  in
              (uu____16940, r)  in
            FStar_Pervasives_Native.Some uu____16929
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17000 = lookup_qname env l  in
      match uu____17000 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17021 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17075 = try_lookup_bv env bv  in
      match uu____17075 with
      | FStar_Pervasives_Native.None  ->
          let uu____17090 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17090 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17106 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17107 =
            let uu____17108 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17108  in
          (uu____17106, uu____17107)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17130 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17130 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17196 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17196  in
          let uu____17197 =
            let uu____17206 =
              let uu____17211 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17211)  in
            (uu____17206, r1)  in
          FStar_Pervasives_Native.Some uu____17197
  
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
        let uu____17246 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17246 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17279,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17304 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17304  in
            let uu____17305 =
              let uu____17310 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17310, r1)  in
            FStar_Pervasives_Native.Some uu____17305
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17334 = try_lookup_lid env l  in
      match uu____17334 with
      | FStar_Pervasives_Native.None  ->
          let uu____17361 = name_not_found l  in
          let uu____17367 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17361 uu____17367
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___282_17410  ->
              match uu___282_17410 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17414 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17435 = lookup_qname env lid  in
      match uu____17435 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17444,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17447;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17449;
              FStar_Syntax_Syntax.sigattrs = uu____17450;_},FStar_Pervasives_Native.None
            ),uu____17451)
          ->
          let uu____17500 =
            let uu____17507 =
              let uu____17508 =
                let uu____17511 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17511 t  in
              (uvs, uu____17508)  in
            (uu____17507, q)  in
          FStar_Pervasives_Native.Some uu____17500
      | uu____17524 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17546 = lookup_qname env lid  in
      match uu____17546 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17551,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17554;
              FStar_Syntax_Syntax.sigquals = uu____17555;
              FStar_Syntax_Syntax.sigmeta = uu____17556;
              FStar_Syntax_Syntax.sigattrs = uu____17557;_},FStar_Pervasives_Native.None
            ),uu____17558)
          ->
          let uu____17607 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17607 (uvs, t)
      | uu____17612 ->
          let uu____17613 = name_not_found lid  in
          let uu____17619 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17613 uu____17619
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17639 = lookup_qname env lid  in
      match uu____17639 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17644,uvs,t,uu____17647,uu____17648,uu____17649);
              FStar_Syntax_Syntax.sigrng = uu____17650;
              FStar_Syntax_Syntax.sigquals = uu____17651;
              FStar_Syntax_Syntax.sigmeta = uu____17652;
              FStar_Syntax_Syntax.sigattrs = uu____17653;_},FStar_Pervasives_Native.None
            ),uu____17654)
          ->
          let uu____17709 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17709 (uvs, t)
      | uu____17714 ->
          let uu____17715 = name_not_found lid  in
          let uu____17721 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17715 uu____17721
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17744 = lookup_qname env lid  in
      match uu____17744 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17752,uu____17753,uu____17754,uu____17755,uu____17756,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17758;
              FStar_Syntax_Syntax.sigquals = uu____17759;
              FStar_Syntax_Syntax.sigmeta = uu____17760;
              FStar_Syntax_Syntax.sigattrs = uu____17761;_},uu____17762),uu____17763)
          -> (true, dcs)
      | uu____17826 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17842 = lookup_qname env lid  in
      match uu____17842 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17843,uu____17844,uu____17845,l,uu____17847,uu____17848);
              FStar_Syntax_Syntax.sigrng = uu____17849;
              FStar_Syntax_Syntax.sigquals = uu____17850;
              FStar_Syntax_Syntax.sigmeta = uu____17851;
              FStar_Syntax_Syntax.sigattrs = uu____17852;_},uu____17853),uu____17854)
          -> l
      | uu____17911 ->
          let uu____17912 =
            let uu____17914 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____17914  in
          failwith uu____17912
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____17984)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18041) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18065 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18065
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18100 -> FStar_Pervasives_Native.None)
          | uu____18109 -> FStar_Pervasives_Native.None
  
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
        let uu____18171 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18171
  
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
        let uu____18204 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18204
  
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
             (FStar_Util.Inl uu____18256,uu____18257) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18306),uu____18307) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18356 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18374 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18384 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18401 ->
                  let uu____18408 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18408
              | FStar_Syntax_Syntax.Sig_let ((uu____18409,lbs),uu____18411)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18427 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18427
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18434 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18442 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18443 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18450 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18451 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18452 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18453 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18466 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18484 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18484
           (fun d_opt  ->
              let uu____18497 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18497
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18507 =
                   let uu____18510 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18510  in
                 match uu____18507 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18511 =
                       let uu____18513 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18513
                        in
                     failwith uu____18511
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18518 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18518
                       then
                         let uu____18521 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18523 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18525 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18521 uu____18523 uu____18525
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
        (FStar_Util.Inr (se,uu____18550),uu____18551) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18600 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18622),uu____18623) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18672 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18694 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18694
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____18717 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____18717 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18741 =
                      let uu____18742 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18742.FStar_Syntax_Syntax.n  in
                    match uu____18741 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____18747 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____18764 = lookup_qname env ftv  in
      match uu____18764 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18768) ->
          let uu____18813 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____18813 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____18834,t),r) ->
               let uu____18849 =
                 let uu____18850 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____18850 t  in
               FStar_Pervasives_Native.Some uu____18849)
      | uu____18851 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____18863 = try_lookup_effect_lid env ftv  in
      match uu____18863 with
      | FStar_Pervasives_Native.None  ->
          let uu____18866 = name_not_found ftv  in
          let uu____18872 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____18866 uu____18872
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
        let uu____18896 = lookup_qname env lid0  in
        match uu____18896 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____18907);
                FStar_Syntax_Syntax.sigrng = uu____18908;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____18910;
                FStar_Syntax_Syntax.sigattrs = uu____18911;_},FStar_Pervasives_Native.None
              ),uu____18912)
            ->
            let lid1 =
              let uu____18966 =
                let uu____18967 = FStar_Ident.range_of_lid lid  in
                let uu____18968 =
                  let uu____18969 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____18969  in
                FStar_Range.set_use_range uu____18967 uu____18968  in
              FStar_Ident.set_lid_range lid uu____18966  in
            let uu____18970 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___283_18976  ->
                      match uu___283_18976 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____18979 -> false))
               in
            if uu____18970
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____18998 =
                      let uu____19000 =
                        let uu____19002 = get_range env  in
                        FStar_Range.string_of_range uu____19002  in
                      let uu____19003 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19005 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19000 uu____19003 uu____19005
                       in
                    failwith uu____18998)
                  in
               match (binders, univs1) with
               | ([],uu____19026) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19052,uu____19053::uu____19054::uu____19055) ->
                   let uu____19076 =
                     let uu____19078 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19080 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19078 uu____19080
                      in
                   failwith uu____19076
               | uu____19091 ->
                   let uu____19106 =
                     let uu____19111 =
                       let uu____19112 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19112)  in
                     inst_tscheme_with uu____19111 insts  in
                   (match uu____19106 with
                    | (uu____19125,t) ->
                        let t1 =
                          let uu____19128 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19128 t  in
                        let uu____19129 =
                          let uu____19130 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19130.FStar_Syntax_Syntax.n  in
                        (match uu____19129 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19165 -> failwith "Impossible")))
        | uu____19173 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19197 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19197 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19210,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19217 = find1 l2  in
            (match uu____19217 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19224 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19224 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19228 = find1 l  in
            (match uu____19228 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19233 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19233
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19248 = lookup_qname env l1  in
      match uu____19248 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19251;
              FStar_Syntax_Syntax.sigrng = uu____19252;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19254;
              FStar_Syntax_Syntax.sigattrs = uu____19255;_},uu____19256),uu____19257)
          -> q
      | uu____19308 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19332 =
          let uu____19333 =
            let uu____19335 = FStar_Util.string_of_int i  in
            let uu____19337 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19335 uu____19337
             in
          failwith uu____19333  in
        let uu____19340 = lookup_datacon env lid  in
        match uu____19340 with
        | (uu____19345,t) ->
            let uu____19347 =
              let uu____19348 = FStar_Syntax_Subst.compress t  in
              uu____19348.FStar_Syntax_Syntax.n  in
            (match uu____19347 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19352) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19396 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19396
                      FStar_Pervasives_Native.fst)
             | uu____19407 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19421 = lookup_qname env l  in
      match uu____19421 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19423,uu____19424,uu____19425);
              FStar_Syntax_Syntax.sigrng = uu____19426;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19428;
              FStar_Syntax_Syntax.sigattrs = uu____19429;_},uu____19430),uu____19431)
          ->
          FStar_Util.for_some
            (fun uu___284_19484  ->
               match uu___284_19484 with
               | FStar_Syntax_Syntax.Projector uu____19486 -> true
               | uu____19492 -> false) quals
      | uu____19494 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19508 = lookup_qname env lid  in
      match uu____19508 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19510,uu____19511,uu____19512,uu____19513,uu____19514,uu____19515);
              FStar_Syntax_Syntax.sigrng = uu____19516;
              FStar_Syntax_Syntax.sigquals = uu____19517;
              FStar_Syntax_Syntax.sigmeta = uu____19518;
              FStar_Syntax_Syntax.sigattrs = uu____19519;_},uu____19520),uu____19521)
          -> true
      | uu____19579 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19593 = lookup_qname env lid  in
      match uu____19593 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19595,uu____19596,uu____19597,uu____19598,uu____19599,uu____19600);
              FStar_Syntax_Syntax.sigrng = uu____19601;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19603;
              FStar_Syntax_Syntax.sigattrs = uu____19604;_},uu____19605),uu____19606)
          ->
          FStar_Util.for_some
            (fun uu___285_19667  ->
               match uu___285_19667 with
               | FStar_Syntax_Syntax.RecordType uu____19669 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19679 -> true
               | uu____19689 -> false) quals
      | uu____19691 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19701,uu____19702);
            FStar_Syntax_Syntax.sigrng = uu____19703;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19705;
            FStar_Syntax_Syntax.sigattrs = uu____19706;_},uu____19707),uu____19708)
        ->
        FStar_Util.for_some
          (fun uu___286_19765  ->
             match uu___286_19765 with
             | FStar_Syntax_Syntax.Action uu____19767 -> true
             | uu____19769 -> false) quals
    | uu____19771 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19785 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____19785
  
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
      let uu____19802 =
        let uu____19803 = FStar_Syntax_Util.un_uinst head1  in
        uu____19803.FStar_Syntax_Syntax.n  in
      match uu____19802 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____19809 ->
               true
           | uu____19812 -> false)
      | uu____19814 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19828 = lookup_qname env l  in
      match uu____19828 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____19831),uu____19832) ->
          FStar_Util.for_some
            (fun uu___287_19880  ->
               match uu___287_19880 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____19883 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____19885 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____19961 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____19979) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____19997 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20005 ->
                 FStar_Pervasives_Native.Some true
             | uu____20024 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20027 =
        let uu____20031 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20031 mapper  in
      match uu____20027 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20091 = lookup_qname env lid  in
      match uu____20091 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20095,uu____20096,tps,uu____20098,uu____20099,uu____20100);
              FStar_Syntax_Syntax.sigrng = uu____20101;
              FStar_Syntax_Syntax.sigquals = uu____20102;
              FStar_Syntax_Syntax.sigmeta = uu____20103;
              FStar_Syntax_Syntax.sigattrs = uu____20104;_},uu____20105),uu____20106)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20172 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20218  ->
              match uu____20218 with
              | (d,uu____20227) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20243 = effect_decl_opt env l  in
      match uu____20243 with
      | FStar_Pervasives_Native.None  ->
          let uu____20258 = name_not_found l  in
          let uu____20264 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20258 uu____20264
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20287  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20306  ->
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
        let uu____20338 = FStar_Ident.lid_equals l1 l2  in
        if uu____20338
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20349 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20349
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20360 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20413  ->
                        match uu____20413 with
                        | (m1,m2,uu____20427,uu____20428,uu____20429) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20360 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20446 =
                    let uu____20452 =
                      let uu____20454 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20456 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20454
                        uu____20456
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20452)
                     in
                  FStar_Errors.raise_error uu____20446 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20466,uu____20467,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20501 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20501
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
  'Auu____20521 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20521) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20550 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20576  ->
                match uu____20576 with
                | (d,uu____20583) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20550 with
      | FStar_Pervasives_Native.None  ->
          let uu____20594 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20594
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20609 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____20609 with
           | (uu____20624,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20642)::(wp,uu____20644)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20700 -> failwith "Impossible"))
  
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
          let uu____20758 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____20758
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____20763 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____20763
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
                  let uu____20774 = get_range env  in
                  let uu____20775 =
                    let uu____20782 =
                      let uu____20783 =
                        let uu____20800 =
                          let uu____20811 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____20811]  in
                        (null_wp, uu____20800)  in
                      FStar_Syntax_Syntax.Tm_app uu____20783  in
                    FStar_Syntax_Syntax.mk uu____20782  in
                  uu____20775 FStar_Pervasives_Native.None uu____20774  in
                let uu____20851 =
                  let uu____20852 =
                    let uu____20863 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____20863]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____20852;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____20851))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___302_20901 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___302_20901.order);
              joins = (uu___302_20901.joins)
            }  in
          let uu___303_20910 = env  in
          {
            solver = (uu___303_20910.solver);
            range = (uu___303_20910.range);
            curmodule = (uu___303_20910.curmodule);
            gamma = (uu___303_20910.gamma);
            gamma_sig = (uu___303_20910.gamma_sig);
            gamma_cache = (uu___303_20910.gamma_cache);
            modules = (uu___303_20910.modules);
            expected_typ = (uu___303_20910.expected_typ);
            sigtab = (uu___303_20910.sigtab);
            attrtab = (uu___303_20910.attrtab);
            is_pattern = (uu___303_20910.is_pattern);
            instantiate_imp = (uu___303_20910.instantiate_imp);
            effects;
            generalize = (uu___303_20910.generalize);
            letrecs = (uu___303_20910.letrecs);
            top_level = (uu___303_20910.top_level);
            check_uvars = (uu___303_20910.check_uvars);
            use_eq = (uu___303_20910.use_eq);
            is_iface = (uu___303_20910.is_iface);
            admit = (uu___303_20910.admit);
            lax = (uu___303_20910.lax);
            lax_universes = (uu___303_20910.lax_universes);
            phase1 = (uu___303_20910.phase1);
            failhard = (uu___303_20910.failhard);
            nosynth = (uu___303_20910.nosynth);
            uvar_subtyping = (uu___303_20910.uvar_subtyping);
            tc_term = (uu___303_20910.tc_term);
            type_of = (uu___303_20910.type_of);
            universe_of = (uu___303_20910.universe_of);
            check_type_of = (uu___303_20910.check_type_of);
            use_bv_sorts = (uu___303_20910.use_bv_sorts);
            qtbl_name_and_index = (uu___303_20910.qtbl_name_and_index);
            normalized_eff_names = (uu___303_20910.normalized_eff_names);
            fv_delta_depths = (uu___303_20910.fv_delta_depths);
            proof_ns = (uu___303_20910.proof_ns);
            synth_hook = (uu___303_20910.synth_hook);
            splice = (uu___303_20910.splice);
            postprocess = (uu___303_20910.postprocess);
            is_native_tactic = (uu___303_20910.is_native_tactic);
            identifier_info = (uu___303_20910.identifier_info);
            tc_hooks = (uu___303_20910.tc_hooks);
            dsenv = (uu___303_20910.dsenv);
            nbe = (uu___303_20910.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____20940 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____20940  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____21098 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____21099 = l1 u t wp e  in
                                l2 u t uu____21098 uu____21099))
                | uu____21100 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21172 = inst_tscheme_with lift_t [u]  in
            match uu____21172 with
            | (uu____21179,lift_t1) ->
                let uu____21181 =
                  let uu____21188 =
                    let uu____21189 =
                      let uu____21206 =
                        let uu____21217 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21226 =
                          let uu____21237 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21237]  in
                        uu____21217 :: uu____21226  in
                      (lift_t1, uu____21206)  in
                    FStar_Syntax_Syntax.Tm_app uu____21189  in
                  FStar_Syntax_Syntax.mk uu____21188  in
                uu____21181 FStar_Pervasives_Native.None
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
            let uu____21350 = inst_tscheme_with lift_t [u]  in
            match uu____21350 with
            | (uu____21357,lift_t1) ->
                let uu____21359 =
                  let uu____21366 =
                    let uu____21367 =
                      let uu____21384 =
                        let uu____21395 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21404 =
                          let uu____21415 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21424 =
                            let uu____21435 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21435]  in
                          uu____21415 :: uu____21424  in
                        uu____21395 :: uu____21404  in
                      (lift_t1, uu____21384)  in
                    FStar_Syntax_Syntax.Tm_app uu____21367  in
                  FStar_Syntax_Syntax.mk uu____21366  in
                uu____21359 FStar_Pervasives_Native.None
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
              let uu____21540 =
                let uu____21541 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21541
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21540  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21550 =
              let uu____21552 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21552  in
            let uu____21553 =
              let uu____21555 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21583 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21583)
                 in
              FStar_Util.dflt "none" uu____21555  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21550
              uu____21553
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21612  ->
                    match uu____21612 with
                    | (e,uu____21620) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21643 =
            match uu____21643 with
            | (i,j) ->
                let uu____21654 = FStar_Ident.lid_equals i j  in
                if uu____21654
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
              let uu____21689 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____21699 = FStar_Ident.lid_equals i k  in
                        if uu____21699
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____21713 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____21713
                                  then []
                                  else
                                    (let uu____21720 =
                                       let uu____21729 =
                                         find_edge order1 (i, k)  in
                                       let uu____21732 =
                                         find_edge order1 (k, j)  in
                                       (uu____21729, uu____21732)  in
                                     match uu____21720 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____21747 =
                                           compose_edges e1 e2  in
                                         [uu____21747]
                                     | uu____21748 -> [])))))
                 in
              FStar_List.append order1 uu____21689  in
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
                   let uu____21778 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____21781 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____21781
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____21778
                   then
                     let uu____21788 =
                       let uu____21794 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____21794)
                        in
                     let uu____21798 = get_range env  in
                     FStar_Errors.raise_error uu____21788 uu____21798
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____21876 = FStar_Ident.lid_equals i j
                                   in
                                if uu____21876
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____21928 =
                                              let uu____21937 =
                                                find_edge order2 (i, k)  in
                                              let uu____21940 =
                                                find_edge order2 (j, k)  in
                                              (uu____21937, uu____21940)  in
                                            match uu____21928 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____21982,uu____21983)
                                                     ->
                                                     let uu____21990 =
                                                       let uu____21997 =
                                                         let uu____21999 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21999
                                                          in
                                                       let uu____22002 =
                                                         let uu____22004 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22004
                                                          in
                                                       (uu____21997,
                                                         uu____22002)
                                                        in
                                                     (match uu____21990 with
                                                      | (true ,true ) ->
                                                          let uu____22021 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____22021
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
                                            | uu____22064 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___304_22137 = env.effects  in
              { decls = (uu___304_22137.decls); order = order2; joins }  in
            let uu___305_22138 = env  in
            {
              solver = (uu___305_22138.solver);
              range = (uu___305_22138.range);
              curmodule = (uu___305_22138.curmodule);
              gamma = (uu___305_22138.gamma);
              gamma_sig = (uu___305_22138.gamma_sig);
              gamma_cache = (uu___305_22138.gamma_cache);
              modules = (uu___305_22138.modules);
              expected_typ = (uu___305_22138.expected_typ);
              sigtab = (uu___305_22138.sigtab);
              attrtab = (uu___305_22138.attrtab);
              is_pattern = (uu___305_22138.is_pattern);
              instantiate_imp = (uu___305_22138.instantiate_imp);
              effects;
              generalize = (uu___305_22138.generalize);
              letrecs = (uu___305_22138.letrecs);
              top_level = (uu___305_22138.top_level);
              check_uvars = (uu___305_22138.check_uvars);
              use_eq = (uu___305_22138.use_eq);
              is_iface = (uu___305_22138.is_iface);
              admit = (uu___305_22138.admit);
              lax = (uu___305_22138.lax);
              lax_universes = (uu___305_22138.lax_universes);
              phase1 = (uu___305_22138.phase1);
              failhard = (uu___305_22138.failhard);
              nosynth = (uu___305_22138.nosynth);
              uvar_subtyping = (uu___305_22138.uvar_subtyping);
              tc_term = (uu___305_22138.tc_term);
              type_of = (uu___305_22138.type_of);
              universe_of = (uu___305_22138.universe_of);
              check_type_of = (uu___305_22138.check_type_of);
              use_bv_sorts = (uu___305_22138.use_bv_sorts);
              qtbl_name_and_index = (uu___305_22138.qtbl_name_and_index);
              normalized_eff_names = (uu___305_22138.normalized_eff_names);
              fv_delta_depths = (uu___305_22138.fv_delta_depths);
              proof_ns = (uu___305_22138.proof_ns);
              synth_hook = (uu___305_22138.synth_hook);
              splice = (uu___305_22138.splice);
              postprocess = (uu___305_22138.postprocess);
              is_native_tactic = (uu___305_22138.is_native_tactic);
              identifier_info = (uu___305_22138.identifier_info);
              tc_hooks = (uu___305_22138.tc_hooks);
              dsenv = (uu___305_22138.dsenv);
              nbe = (uu___305_22138.nbe)
            }))
      | uu____22139 -> env
  
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
        | uu____22168 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22181 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22181 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22198 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22198 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____22223 =
                     let uu____22229 =
                       let uu____22231 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22239 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22250 =
                         let uu____22252 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22252  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22231 uu____22239 uu____22250
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22229)
                      in
                   FStar_Errors.raise_error uu____22223
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22260 =
                     let uu____22271 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22271 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22308  ->
                        fun uu____22309  ->
                          match (uu____22308, uu____22309) with
                          | ((x,uu____22339),(t,uu____22341)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22260
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22372 =
                     let uu___306_22373 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___306_22373.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___306_22373.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___306_22373.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___306_22373.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22372
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22385 .
    'Auu____22385 ->
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
          let uu____22415 = effect_decl_opt env effect_name  in
          match uu____22415 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22454 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22477 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22516 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____22516
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22521 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22521
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22536 =
                     let uu____22539 = get_range env  in
                     let uu____22540 =
                       let uu____22547 =
                         let uu____22548 =
                           let uu____22565 =
                             let uu____22576 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22576; wp]  in
                           (repr, uu____22565)  in
                         FStar_Syntax_Syntax.Tm_app uu____22548  in
                       FStar_Syntax_Syntax.mk uu____22547  in
                     uu____22540 FStar_Pervasives_Native.None uu____22539  in
                   FStar_Pervasives_Native.Some uu____22536)
  
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
      | uu____22723 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22738 =
        let uu____22739 = FStar_Syntax_Subst.compress t  in
        uu____22739.FStar_Syntax_Syntax.n  in
      match uu____22738 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22743,c) ->
          is_reifiable_comp env c
      | uu____22765 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22785 =
           let uu____22787 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22787  in
         if uu____22785
         then
           let uu____22790 =
             let uu____22796 =
               let uu____22798 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22798
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22796)  in
           let uu____22802 = get_range env  in
           FStar_Errors.raise_error uu____22790 uu____22802
         else ());
        (let uu____22805 = effect_repr_aux true env c u_c  in
         match uu____22805 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___307_22841 = env  in
        {
          solver = (uu___307_22841.solver);
          range = (uu___307_22841.range);
          curmodule = (uu___307_22841.curmodule);
          gamma = (uu___307_22841.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___307_22841.gamma_cache);
          modules = (uu___307_22841.modules);
          expected_typ = (uu___307_22841.expected_typ);
          sigtab = (uu___307_22841.sigtab);
          attrtab = (uu___307_22841.attrtab);
          is_pattern = (uu___307_22841.is_pattern);
          instantiate_imp = (uu___307_22841.instantiate_imp);
          effects = (uu___307_22841.effects);
          generalize = (uu___307_22841.generalize);
          letrecs = (uu___307_22841.letrecs);
          top_level = (uu___307_22841.top_level);
          check_uvars = (uu___307_22841.check_uvars);
          use_eq = (uu___307_22841.use_eq);
          is_iface = (uu___307_22841.is_iface);
          admit = (uu___307_22841.admit);
          lax = (uu___307_22841.lax);
          lax_universes = (uu___307_22841.lax_universes);
          phase1 = (uu___307_22841.phase1);
          failhard = (uu___307_22841.failhard);
          nosynth = (uu___307_22841.nosynth);
          uvar_subtyping = (uu___307_22841.uvar_subtyping);
          tc_term = (uu___307_22841.tc_term);
          type_of = (uu___307_22841.type_of);
          universe_of = (uu___307_22841.universe_of);
          check_type_of = (uu___307_22841.check_type_of);
          use_bv_sorts = (uu___307_22841.use_bv_sorts);
          qtbl_name_and_index = (uu___307_22841.qtbl_name_and_index);
          normalized_eff_names = (uu___307_22841.normalized_eff_names);
          fv_delta_depths = (uu___307_22841.fv_delta_depths);
          proof_ns = (uu___307_22841.proof_ns);
          synth_hook = (uu___307_22841.synth_hook);
          splice = (uu___307_22841.splice);
          postprocess = (uu___307_22841.postprocess);
          is_native_tactic = (uu___307_22841.is_native_tactic);
          identifier_info = (uu___307_22841.identifier_info);
          tc_hooks = (uu___307_22841.tc_hooks);
          dsenv = (uu___307_22841.dsenv);
          nbe = (uu___307_22841.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___308_22855 = env  in
      {
        solver = (uu___308_22855.solver);
        range = (uu___308_22855.range);
        curmodule = (uu___308_22855.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___308_22855.gamma_sig);
        gamma_cache = (uu___308_22855.gamma_cache);
        modules = (uu___308_22855.modules);
        expected_typ = (uu___308_22855.expected_typ);
        sigtab = (uu___308_22855.sigtab);
        attrtab = (uu___308_22855.attrtab);
        is_pattern = (uu___308_22855.is_pattern);
        instantiate_imp = (uu___308_22855.instantiate_imp);
        effects = (uu___308_22855.effects);
        generalize = (uu___308_22855.generalize);
        letrecs = (uu___308_22855.letrecs);
        top_level = (uu___308_22855.top_level);
        check_uvars = (uu___308_22855.check_uvars);
        use_eq = (uu___308_22855.use_eq);
        is_iface = (uu___308_22855.is_iface);
        admit = (uu___308_22855.admit);
        lax = (uu___308_22855.lax);
        lax_universes = (uu___308_22855.lax_universes);
        phase1 = (uu___308_22855.phase1);
        failhard = (uu___308_22855.failhard);
        nosynth = (uu___308_22855.nosynth);
        uvar_subtyping = (uu___308_22855.uvar_subtyping);
        tc_term = (uu___308_22855.tc_term);
        type_of = (uu___308_22855.type_of);
        universe_of = (uu___308_22855.universe_of);
        check_type_of = (uu___308_22855.check_type_of);
        use_bv_sorts = (uu___308_22855.use_bv_sorts);
        qtbl_name_and_index = (uu___308_22855.qtbl_name_and_index);
        normalized_eff_names = (uu___308_22855.normalized_eff_names);
        fv_delta_depths = (uu___308_22855.fv_delta_depths);
        proof_ns = (uu___308_22855.proof_ns);
        synth_hook = (uu___308_22855.synth_hook);
        splice = (uu___308_22855.splice);
        postprocess = (uu___308_22855.postprocess);
        is_native_tactic = (uu___308_22855.is_native_tactic);
        identifier_info = (uu___308_22855.identifier_info);
        tc_hooks = (uu___308_22855.tc_hooks);
        dsenv = (uu___308_22855.dsenv);
        nbe = (uu___308_22855.nbe)
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
            (let uu___309_22913 = env  in
             {
               solver = (uu___309_22913.solver);
               range = (uu___309_22913.range);
               curmodule = (uu___309_22913.curmodule);
               gamma = rest;
               gamma_sig = (uu___309_22913.gamma_sig);
               gamma_cache = (uu___309_22913.gamma_cache);
               modules = (uu___309_22913.modules);
               expected_typ = (uu___309_22913.expected_typ);
               sigtab = (uu___309_22913.sigtab);
               attrtab = (uu___309_22913.attrtab);
               is_pattern = (uu___309_22913.is_pattern);
               instantiate_imp = (uu___309_22913.instantiate_imp);
               effects = (uu___309_22913.effects);
               generalize = (uu___309_22913.generalize);
               letrecs = (uu___309_22913.letrecs);
               top_level = (uu___309_22913.top_level);
               check_uvars = (uu___309_22913.check_uvars);
               use_eq = (uu___309_22913.use_eq);
               is_iface = (uu___309_22913.is_iface);
               admit = (uu___309_22913.admit);
               lax = (uu___309_22913.lax);
               lax_universes = (uu___309_22913.lax_universes);
               phase1 = (uu___309_22913.phase1);
               failhard = (uu___309_22913.failhard);
               nosynth = (uu___309_22913.nosynth);
               uvar_subtyping = (uu___309_22913.uvar_subtyping);
               tc_term = (uu___309_22913.tc_term);
               type_of = (uu___309_22913.type_of);
               universe_of = (uu___309_22913.universe_of);
               check_type_of = (uu___309_22913.check_type_of);
               use_bv_sorts = (uu___309_22913.use_bv_sorts);
               qtbl_name_and_index = (uu___309_22913.qtbl_name_and_index);
               normalized_eff_names = (uu___309_22913.normalized_eff_names);
               fv_delta_depths = (uu___309_22913.fv_delta_depths);
               proof_ns = (uu___309_22913.proof_ns);
               synth_hook = (uu___309_22913.synth_hook);
               splice = (uu___309_22913.splice);
               postprocess = (uu___309_22913.postprocess);
               is_native_tactic = (uu___309_22913.is_native_tactic);
               identifier_info = (uu___309_22913.identifier_info);
               tc_hooks = (uu___309_22913.tc_hooks);
               dsenv = (uu___309_22913.dsenv);
               nbe = (uu___309_22913.nbe)
             }))
    | uu____22914 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____22943  ->
             match uu____22943 with | (x,uu____22951) -> push_bv env1 x) env
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
            let uu___310_22986 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___310_22986.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___310_22986.FStar_Syntax_Syntax.index);
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
      (let uu___311_23028 = env  in
       {
         solver = (uu___311_23028.solver);
         range = (uu___311_23028.range);
         curmodule = (uu___311_23028.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___311_23028.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___311_23028.sigtab);
         attrtab = (uu___311_23028.attrtab);
         is_pattern = (uu___311_23028.is_pattern);
         instantiate_imp = (uu___311_23028.instantiate_imp);
         effects = (uu___311_23028.effects);
         generalize = (uu___311_23028.generalize);
         letrecs = (uu___311_23028.letrecs);
         top_level = (uu___311_23028.top_level);
         check_uvars = (uu___311_23028.check_uvars);
         use_eq = (uu___311_23028.use_eq);
         is_iface = (uu___311_23028.is_iface);
         admit = (uu___311_23028.admit);
         lax = (uu___311_23028.lax);
         lax_universes = (uu___311_23028.lax_universes);
         phase1 = (uu___311_23028.phase1);
         failhard = (uu___311_23028.failhard);
         nosynth = (uu___311_23028.nosynth);
         uvar_subtyping = (uu___311_23028.uvar_subtyping);
         tc_term = (uu___311_23028.tc_term);
         type_of = (uu___311_23028.type_of);
         universe_of = (uu___311_23028.universe_of);
         check_type_of = (uu___311_23028.check_type_of);
         use_bv_sorts = (uu___311_23028.use_bv_sorts);
         qtbl_name_and_index = (uu___311_23028.qtbl_name_and_index);
         normalized_eff_names = (uu___311_23028.normalized_eff_names);
         fv_delta_depths = (uu___311_23028.fv_delta_depths);
         proof_ns = (uu___311_23028.proof_ns);
         synth_hook = (uu___311_23028.synth_hook);
         splice = (uu___311_23028.splice);
         postprocess = (uu___311_23028.postprocess);
         is_native_tactic = (uu___311_23028.is_native_tactic);
         identifier_info = (uu___311_23028.identifier_info);
         tc_hooks = (uu___311_23028.tc_hooks);
         dsenv = (uu___311_23028.dsenv);
         nbe = (uu___311_23028.nbe)
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
        let uu____23072 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23072 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23100 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23100)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___312_23116 = env  in
      {
        solver = (uu___312_23116.solver);
        range = (uu___312_23116.range);
        curmodule = (uu___312_23116.curmodule);
        gamma = (uu___312_23116.gamma);
        gamma_sig = (uu___312_23116.gamma_sig);
        gamma_cache = (uu___312_23116.gamma_cache);
        modules = (uu___312_23116.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___312_23116.sigtab);
        attrtab = (uu___312_23116.attrtab);
        is_pattern = (uu___312_23116.is_pattern);
        instantiate_imp = (uu___312_23116.instantiate_imp);
        effects = (uu___312_23116.effects);
        generalize = (uu___312_23116.generalize);
        letrecs = (uu___312_23116.letrecs);
        top_level = (uu___312_23116.top_level);
        check_uvars = (uu___312_23116.check_uvars);
        use_eq = false;
        is_iface = (uu___312_23116.is_iface);
        admit = (uu___312_23116.admit);
        lax = (uu___312_23116.lax);
        lax_universes = (uu___312_23116.lax_universes);
        phase1 = (uu___312_23116.phase1);
        failhard = (uu___312_23116.failhard);
        nosynth = (uu___312_23116.nosynth);
        uvar_subtyping = (uu___312_23116.uvar_subtyping);
        tc_term = (uu___312_23116.tc_term);
        type_of = (uu___312_23116.type_of);
        universe_of = (uu___312_23116.universe_of);
        check_type_of = (uu___312_23116.check_type_of);
        use_bv_sorts = (uu___312_23116.use_bv_sorts);
        qtbl_name_and_index = (uu___312_23116.qtbl_name_and_index);
        normalized_eff_names = (uu___312_23116.normalized_eff_names);
        fv_delta_depths = (uu___312_23116.fv_delta_depths);
        proof_ns = (uu___312_23116.proof_ns);
        synth_hook = (uu___312_23116.synth_hook);
        splice = (uu___312_23116.splice);
        postprocess = (uu___312_23116.postprocess);
        is_native_tactic = (uu___312_23116.is_native_tactic);
        identifier_info = (uu___312_23116.identifier_info);
        tc_hooks = (uu___312_23116.tc_hooks);
        dsenv = (uu___312_23116.dsenv);
        nbe = (uu___312_23116.nbe)
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
    let uu____23147 = expected_typ env_  in
    ((let uu___313_23153 = env_  in
      {
        solver = (uu___313_23153.solver);
        range = (uu___313_23153.range);
        curmodule = (uu___313_23153.curmodule);
        gamma = (uu___313_23153.gamma);
        gamma_sig = (uu___313_23153.gamma_sig);
        gamma_cache = (uu___313_23153.gamma_cache);
        modules = (uu___313_23153.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___313_23153.sigtab);
        attrtab = (uu___313_23153.attrtab);
        is_pattern = (uu___313_23153.is_pattern);
        instantiate_imp = (uu___313_23153.instantiate_imp);
        effects = (uu___313_23153.effects);
        generalize = (uu___313_23153.generalize);
        letrecs = (uu___313_23153.letrecs);
        top_level = (uu___313_23153.top_level);
        check_uvars = (uu___313_23153.check_uvars);
        use_eq = false;
        is_iface = (uu___313_23153.is_iface);
        admit = (uu___313_23153.admit);
        lax = (uu___313_23153.lax);
        lax_universes = (uu___313_23153.lax_universes);
        phase1 = (uu___313_23153.phase1);
        failhard = (uu___313_23153.failhard);
        nosynth = (uu___313_23153.nosynth);
        uvar_subtyping = (uu___313_23153.uvar_subtyping);
        tc_term = (uu___313_23153.tc_term);
        type_of = (uu___313_23153.type_of);
        universe_of = (uu___313_23153.universe_of);
        check_type_of = (uu___313_23153.check_type_of);
        use_bv_sorts = (uu___313_23153.use_bv_sorts);
        qtbl_name_and_index = (uu___313_23153.qtbl_name_and_index);
        normalized_eff_names = (uu___313_23153.normalized_eff_names);
        fv_delta_depths = (uu___313_23153.fv_delta_depths);
        proof_ns = (uu___313_23153.proof_ns);
        synth_hook = (uu___313_23153.synth_hook);
        splice = (uu___313_23153.splice);
        postprocess = (uu___313_23153.postprocess);
        is_native_tactic = (uu___313_23153.is_native_tactic);
        identifier_info = (uu___313_23153.identifier_info);
        tc_hooks = (uu___313_23153.tc_hooks);
        dsenv = (uu___313_23153.dsenv);
        nbe = (uu___313_23153.nbe)
      }), uu____23147)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23165 =
      let uu____23168 = FStar_Ident.id_of_text ""  in [uu____23168]  in
    FStar_Ident.lid_of_ids uu____23165  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23175 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23175
        then
          let uu____23180 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23180 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___314_23208 = env  in
       {
         solver = (uu___314_23208.solver);
         range = (uu___314_23208.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___314_23208.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___314_23208.expected_typ);
         sigtab = (uu___314_23208.sigtab);
         attrtab = (uu___314_23208.attrtab);
         is_pattern = (uu___314_23208.is_pattern);
         instantiate_imp = (uu___314_23208.instantiate_imp);
         effects = (uu___314_23208.effects);
         generalize = (uu___314_23208.generalize);
         letrecs = (uu___314_23208.letrecs);
         top_level = (uu___314_23208.top_level);
         check_uvars = (uu___314_23208.check_uvars);
         use_eq = (uu___314_23208.use_eq);
         is_iface = (uu___314_23208.is_iface);
         admit = (uu___314_23208.admit);
         lax = (uu___314_23208.lax);
         lax_universes = (uu___314_23208.lax_universes);
         phase1 = (uu___314_23208.phase1);
         failhard = (uu___314_23208.failhard);
         nosynth = (uu___314_23208.nosynth);
         uvar_subtyping = (uu___314_23208.uvar_subtyping);
         tc_term = (uu___314_23208.tc_term);
         type_of = (uu___314_23208.type_of);
         universe_of = (uu___314_23208.universe_of);
         check_type_of = (uu___314_23208.check_type_of);
         use_bv_sorts = (uu___314_23208.use_bv_sorts);
         qtbl_name_and_index = (uu___314_23208.qtbl_name_and_index);
         normalized_eff_names = (uu___314_23208.normalized_eff_names);
         fv_delta_depths = (uu___314_23208.fv_delta_depths);
         proof_ns = (uu___314_23208.proof_ns);
         synth_hook = (uu___314_23208.synth_hook);
         splice = (uu___314_23208.splice);
         postprocess = (uu___314_23208.postprocess);
         is_native_tactic = (uu___314_23208.is_native_tactic);
         identifier_info = (uu___314_23208.identifier_info);
         tc_hooks = (uu___314_23208.tc_hooks);
         dsenv = (uu___314_23208.dsenv);
         nbe = (uu___314_23208.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23260)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23264,(uu____23265,t)))::tl1
          ->
          let uu____23286 =
            let uu____23289 = FStar_Syntax_Free.uvars t  in
            ext out uu____23289  in
          aux uu____23286 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23292;
            FStar_Syntax_Syntax.index = uu____23293;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23301 =
            let uu____23304 = FStar_Syntax_Free.uvars t  in
            ext out uu____23304  in
          aux uu____23301 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23362)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23366,(uu____23367,t)))::tl1
          ->
          let uu____23388 =
            let uu____23391 = FStar_Syntax_Free.univs t  in
            ext out uu____23391  in
          aux uu____23388 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23394;
            FStar_Syntax_Syntax.index = uu____23395;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23403 =
            let uu____23406 = FStar_Syntax_Free.univs t  in
            ext out uu____23406  in
          aux uu____23403 tl1
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
          let uu____23468 = FStar_Util.set_add uname out  in
          aux uu____23468 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23471,(uu____23472,t)))::tl1
          ->
          let uu____23493 =
            let uu____23496 = FStar_Syntax_Free.univnames t  in
            ext out uu____23496  in
          aux uu____23493 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23499;
            FStar_Syntax_Syntax.index = uu____23500;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23508 =
            let uu____23511 = FStar_Syntax_Free.univnames t  in
            ext out uu____23511  in
          aux uu____23508 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___288_23532  ->
            match uu___288_23532 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23536 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23549 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23560 =
      let uu____23569 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23569
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23560 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23617 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___289_23630  ->
              match uu___289_23630 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23633 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____23633
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23639) ->
                  let uu____23656 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____23656))
       in
    FStar_All.pipe_right uu____23617 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___290_23670  ->
    match uu___290_23670 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23676 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____23676
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23699  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23754) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____23787,uu____23788) -> false  in
      let uu____23802 =
        FStar_List.tryFind
          (fun uu____23824  ->
             match uu____23824 with | (p,uu____23835) -> list_prefix p path)
          env.proof_ns
         in
      match uu____23802 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23854,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23884 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23884
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___315_23906 = e  in
        {
          solver = (uu___315_23906.solver);
          range = (uu___315_23906.range);
          curmodule = (uu___315_23906.curmodule);
          gamma = (uu___315_23906.gamma);
          gamma_sig = (uu___315_23906.gamma_sig);
          gamma_cache = (uu___315_23906.gamma_cache);
          modules = (uu___315_23906.modules);
          expected_typ = (uu___315_23906.expected_typ);
          sigtab = (uu___315_23906.sigtab);
          attrtab = (uu___315_23906.attrtab);
          is_pattern = (uu___315_23906.is_pattern);
          instantiate_imp = (uu___315_23906.instantiate_imp);
          effects = (uu___315_23906.effects);
          generalize = (uu___315_23906.generalize);
          letrecs = (uu___315_23906.letrecs);
          top_level = (uu___315_23906.top_level);
          check_uvars = (uu___315_23906.check_uvars);
          use_eq = (uu___315_23906.use_eq);
          is_iface = (uu___315_23906.is_iface);
          admit = (uu___315_23906.admit);
          lax = (uu___315_23906.lax);
          lax_universes = (uu___315_23906.lax_universes);
          phase1 = (uu___315_23906.phase1);
          failhard = (uu___315_23906.failhard);
          nosynth = (uu___315_23906.nosynth);
          uvar_subtyping = (uu___315_23906.uvar_subtyping);
          tc_term = (uu___315_23906.tc_term);
          type_of = (uu___315_23906.type_of);
          universe_of = (uu___315_23906.universe_of);
          check_type_of = (uu___315_23906.check_type_of);
          use_bv_sorts = (uu___315_23906.use_bv_sorts);
          qtbl_name_and_index = (uu___315_23906.qtbl_name_and_index);
          normalized_eff_names = (uu___315_23906.normalized_eff_names);
          fv_delta_depths = (uu___315_23906.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___315_23906.synth_hook);
          splice = (uu___315_23906.splice);
          postprocess = (uu___315_23906.postprocess);
          is_native_tactic = (uu___315_23906.is_native_tactic);
          identifier_info = (uu___315_23906.identifier_info);
          tc_hooks = (uu___315_23906.tc_hooks);
          dsenv = (uu___315_23906.dsenv);
          nbe = (uu___315_23906.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___316_23954 = e  in
      {
        solver = (uu___316_23954.solver);
        range = (uu___316_23954.range);
        curmodule = (uu___316_23954.curmodule);
        gamma = (uu___316_23954.gamma);
        gamma_sig = (uu___316_23954.gamma_sig);
        gamma_cache = (uu___316_23954.gamma_cache);
        modules = (uu___316_23954.modules);
        expected_typ = (uu___316_23954.expected_typ);
        sigtab = (uu___316_23954.sigtab);
        attrtab = (uu___316_23954.attrtab);
        is_pattern = (uu___316_23954.is_pattern);
        instantiate_imp = (uu___316_23954.instantiate_imp);
        effects = (uu___316_23954.effects);
        generalize = (uu___316_23954.generalize);
        letrecs = (uu___316_23954.letrecs);
        top_level = (uu___316_23954.top_level);
        check_uvars = (uu___316_23954.check_uvars);
        use_eq = (uu___316_23954.use_eq);
        is_iface = (uu___316_23954.is_iface);
        admit = (uu___316_23954.admit);
        lax = (uu___316_23954.lax);
        lax_universes = (uu___316_23954.lax_universes);
        phase1 = (uu___316_23954.phase1);
        failhard = (uu___316_23954.failhard);
        nosynth = (uu___316_23954.nosynth);
        uvar_subtyping = (uu___316_23954.uvar_subtyping);
        tc_term = (uu___316_23954.tc_term);
        type_of = (uu___316_23954.type_of);
        universe_of = (uu___316_23954.universe_of);
        check_type_of = (uu___316_23954.check_type_of);
        use_bv_sorts = (uu___316_23954.use_bv_sorts);
        qtbl_name_and_index = (uu___316_23954.qtbl_name_and_index);
        normalized_eff_names = (uu___316_23954.normalized_eff_names);
        fv_delta_depths = (uu___316_23954.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___316_23954.synth_hook);
        splice = (uu___316_23954.splice);
        postprocess = (uu___316_23954.postprocess);
        is_native_tactic = (uu___316_23954.is_native_tactic);
        identifier_info = (uu___316_23954.identifier_info);
        tc_hooks = (uu___316_23954.tc_hooks);
        dsenv = (uu___316_23954.dsenv);
        nbe = (uu___316_23954.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____23970 = FStar_Syntax_Free.names t  in
      let uu____23973 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____23970 uu____23973
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____23996 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____23996
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24006 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24006
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24027 =
      match uu____24027 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24047 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____24047)
       in
    let uu____24055 =
      let uu____24059 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24059 FStar_List.rev  in
    FStar_All.pipe_right uu____24055 (FStar_String.concat " ")
  
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
                  (let uu____24129 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24129 with
                   | FStar_Pervasives_Native.Some uu____24133 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24136 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24146;
        univ_ineqs = uu____24147; implicits = uu____24148;_} -> true
    | uu____24160 -> false
  
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
          let uu___317_24191 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___317_24191.deferred);
            univ_ineqs = (uu___317_24191.univ_ineqs);
            implicits = (uu___317_24191.implicits)
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
          let uu____24230 = FStar_Options.defensive ()  in
          if uu____24230
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24236 =
              let uu____24238 =
                let uu____24240 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24240  in
              Prims.op_Negation uu____24238  in
            (if uu____24236
             then
               let uu____24247 =
                 let uu____24253 =
                   let uu____24255 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24257 =
                     let uu____24259 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24259
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24255 uu____24257
                    in
                 (FStar_Errors.Warning_Defensive, uu____24253)  in
               FStar_Errors.log_issue rng uu____24247
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
          let uu____24299 =
            let uu____24301 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24301  in
          if uu____24299
          then ()
          else
            (let uu____24306 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24306 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24332 =
            let uu____24334 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24334  in
          if uu____24332
          then ()
          else
            (let uu____24339 = bound_vars e  in
             def_check_closed_in rng msg uu____24339 t)
  
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
          let uu___318_24378 = g  in
          let uu____24379 =
            let uu____24380 =
              let uu____24381 =
                let uu____24388 =
                  let uu____24389 =
                    let uu____24406 =
                      let uu____24417 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24417]  in
                    (f, uu____24406)  in
                  FStar_Syntax_Syntax.Tm_app uu____24389  in
                FStar_Syntax_Syntax.mk uu____24388  in
              uu____24381 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_2  -> FStar_TypeChecker_Common.NonTrivial _0_2)
              uu____24380
             in
          {
            guard_f = uu____24379;
            deferred = (uu___318_24378.deferred);
            univ_ineqs = (uu___318_24378.univ_ineqs);
            implicits = (uu___318_24378.implicits)
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
          let uu___319_24474 = g  in
          let uu____24475 =
            let uu____24476 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24476  in
          {
            guard_f = uu____24475;
            deferred = (uu___319_24474.deferred);
            univ_ineqs = (uu___319_24474.univ_ineqs);
            implicits = (uu___319_24474.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___320_24493 = g  in
          let uu____24494 =
            let uu____24495 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24495  in
          {
            guard_f = uu____24494;
            deferred = (uu___320_24493.deferred);
            univ_ineqs = (uu___320_24493.univ_ineqs);
            implicits = (uu___320_24493.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___321_24497 = g  in
          let uu____24498 =
            let uu____24499 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24499  in
          {
            guard_f = uu____24498;
            deferred = (uu___321_24497.deferred);
            univ_ineqs = (uu___321_24497.univ_ineqs);
            implicits = (uu___321_24497.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24506 ->
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
          let uu____24523 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24523
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24530 =
      let uu____24531 = FStar_Syntax_Util.unmeta t  in
      uu____24531.FStar_Syntax_Syntax.n  in
    match uu____24530 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24535 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24578 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24578;
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
                       let uu____24673 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24673
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___322_24680 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___322_24680.deferred);
              univ_ineqs = (uu___322_24680.univ_ineqs);
              implicits = (uu___322_24680.implicits)
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
               let uu____24714 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24714
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
            let uu___323_24741 = g  in
            let uu____24742 =
              let uu____24743 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24743  in
            {
              guard_f = uu____24742;
              deferred = (uu___323_24741.deferred);
              univ_ineqs = (uu___323_24741.univ_ineqs);
              implicits = (uu___323_24741.implicits)
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
              let uu____24801 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____24801 with
              | FStar_Pervasives_Native.Some
                  (uu____24826::(tm,uu____24828)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____24892 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____24910 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____24910;
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
                      let uu___324_24942 = trivial_guard  in
                      {
                        guard_f = (uu___324_24942.guard_f);
                        deferred = (uu___324_24942.deferred);
                        univ_ineqs = (uu___324_24942.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____24960  -> ());
    push = (fun uu____24962  -> ());
    pop = (fun uu____24965  -> ());
    snapshot =
      (fun uu____24968  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____24987  -> fun uu____24988  -> ());
    encode_modul = (fun uu____25003  -> fun uu____25004  -> ());
    encode_sig = (fun uu____25007  -> fun uu____25008  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25014 =
             let uu____25021 = FStar_Options.peek ()  in (e, g, uu____25021)
              in
           [uu____25014]);
    solve = (fun uu____25037  -> fun uu____25038  -> fun uu____25039  -> ());
    finish = (fun uu____25046  -> ());
    refresh = (fun uu____25048  -> ())
  } 