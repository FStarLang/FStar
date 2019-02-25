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
  fun projectee  ->
    match projectee with | Beta  -> true | uu____56005 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56016 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56027 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56039 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56058 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56069 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56080 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____56091 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____56102 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____56113 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____56125 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56147 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56175 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56203 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____56228 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____56239 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____56250 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____56261 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____56272 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56283 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____56294 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____56305 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____56316 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____56327 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____56338 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56349 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____56360 -> false
  
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
      | uu____56420 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____56446 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____56457 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____56468 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____56480 -> false
  
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
           (fun uu___446_67742  ->
              match uu___446_67742 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____67745 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____67745  in
                  let uu____67746 =
                    let uu____67747 = FStar_Syntax_Subst.compress y  in
                    uu____67747.FStar_Syntax_Syntax.n  in
                  (match uu____67746 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____67751 =
                         let uu___775_67752 = y1  in
                         let uu____67753 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_67752.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_67752.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____67753
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____67751
                   | uu____67756 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_67770 = env  in
      let uu____67771 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_67770.solver);
        range = (uu___781_67770.range);
        curmodule = (uu___781_67770.curmodule);
        gamma = uu____67771;
        gamma_sig = (uu___781_67770.gamma_sig);
        gamma_cache = (uu___781_67770.gamma_cache);
        modules = (uu___781_67770.modules);
        expected_typ = (uu___781_67770.expected_typ);
        sigtab = (uu___781_67770.sigtab);
        attrtab = (uu___781_67770.attrtab);
        is_pattern = (uu___781_67770.is_pattern);
        instantiate_imp = (uu___781_67770.instantiate_imp);
        effects = (uu___781_67770.effects);
        generalize = (uu___781_67770.generalize);
        letrecs = (uu___781_67770.letrecs);
        top_level = (uu___781_67770.top_level);
        check_uvars = (uu___781_67770.check_uvars);
        use_eq = (uu___781_67770.use_eq);
        is_iface = (uu___781_67770.is_iface);
        admit = (uu___781_67770.admit);
        lax = (uu___781_67770.lax);
        lax_universes = (uu___781_67770.lax_universes);
        phase1 = (uu___781_67770.phase1);
        failhard = (uu___781_67770.failhard);
        nosynth = (uu___781_67770.nosynth);
        uvar_subtyping = (uu___781_67770.uvar_subtyping);
        tc_term = (uu___781_67770.tc_term);
        type_of = (uu___781_67770.type_of);
        universe_of = (uu___781_67770.universe_of);
        check_type_of = (uu___781_67770.check_type_of);
        use_bv_sorts = (uu___781_67770.use_bv_sorts);
        qtbl_name_and_index = (uu___781_67770.qtbl_name_and_index);
        normalized_eff_names = (uu___781_67770.normalized_eff_names);
        fv_delta_depths = (uu___781_67770.fv_delta_depths);
        proof_ns = (uu___781_67770.proof_ns);
        synth_hook = (uu___781_67770.synth_hook);
        splice = (uu___781_67770.splice);
        postprocess = (uu___781_67770.postprocess);
        is_native_tactic = (uu___781_67770.is_native_tactic);
        identifier_info = (uu___781_67770.identifier_info);
        tc_hooks = (uu___781_67770.tc_hooks);
        dsenv = (uu___781_67770.dsenv);
        nbe = (uu___781_67770.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____67779  -> fun uu____67780  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_67802 = env  in
      {
        solver = (uu___788_67802.solver);
        range = (uu___788_67802.range);
        curmodule = (uu___788_67802.curmodule);
        gamma = (uu___788_67802.gamma);
        gamma_sig = (uu___788_67802.gamma_sig);
        gamma_cache = (uu___788_67802.gamma_cache);
        modules = (uu___788_67802.modules);
        expected_typ = (uu___788_67802.expected_typ);
        sigtab = (uu___788_67802.sigtab);
        attrtab = (uu___788_67802.attrtab);
        is_pattern = (uu___788_67802.is_pattern);
        instantiate_imp = (uu___788_67802.instantiate_imp);
        effects = (uu___788_67802.effects);
        generalize = (uu___788_67802.generalize);
        letrecs = (uu___788_67802.letrecs);
        top_level = (uu___788_67802.top_level);
        check_uvars = (uu___788_67802.check_uvars);
        use_eq = (uu___788_67802.use_eq);
        is_iface = (uu___788_67802.is_iface);
        admit = (uu___788_67802.admit);
        lax = (uu___788_67802.lax);
        lax_universes = (uu___788_67802.lax_universes);
        phase1 = (uu___788_67802.phase1);
        failhard = (uu___788_67802.failhard);
        nosynth = (uu___788_67802.nosynth);
        uvar_subtyping = (uu___788_67802.uvar_subtyping);
        tc_term = (uu___788_67802.tc_term);
        type_of = (uu___788_67802.type_of);
        universe_of = (uu___788_67802.universe_of);
        check_type_of = (uu___788_67802.check_type_of);
        use_bv_sorts = (uu___788_67802.use_bv_sorts);
        qtbl_name_and_index = (uu___788_67802.qtbl_name_and_index);
        normalized_eff_names = (uu___788_67802.normalized_eff_names);
        fv_delta_depths = (uu___788_67802.fv_delta_depths);
        proof_ns = (uu___788_67802.proof_ns);
        synth_hook = (uu___788_67802.synth_hook);
        splice = (uu___788_67802.splice);
        postprocess = (uu___788_67802.postprocess);
        is_native_tactic = (uu___788_67802.is_native_tactic);
        identifier_info = (uu___788_67802.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_67802.dsenv);
        nbe = (uu___788_67802.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_67814 = e  in
      let uu____67815 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_67814.solver);
        range = (uu___792_67814.range);
        curmodule = (uu___792_67814.curmodule);
        gamma = (uu___792_67814.gamma);
        gamma_sig = (uu___792_67814.gamma_sig);
        gamma_cache = (uu___792_67814.gamma_cache);
        modules = (uu___792_67814.modules);
        expected_typ = (uu___792_67814.expected_typ);
        sigtab = (uu___792_67814.sigtab);
        attrtab = (uu___792_67814.attrtab);
        is_pattern = (uu___792_67814.is_pattern);
        instantiate_imp = (uu___792_67814.instantiate_imp);
        effects = (uu___792_67814.effects);
        generalize = (uu___792_67814.generalize);
        letrecs = (uu___792_67814.letrecs);
        top_level = (uu___792_67814.top_level);
        check_uvars = (uu___792_67814.check_uvars);
        use_eq = (uu___792_67814.use_eq);
        is_iface = (uu___792_67814.is_iface);
        admit = (uu___792_67814.admit);
        lax = (uu___792_67814.lax);
        lax_universes = (uu___792_67814.lax_universes);
        phase1 = (uu___792_67814.phase1);
        failhard = (uu___792_67814.failhard);
        nosynth = (uu___792_67814.nosynth);
        uvar_subtyping = (uu___792_67814.uvar_subtyping);
        tc_term = (uu___792_67814.tc_term);
        type_of = (uu___792_67814.type_of);
        universe_of = (uu___792_67814.universe_of);
        check_type_of = (uu___792_67814.check_type_of);
        use_bv_sorts = (uu___792_67814.use_bv_sorts);
        qtbl_name_and_index = (uu___792_67814.qtbl_name_and_index);
        normalized_eff_names = (uu___792_67814.normalized_eff_names);
        fv_delta_depths = (uu___792_67814.fv_delta_depths);
        proof_ns = (uu___792_67814.proof_ns);
        synth_hook = (uu___792_67814.synth_hook);
        splice = (uu___792_67814.splice);
        postprocess = (uu___792_67814.postprocess);
        is_native_tactic = (uu___792_67814.is_native_tactic);
        identifier_info = (uu___792_67814.identifier_info);
        tc_hooks = (uu___792_67814.tc_hooks);
        dsenv = uu____67815;
        nbe = (uu___792_67814.nbe)
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
      | (NoDelta ,uu____67844) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____67847,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____67849,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____67852 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____67866 . unit -> 'Auu____67866 FStar_Util.smap =
  fun uu____67873  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____67879 . unit -> 'Auu____67879 FStar_Util.smap =
  fun uu____67886  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____68024 = new_gamma_cache ()  in
                  let uu____68027 = new_sigtab ()  in
                  let uu____68030 = new_sigtab ()  in
                  let uu____68037 =
                    let uu____68052 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____68052, FStar_Pervasives_Native.None)  in
                  let uu____68073 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____68077 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____68081 = FStar_Options.using_facts_from ()  in
                  let uu____68082 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____68085 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____68024;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____68027;
                    attrtab = uu____68030;
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
                    qtbl_name_and_index = uu____68037;
                    normalized_eff_names = uu____68073;
                    fv_delta_depths = uu____68077;
                    proof_ns = uu____68081;
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
                    is_native_tactic = (fun uu____68147  -> false);
                    identifier_info = uu____68082;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____68085;
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
  fun uu____68259  ->
    let uu____68260 = FStar_ST.op_Bang query_indices  in
    match uu____68260 with
    | [] -> failwith "Empty query indices!"
    | uu____68315 ->
        let uu____68325 =
          let uu____68335 =
            let uu____68343 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____68343  in
          let uu____68397 = FStar_ST.op_Bang query_indices  in uu____68335 ::
            uu____68397
           in
        FStar_ST.op_Colon_Equals query_indices uu____68325
  
let (pop_query_indices : unit -> unit) =
  fun uu____68493  ->
    let uu____68494 = FStar_ST.op_Bang query_indices  in
    match uu____68494 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____68621  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____68658  ->
    match uu____68658 with
    | (l,n1) ->
        let uu____68668 = FStar_ST.op_Bang query_indices  in
        (match uu____68668 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____68790 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____68813  ->
    let uu____68814 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____68814
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____68893 =
       let uu____68896 = FStar_ST.op_Bang stack  in env :: uu____68896  in
     FStar_ST.op_Colon_Equals stack uu____68893);
    (let uu___860_68945 = env  in
     let uu____68946 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____68949 = FStar_Util.smap_copy (sigtab env)  in
     let uu____68952 = FStar_Util.smap_copy (attrtab env)  in
     let uu____68959 =
       let uu____68974 =
         let uu____68978 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____68978  in
       let uu____69010 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____68974, uu____69010)  in
     let uu____69059 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____69062 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____69065 =
       let uu____69068 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____69068  in
     {
       solver = (uu___860_68945.solver);
       range = (uu___860_68945.range);
       curmodule = (uu___860_68945.curmodule);
       gamma = (uu___860_68945.gamma);
       gamma_sig = (uu___860_68945.gamma_sig);
       gamma_cache = uu____68946;
       modules = (uu___860_68945.modules);
       expected_typ = (uu___860_68945.expected_typ);
       sigtab = uu____68949;
       attrtab = uu____68952;
       is_pattern = (uu___860_68945.is_pattern);
       instantiate_imp = (uu___860_68945.instantiate_imp);
       effects = (uu___860_68945.effects);
       generalize = (uu___860_68945.generalize);
       letrecs = (uu___860_68945.letrecs);
       top_level = (uu___860_68945.top_level);
       check_uvars = (uu___860_68945.check_uvars);
       use_eq = (uu___860_68945.use_eq);
       is_iface = (uu___860_68945.is_iface);
       admit = (uu___860_68945.admit);
       lax = (uu___860_68945.lax);
       lax_universes = (uu___860_68945.lax_universes);
       phase1 = (uu___860_68945.phase1);
       failhard = (uu___860_68945.failhard);
       nosynth = (uu___860_68945.nosynth);
       uvar_subtyping = (uu___860_68945.uvar_subtyping);
       tc_term = (uu___860_68945.tc_term);
       type_of = (uu___860_68945.type_of);
       universe_of = (uu___860_68945.universe_of);
       check_type_of = (uu___860_68945.check_type_of);
       use_bv_sorts = (uu___860_68945.use_bv_sorts);
       qtbl_name_and_index = uu____68959;
       normalized_eff_names = uu____69059;
       fv_delta_depths = uu____69062;
       proof_ns = (uu___860_68945.proof_ns);
       synth_hook = (uu___860_68945.synth_hook);
       splice = (uu___860_68945.splice);
       postprocess = (uu___860_68945.postprocess);
       is_native_tactic = (uu___860_68945.is_native_tactic);
       identifier_info = uu____69065;
       tc_hooks = (uu___860_68945.tc_hooks);
       dsenv = (uu___860_68945.dsenv);
       nbe = (uu___860_68945.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____69115  ->
    let uu____69116 = FStar_ST.op_Bang stack  in
    match uu____69116 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____69170 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____69260  ->
           let uu____69261 = snapshot_stack env  in
           match uu____69261 with
           | (stack_depth,env1) ->
               let uu____69295 = snapshot_query_indices ()  in
               (match uu____69295 with
                | (query_indices_depth,()) ->
                    let uu____69328 = (env1.solver).snapshot msg  in
                    (match uu____69328 with
                     | (solver_depth,()) ->
                         let uu____69385 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____69385 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_69452 = env1  in
                                 {
                                   solver = (uu___885_69452.solver);
                                   range = (uu___885_69452.range);
                                   curmodule = (uu___885_69452.curmodule);
                                   gamma = (uu___885_69452.gamma);
                                   gamma_sig = (uu___885_69452.gamma_sig);
                                   gamma_cache = (uu___885_69452.gamma_cache);
                                   modules = (uu___885_69452.modules);
                                   expected_typ =
                                     (uu___885_69452.expected_typ);
                                   sigtab = (uu___885_69452.sigtab);
                                   attrtab = (uu___885_69452.attrtab);
                                   is_pattern = (uu___885_69452.is_pattern);
                                   instantiate_imp =
                                     (uu___885_69452.instantiate_imp);
                                   effects = (uu___885_69452.effects);
                                   generalize = (uu___885_69452.generalize);
                                   letrecs = (uu___885_69452.letrecs);
                                   top_level = (uu___885_69452.top_level);
                                   check_uvars = (uu___885_69452.check_uvars);
                                   use_eq = (uu___885_69452.use_eq);
                                   is_iface = (uu___885_69452.is_iface);
                                   admit = (uu___885_69452.admit);
                                   lax = (uu___885_69452.lax);
                                   lax_universes =
                                     (uu___885_69452.lax_universes);
                                   phase1 = (uu___885_69452.phase1);
                                   failhard = (uu___885_69452.failhard);
                                   nosynth = (uu___885_69452.nosynth);
                                   uvar_subtyping =
                                     (uu___885_69452.uvar_subtyping);
                                   tc_term = (uu___885_69452.tc_term);
                                   type_of = (uu___885_69452.type_of);
                                   universe_of = (uu___885_69452.universe_of);
                                   check_type_of =
                                     (uu___885_69452.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_69452.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_69452.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_69452.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_69452.fv_delta_depths);
                                   proof_ns = (uu___885_69452.proof_ns);
                                   synth_hook = (uu___885_69452.synth_hook);
                                   splice = (uu___885_69452.splice);
                                   postprocess = (uu___885_69452.postprocess);
                                   is_native_tactic =
                                     (uu___885_69452.is_native_tactic);
                                   identifier_info =
                                     (uu___885_69452.identifier_info);
                                   tc_hooks = (uu___885_69452.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_69452.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____69486  ->
             let uu____69487 =
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
             match uu____69487 with
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
                             ((let uu____69667 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____69667
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____69683 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____69683
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____69715,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____69757 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____69787  ->
                  match uu____69787 with
                  | (m,uu____69795) -> FStar_Ident.lid_equals l m))
           in
        (match uu____69757 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_69810 = env  in
               {
                 solver = (uu___930_69810.solver);
                 range = (uu___930_69810.range);
                 curmodule = (uu___930_69810.curmodule);
                 gamma = (uu___930_69810.gamma);
                 gamma_sig = (uu___930_69810.gamma_sig);
                 gamma_cache = (uu___930_69810.gamma_cache);
                 modules = (uu___930_69810.modules);
                 expected_typ = (uu___930_69810.expected_typ);
                 sigtab = (uu___930_69810.sigtab);
                 attrtab = (uu___930_69810.attrtab);
                 is_pattern = (uu___930_69810.is_pattern);
                 instantiate_imp = (uu___930_69810.instantiate_imp);
                 effects = (uu___930_69810.effects);
                 generalize = (uu___930_69810.generalize);
                 letrecs = (uu___930_69810.letrecs);
                 top_level = (uu___930_69810.top_level);
                 check_uvars = (uu___930_69810.check_uvars);
                 use_eq = (uu___930_69810.use_eq);
                 is_iface = (uu___930_69810.is_iface);
                 admit = (uu___930_69810.admit);
                 lax = (uu___930_69810.lax);
                 lax_universes = (uu___930_69810.lax_universes);
                 phase1 = (uu___930_69810.phase1);
                 failhard = (uu___930_69810.failhard);
                 nosynth = (uu___930_69810.nosynth);
                 uvar_subtyping = (uu___930_69810.uvar_subtyping);
                 tc_term = (uu___930_69810.tc_term);
                 type_of = (uu___930_69810.type_of);
                 universe_of = (uu___930_69810.universe_of);
                 check_type_of = (uu___930_69810.check_type_of);
                 use_bv_sorts = (uu___930_69810.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_69810.normalized_eff_names);
                 fv_delta_depths = (uu___930_69810.fv_delta_depths);
                 proof_ns = (uu___930_69810.proof_ns);
                 synth_hook = (uu___930_69810.synth_hook);
                 splice = (uu___930_69810.splice);
                 postprocess = (uu___930_69810.postprocess);
                 is_native_tactic = (uu___930_69810.is_native_tactic);
                 identifier_info = (uu___930_69810.identifier_info);
                 tc_hooks = (uu___930_69810.tc_hooks);
                 dsenv = (uu___930_69810.dsenv);
                 nbe = (uu___930_69810.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____69827,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_69843 = env  in
               {
                 solver = (uu___939_69843.solver);
                 range = (uu___939_69843.range);
                 curmodule = (uu___939_69843.curmodule);
                 gamma = (uu___939_69843.gamma);
                 gamma_sig = (uu___939_69843.gamma_sig);
                 gamma_cache = (uu___939_69843.gamma_cache);
                 modules = (uu___939_69843.modules);
                 expected_typ = (uu___939_69843.expected_typ);
                 sigtab = (uu___939_69843.sigtab);
                 attrtab = (uu___939_69843.attrtab);
                 is_pattern = (uu___939_69843.is_pattern);
                 instantiate_imp = (uu___939_69843.instantiate_imp);
                 effects = (uu___939_69843.effects);
                 generalize = (uu___939_69843.generalize);
                 letrecs = (uu___939_69843.letrecs);
                 top_level = (uu___939_69843.top_level);
                 check_uvars = (uu___939_69843.check_uvars);
                 use_eq = (uu___939_69843.use_eq);
                 is_iface = (uu___939_69843.is_iface);
                 admit = (uu___939_69843.admit);
                 lax = (uu___939_69843.lax);
                 lax_universes = (uu___939_69843.lax_universes);
                 phase1 = (uu___939_69843.phase1);
                 failhard = (uu___939_69843.failhard);
                 nosynth = (uu___939_69843.nosynth);
                 uvar_subtyping = (uu___939_69843.uvar_subtyping);
                 tc_term = (uu___939_69843.tc_term);
                 type_of = (uu___939_69843.type_of);
                 universe_of = (uu___939_69843.universe_of);
                 check_type_of = (uu___939_69843.check_type_of);
                 use_bv_sorts = (uu___939_69843.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_69843.normalized_eff_names);
                 fv_delta_depths = (uu___939_69843.fv_delta_depths);
                 proof_ns = (uu___939_69843.proof_ns);
                 synth_hook = (uu___939_69843.synth_hook);
                 splice = (uu___939_69843.splice);
                 postprocess = (uu___939_69843.postprocess);
                 is_native_tactic = (uu___939_69843.is_native_tactic);
                 identifier_info = (uu___939_69843.identifier_info);
                 tc_hooks = (uu___939_69843.tc_hooks);
                 dsenv = (uu___939_69843.dsenv);
                 nbe = (uu___939_69843.nbe)
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
        (let uu___946_69886 = e  in
         {
           solver = (uu___946_69886.solver);
           range = r;
           curmodule = (uu___946_69886.curmodule);
           gamma = (uu___946_69886.gamma);
           gamma_sig = (uu___946_69886.gamma_sig);
           gamma_cache = (uu___946_69886.gamma_cache);
           modules = (uu___946_69886.modules);
           expected_typ = (uu___946_69886.expected_typ);
           sigtab = (uu___946_69886.sigtab);
           attrtab = (uu___946_69886.attrtab);
           is_pattern = (uu___946_69886.is_pattern);
           instantiate_imp = (uu___946_69886.instantiate_imp);
           effects = (uu___946_69886.effects);
           generalize = (uu___946_69886.generalize);
           letrecs = (uu___946_69886.letrecs);
           top_level = (uu___946_69886.top_level);
           check_uvars = (uu___946_69886.check_uvars);
           use_eq = (uu___946_69886.use_eq);
           is_iface = (uu___946_69886.is_iface);
           admit = (uu___946_69886.admit);
           lax = (uu___946_69886.lax);
           lax_universes = (uu___946_69886.lax_universes);
           phase1 = (uu___946_69886.phase1);
           failhard = (uu___946_69886.failhard);
           nosynth = (uu___946_69886.nosynth);
           uvar_subtyping = (uu___946_69886.uvar_subtyping);
           tc_term = (uu___946_69886.tc_term);
           type_of = (uu___946_69886.type_of);
           universe_of = (uu___946_69886.universe_of);
           check_type_of = (uu___946_69886.check_type_of);
           use_bv_sorts = (uu___946_69886.use_bv_sorts);
           qtbl_name_and_index = (uu___946_69886.qtbl_name_and_index);
           normalized_eff_names = (uu___946_69886.normalized_eff_names);
           fv_delta_depths = (uu___946_69886.fv_delta_depths);
           proof_ns = (uu___946_69886.proof_ns);
           synth_hook = (uu___946_69886.synth_hook);
           splice = (uu___946_69886.splice);
           postprocess = (uu___946_69886.postprocess);
           is_native_tactic = (uu___946_69886.is_native_tactic);
           identifier_info = (uu___946_69886.identifier_info);
           tc_hooks = (uu___946_69886.tc_hooks);
           dsenv = (uu___946_69886.dsenv);
           nbe = (uu___946_69886.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____69906 =
        let uu____69907 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____69907 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____69906
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____69962 =
          let uu____69963 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____69963 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____69962
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____70018 =
          let uu____70019 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____70019 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70018
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____70074 =
        let uu____70075 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____70075 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____70074
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_70139 = env  in
      {
        solver = (uu___963_70139.solver);
        range = (uu___963_70139.range);
        curmodule = lid;
        gamma = (uu___963_70139.gamma);
        gamma_sig = (uu___963_70139.gamma_sig);
        gamma_cache = (uu___963_70139.gamma_cache);
        modules = (uu___963_70139.modules);
        expected_typ = (uu___963_70139.expected_typ);
        sigtab = (uu___963_70139.sigtab);
        attrtab = (uu___963_70139.attrtab);
        is_pattern = (uu___963_70139.is_pattern);
        instantiate_imp = (uu___963_70139.instantiate_imp);
        effects = (uu___963_70139.effects);
        generalize = (uu___963_70139.generalize);
        letrecs = (uu___963_70139.letrecs);
        top_level = (uu___963_70139.top_level);
        check_uvars = (uu___963_70139.check_uvars);
        use_eq = (uu___963_70139.use_eq);
        is_iface = (uu___963_70139.is_iface);
        admit = (uu___963_70139.admit);
        lax = (uu___963_70139.lax);
        lax_universes = (uu___963_70139.lax_universes);
        phase1 = (uu___963_70139.phase1);
        failhard = (uu___963_70139.failhard);
        nosynth = (uu___963_70139.nosynth);
        uvar_subtyping = (uu___963_70139.uvar_subtyping);
        tc_term = (uu___963_70139.tc_term);
        type_of = (uu___963_70139.type_of);
        universe_of = (uu___963_70139.universe_of);
        check_type_of = (uu___963_70139.check_type_of);
        use_bv_sorts = (uu___963_70139.use_bv_sorts);
        qtbl_name_and_index = (uu___963_70139.qtbl_name_and_index);
        normalized_eff_names = (uu___963_70139.normalized_eff_names);
        fv_delta_depths = (uu___963_70139.fv_delta_depths);
        proof_ns = (uu___963_70139.proof_ns);
        synth_hook = (uu___963_70139.synth_hook);
        splice = (uu___963_70139.splice);
        postprocess = (uu___963_70139.postprocess);
        is_native_tactic = (uu___963_70139.is_native_tactic);
        identifier_info = (uu___963_70139.identifier_info);
        tc_hooks = (uu___963_70139.tc_hooks);
        dsenv = (uu___963_70139.dsenv);
        nbe = (uu___963_70139.nbe)
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
      let uu____70170 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____70170
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____70183 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____70183)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____70198 =
      let uu____70200 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____70200  in
    (FStar_Errors.Fatal_VariableNotFound, uu____70198)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____70209  ->
    let uu____70210 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____70210
  
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
      | ((formals,t),uu____70310) ->
          let vs = mk_univ_subst formals us  in
          let uu____70334 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____70334)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_70351  ->
    match uu___447_70351 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____70377  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____70397 = inst_tscheme t  in
      match uu____70397 with
      | (us,t1) ->
          let uu____70408 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____70408)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____70429  ->
          match uu____70429 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____70451 =
                         let uu____70453 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____70457 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____70461 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____70463 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____70453 uu____70457 uu____70461 uu____70463
                          in
                       failwith uu____70451)
                    else ();
                    (let uu____70468 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____70468))
               | uu____70477 ->
                   let uu____70478 =
                     let uu____70480 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____70480
                      in
                   failwith uu____70478)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____70492 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____70503 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____70514 -> false
  
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
             | ([],uu____70562) -> Maybe
             | (uu____70569,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____70589 -> No  in
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
          let uu____70683 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____70683 with
          | FStar_Pervasives_Native.None  ->
              let uu____70706 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_70750  ->
                     match uu___448_70750 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____70789 = FStar_Ident.lid_equals lid l  in
                         if uu____70789
                         then
                           let uu____70812 =
                             let uu____70831 =
                               let uu____70846 = inst_tscheme t  in
                               FStar_Util.Inl uu____70846  in
                             let uu____70861 = FStar_Ident.range_of_lid l  in
                             (uu____70831, uu____70861)  in
                           FStar_Pervasives_Native.Some uu____70812
                         else FStar_Pervasives_Native.None
                     | uu____70914 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____70706
                (fun uu____70952  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_70961  ->
                        match uu___449_70961 with
                        | (uu____70964,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____70966);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____70967;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____70968;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____70969;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____70970;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____70990 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____70990
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
                                  uu____71042 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____71049 -> cache t  in
                            let uu____71050 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____71050 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____71056 =
                                   let uu____71057 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____71057)
                                    in
                                 maybe_cache uu____71056)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____71128 = find_in_sigtab env lid  in
         match uu____71128 with
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
      let uu____71209 = lookup_qname env lid  in
      match uu____71209 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____71230,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____71344 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____71344 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____71389 =
          let uu____71392 = lookup_attr env1 attr  in se1 :: uu____71392  in
        FStar_Util.smap_add (attrtab env1) attr uu____71389  in
      FStar_List.iter
        (fun attr  ->
           let uu____71402 =
             let uu____71403 = FStar_Syntax_Subst.compress attr  in
             uu____71403.FStar_Syntax_Syntax.n  in
           match uu____71402 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____71407 =
                 let uu____71409 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____71409.FStar_Ident.str  in
               add_one1 env se uu____71407
           | uu____71410 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____71433) ->
          add_sigelts env ses
      | uu____71442 ->
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
            | uu____71457 -> ()))

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
        (fun uu___450_71489  ->
           match uu___450_71489 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____71507 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____71569,lb::[]),uu____71571) ->
            let uu____71580 =
              let uu____71589 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____71598 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____71589, uu____71598)  in
            FStar_Pervasives_Native.Some uu____71580
        | FStar_Syntax_Syntax.Sig_let ((uu____71611,lbs),uu____71613) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____71645 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____71658 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____71658
                     then
                       let uu____71671 =
                         let uu____71680 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____71689 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____71680, uu____71689)  in
                       FStar_Pervasives_Native.Some uu____71671
                     else FStar_Pervasives_Native.None)
        | uu____71712 -> FStar_Pervasives_Native.None
  
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
          let uu____71772 =
            let uu____71781 =
              let uu____71786 =
                let uu____71787 =
                  let uu____71790 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____71790
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____71787)  in
              inst_tscheme1 uu____71786  in
            (uu____71781, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71772
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____71812,uu____71813) ->
          let uu____71818 =
            let uu____71827 =
              let uu____71832 =
                let uu____71833 =
                  let uu____71836 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____71836  in
                (us, uu____71833)  in
              inst_tscheme1 uu____71832  in
            (uu____71827, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71818
      | uu____71855 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____71944 =
          match uu____71944 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____72040,uvs,t,uu____72043,uu____72044,uu____72045);
                      FStar_Syntax_Syntax.sigrng = uu____72046;
                      FStar_Syntax_Syntax.sigquals = uu____72047;
                      FStar_Syntax_Syntax.sigmeta = uu____72048;
                      FStar_Syntax_Syntax.sigattrs = uu____72049;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72072 =
                     let uu____72081 = inst_tscheme1 (uvs, t)  in
                     (uu____72081, rng)  in
                   FStar_Pervasives_Native.Some uu____72072
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____72105;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____72107;
                      FStar_Syntax_Syntax.sigattrs = uu____72108;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72125 =
                     let uu____72127 = in_cur_mod env l  in uu____72127 = Yes
                      in
                   if uu____72125
                   then
                     let uu____72139 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____72139
                      then
                        let uu____72155 =
                          let uu____72164 = inst_tscheme1 (uvs, t)  in
                          (uu____72164, rng)  in
                        FStar_Pervasives_Native.Some uu____72155
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____72197 =
                        let uu____72206 = inst_tscheme1 (uvs, t)  in
                        (uu____72206, rng)  in
                      FStar_Pervasives_Native.Some uu____72197)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72231,uu____72232);
                      FStar_Syntax_Syntax.sigrng = uu____72233;
                      FStar_Syntax_Syntax.sigquals = uu____72234;
                      FStar_Syntax_Syntax.sigmeta = uu____72235;
                      FStar_Syntax_Syntax.sigattrs = uu____72236;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____72277 =
                          let uu____72286 = inst_tscheme1 (uvs, k)  in
                          (uu____72286, rng)  in
                        FStar_Pervasives_Native.Some uu____72277
                    | uu____72307 ->
                        let uu____72308 =
                          let uu____72317 =
                            let uu____72322 =
                              let uu____72323 =
                                let uu____72326 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72326
                                 in
                              (uvs, uu____72323)  in
                            inst_tscheme1 uu____72322  in
                          (uu____72317, rng)  in
                        FStar_Pervasives_Native.Some uu____72308)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72349,uu____72350);
                      FStar_Syntax_Syntax.sigrng = uu____72351;
                      FStar_Syntax_Syntax.sigquals = uu____72352;
                      FStar_Syntax_Syntax.sigmeta = uu____72353;
                      FStar_Syntax_Syntax.sigattrs = uu____72354;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____72396 =
                          let uu____72405 = inst_tscheme_with (uvs, k) us  in
                          (uu____72405, rng)  in
                        FStar_Pervasives_Native.Some uu____72396
                    | uu____72426 ->
                        let uu____72427 =
                          let uu____72436 =
                            let uu____72441 =
                              let uu____72442 =
                                let uu____72445 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72445
                                 in
                              (uvs, uu____72442)  in
                            inst_tscheme_with uu____72441 us  in
                          (uu____72436, rng)  in
                        FStar_Pervasives_Native.Some uu____72427)
               | FStar_Util.Inr se ->
                   let uu____72481 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____72502;
                          FStar_Syntax_Syntax.sigrng = uu____72503;
                          FStar_Syntax_Syntax.sigquals = uu____72504;
                          FStar_Syntax_Syntax.sigmeta = uu____72505;
                          FStar_Syntax_Syntax.sigattrs = uu____72506;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____72521 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____72481
                     (FStar_Util.map_option
                        (fun uu____72569  ->
                           match uu____72569 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____72600 =
          let uu____72611 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____72611 mapper  in
        match uu____72600 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____72685 =
              let uu____72696 =
                let uu____72703 =
                  let uu___1290_72706 = t  in
                  let uu____72707 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_72706.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____72707;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_72706.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____72703)  in
              (uu____72696, r)  in
            FStar_Pervasives_Native.Some uu____72685
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____72756 = lookup_qname env l  in
      match uu____72756 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____72777 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____72831 = try_lookup_bv env bv  in
      match uu____72831 with
      | FStar_Pervasives_Native.None  ->
          let uu____72846 = variable_not_found bv  in
          FStar_Errors.raise_error uu____72846 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____72862 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____72863 =
            let uu____72864 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____72864  in
          (uu____72862, uu____72863)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____72886 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____72886 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____72952 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____72952  in
          let uu____72953 =
            let uu____72962 =
              let uu____72967 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____72967)  in
            (uu____72962, r1)  in
          FStar_Pervasives_Native.Some uu____72953
  
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
        let uu____73002 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____73002 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____73035,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____73060 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____73060  in
            let uu____73061 =
              let uu____73066 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____73066, r1)  in
            FStar_Pervasives_Native.Some uu____73061
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____73090 = try_lookup_lid env l  in
      match uu____73090 with
      | FStar_Pervasives_Native.None  ->
          let uu____73117 = name_not_found l  in
          let uu____73123 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____73117 uu____73123
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_73166  ->
              match uu___451_73166 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____73170 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____73191 = lookup_qname env lid  in
      match uu____73191 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73200,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73203;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73205;
              FStar_Syntax_Syntax.sigattrs = uu____73206;_},FStar_Pervasives_Native.None
            ),uu____73207)
          ->
          let uu____73256 =
            let uu____73263 =
              let uu____73264 =
                let uu____73267 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____73267 t  in
              (uvs, uu____73264)  in
            (uu____73263, q)  in
          FStar_Pervasives_Native.Some uu____73256
      | uu____73280 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73302 = lookup_qname env lid  in
      match uu____73302 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73307,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73310;
              FStar_Syntax_Syntax.sigquals = uu____73311;
              FStar_Syntax_Syntax.sigmeta = uu____73312;
              FStar_Syntax_Syntax.sigattrs = uu____73313;_},FStar_Pervasives_Native.None
            ),uu____73314)
          ->
          let uu____73363 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73363 (uvs, t)
      | uu____73368 ->
          let uu____73369 = name_not_found lid  in
          let uu____73375 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73369 uu____73375
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73395 = lookup_qname env lid  in
      match uu____73395 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73400,uvs,t,uu____73403,uu____73404,uu____73405);
              FStar_Syntax_Syntax.sigrng = uu____73406;
              FStar_Syntax_Syntax.sigquals = uu____73407;
              FStar_Syntax_Syntax.sigmeta = uu____73408;
              FStar_Syntax_Syntax.sigattrs = uu____73409;_},FStar_Pervasives_Native.None
            ),uu____73410)
          ->
          let uu____73465 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73465 (uvs, t)
      | uu____73470 ->
          let uu____73471 = name_not_found lid  in
          let uu____73477 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73471 uu____73477
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____73500 = lookup_qname env lid  in
      match uu____73500 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____73508,uu____73509,uu____73510,uu____73511,uu____73512,dcs);
              FStar_Syntax_Syntax.sigrng = uu____73514;
              FStar_Syntax_Syntax.sigquals = uu____73515;
              FStar_Syntax_Syntax.sigmeta = uu____73516;
              FStar_Syntax_Syntax.sigattrs = uu____73517;_},uu____73518),uu____73519)
          -> (true, dcs)
      | uu____73582 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____73598 = lookup_qname env lid  in
      match uu____73598 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73599,uu____73600,uu____73601,l,uu____73603,uu____73604);
              FStar_Syntax_Syntax.sigrng = uu____73605;
              FStar_Syntax_Syntax.sigquals = uu____73606;
              FStar_Syntax_Syntax.sigmeta = uu____73607;
              FStar_Syntax_Syntax.sigattrs = uu____73608;_},uu____73609),uu____73610)
          -> l
      | uu____73667 ->
          let uu____73668 =
            let uu____73670 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____73670  in
          failwith uu____73668
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____73740)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____73797) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____73821 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____73821
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____73856 -> FStar_Pervasives_Native.None)
          | uu____73865 -> FStar_Pervasives_Native.None
  
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
        let uu____73927 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____73927
  
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
        let uu____73960 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____73960
  
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
             (FStar_Util.Inl uu____74012,uu____74013) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____74062),uu____74063) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____74112 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____74130 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____74140 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____74157 ->
                  let uu____74164 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____74164
              | FStar_Syntax_Syntax.Sig_let ((uu____74165,lbs),uu____74167)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____74183 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____74183
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____74190 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____74198 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____74199 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____74206 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74207 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____74208 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74209 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____74222 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____74240 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____74240
           (fun d_opt  ->
              let uu____74253 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____74253
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____74263 =
                   let uu____74266 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____74266  in
                 match uu____74263 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____74267 =
                       let uu____74269 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____74269
                        in
                     failwith uu____74267
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____74274 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____74274
                       then
                         let uu____74277 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____74279 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____74281 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____74277 uu____74279 uu____74281
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
        (FStar_Util.Inr (se,uu____74306),uu____74307) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____74356 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____74378),uu____74379) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____74428 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____74450 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____74450
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____74473 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____74473 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____74497 =
                      let uu____74498 = FStar_Syntax_Util.un_uinst tm  in
                      uu____74498.FStar_Syntax_Syntax.n  in
                    match uu____74497 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____74503 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____74520 = lookup_qname env ftv  in
      match uu____74520 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____74524) ->
          let uu____74569 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____74569 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____74590,t),r) ->
               let uu____74605 =
                 let uu____74606 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____74606 t  in
               FStar_Pervasives_Native.Some uu____74605)
      | uu____74607 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____74619 = try_lookup_effect_lid env ftv  in
      match uu____74619 with
      | FStar_Pervasives_Native.None  ->
          let uu____74622 = name_not_found ftv  in
          let uu____74628 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____74622 uu____74628
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
        let uu____74652 = lookup_qname env lid0  in
        match uu____74652 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____74663);
                FStar_Syntax_Syntax.sigrng = uu____74664;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____74666;
                FStar_Syntax_Syntax.sigattrs = uu____74667;_},FStar_Pervasives_Native.None
              ),uu____74668)
            ->
            let lid1 =
              let uu____74722 =
                let uu____74723 = FStar_Ident.range_of_lid lid  in
                let uu____74724 =
                  let uu____74725 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____74725  in
                FStar_Range.set_use_range uu____74723 uu____74724  in
              FStar_Ident.set_lid_range lid uu____74722  in
            let uu____74726 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_74732  ->
                      match uu___452_74732 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____74735 -> false))
               in
            if uu____74726
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____74754 =
                      let uu____74756 =
                        let uu____74758 = get_range env  in
                        FStar_Range.string_of_range uu____74758  in
                      let uu____74759 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____74761 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____74756 uu____74759 uu____74761
                       in
                    failwith uu____74754)
                  in
               match (binders, univs1) with
               | ([],uu____74782) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____74808,uu____74809::uu____74810::uu____74811) ->
                   let uu____74832 =
                     let uu____74834 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____74836 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____74834 uu____74836
                      in
                   failwith uu____74832
               | uu____74847 ->
                   let uu____74862 =
                     let uu____74867 =
                       let uu____74868 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____74868)  in
                     inst_tscheme_with uu____74867 insts  in
                   (match uu____74862 with
                    | (uu____74881,t) ->
                        let t1 =
                          let uu____74884 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____74884 t  in
                        let uu____74885 =
                          let uu____74886 = FStar_Syntax_Subst.compress t1
                             in
                          uu____74886.FStar_Syntax_Syntax.n  in
                        (match uu____74885 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____74921 -> failwith "Impossible")))
        | uu____74929 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____74953 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____74953 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____74966,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____74973 = find1 l2  in
            (match uu____74973 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____74980 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____74980 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____74984 = find1 l  in
            (match uu____74984 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____74989 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____74989
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____75004 = lookup_qname env l1  in
      match uu____75004 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____75007;
              FStar_Syntax_Syntax.sigrng = uu____75008;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____75010;
              FStar_Syntax_Syntax.sigattrs = uu____75011;_},uu____75012),uu____75013)
          -> q
      | uu____75064 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____75088 =
          let uu____75089 =
            let uu____75091 = FStar_Util.string_of_int i  in
            let uu____75093 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____75091 uu____75093
             in
          failwith uu____75089  in
        let uu____75096 = lookup_datacon env lid  in
        match uu____75096 with
        | (uu____75101,t) ->
            let uu____75103 =
              let uu____75104 = FStar_Syntax_Subst.compress t  in
              uu____75104.FStar_Syntax_Syntax.n  in
            (match uu____75103 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75108) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____75152 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____75152
                      FStar_Pervasives_Native.fst)
             | uu____75163 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75177 = lookup_qname env l  in
      match uu____75177 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____75179,uu____75180,uu____75181);
              FStar_Syntax_Syntax.sigrng = uu____75182;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75184;
              FStar_Syntax_Syntax.sigattrs = uu____75185;_},uu____75186),uu____75187)
          ->
          FStar_Util.for_some
            (fun uu___453_75240  ->
               match uu___453_75240 with
               | FStar_Syntax_Syntax.Projector uu____75242 -> true
               | uu____75248 -> false) quals
      | uu____75250 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75264 = lookup_qname env lid  in
      match uu____75264 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____75266,uu____75267,uu____75268,uu____75269,uu____75270,uu____75271);
              FStar_Syntax_Syntax.sigrng = uu____75272;
              FStar_Syntax_Syntax.sigquals = uu____75273;
              FStar_Syntax_Syntax.sigmeta = uu____75274;
              FStar_Syntax_Syntax.sigattrs = uu____75275;_},uu____75276),uu____75277)
          -> true
      | uu____75335 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75349 = lookup_qname env lid  in
      match uu____75349 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75351,uu____75352,uu____75353,uu____75354,uu____75355,uu____75356);
              FStar_Syntax_Syntax.sigrng = uu____75357;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75359;
              FStar_Syntax_Syntax.sigattrs = uu____75360;_},uu____75361),uu____75362)
          ->
          FStar_Util.for_some
            (fun uu___454_75423  ->
               match uu___454_75423 with
               | FStar_Syntax_Syntax.RecordType uu____75425 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____75435 -> true
               | uu____75445 -> false) quals
      | uu____75447 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____75457,uu____75458);
            FStar_Syntax_Syntax.sigrng = uu____75459;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____75461;
            FStar_Syntax_Syntax.sigattrs = uu____75462;_},uu____75463),uu____75464)
        ->
        FStar_Util.for_some
          (fun uu___455_75521  ->
             match uu___455_75521 with
             | FStar_Syntax_Syntax.Action uu____75523 -> true
             | uu____75525 -> false) quals
    | uu____75527 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75541 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____75541
  
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
      let uu____75558 =
        let uu____75559 = FStar_Syntax_Util.un_uinst head1  in
        uu____75559.FStar_Syntax_Syntax.n  in
      match uu____75558 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75565 ->
               true
           | uu____75568 -> false)
      | uu____75570 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75584 = lookup_qname env l  in
      match uu____75584 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75587),uu____75588) ->
          FStar_Util.for_some
            (fun uu___456_75636  ->
               match uu___456_75636 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75639 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75641 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75717 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75735) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75753 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75761 ->
                 FStar_Pervasives_Native.Some true
             | uu____75780 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75783 =
        let uu____75787 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75787 mapper  in
      match uu____75783 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75847 = lookup_qname env lid  in
      match uu____75847 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75851,uu____75852,tps,uu____75854,uu____75855,uu____75856);
              FStar_Syntax_Syntax.sigrng = uu____75857;
              FStar_Syntax_Syntax.sigquals = uu____75858;
              FStar_Syntax_Syntax.sigmeta = uu____75859;
              FStar_Syntax_Syntax.sigattrs = uu____75860;_},uu____75861),uu____75862)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____75928 -> FStar_Pervasives_Native.None
  
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
           (fun uu____75974  ->
              match uu____75974 with
              | (d,uu____75983) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____75999 = effect_decl_opt env l  in
      match uu____75999 with
      | FStar_Pervasives_Native.None  ->
          let uu____76014 = name_not_found l  in
          let uu____76020 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76014 uu____76020
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76043  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76062  ->
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
        let uu____76094 = FStar_Ident.lid_equals l1 l2  in
        if uu____76094
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76105 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76105
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76116 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____76169  ->
                        match uu____76169 with
                        | (m1,m2,uu____76183,uu____76184,uu____76185) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76116 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76202 =
                    let uu____76208 =
                      let uu____76210 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____76212 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____76210
                        uu____76212
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____76208)
                     in
                  FStar_Errors.raise_error uu____76202 env.range
              | FStar_Pervasives_Native.Some
                  (uu____76222,uu____76223,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____76257 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____76257
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
  'Auu____76277 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____76277) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____76306 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____76332  ->
                match uu____76332 with
                | (d,uu____76339) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____76306 with
      | FStar_Pervasives_Native.None  ->
          let uu____76350 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____76350
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____76365 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____76365 with
           | (uu____76380,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____76398)::(wp,uu____76400)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____76456 -> failwith "Impossible"))
  
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
          let uu____76514 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____76514
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____76519 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____76519
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
                  let uu____76530 = get_range env  in
                  let uu____76531 =
                    let uu____76538 =
                      let uu____76539 =
                        let uu____76556 =
                          let uu____76567 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____76567]  in
                        (null_wp, uu____76556)  in
                      FStar_Syntax_Syntax.Tm_app uu____76539  in
                    FStar_Syntax_Syntax.mk uu____76538  in
                  uu____76531 FStar_Pervasives_Native.None uu____76530  in
                let uu____76607 =
                  let uu____76608 =
                    let uu____76619 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____76619]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____76608;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____76607))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1939_76657 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1939_76657.order);
              joins = (uu___1939_76657.joins)
            }  in
          let uu___1942_76666 = env  in
          {
            solver = (uu___1942_76666.solver);
            range = (uu___1942_76666.range);
            curmodule = (uu___1942_76666.curmodule);
            gamma = (uu___1942_76666.gamma);
            gamma_sig = (uu___1942_76666.gamma_sig);
            gamma_cache = (uu___1942_76666.gamma_cache);
            modules = (uu___1942_76666.modules);
            expected_typ = (uu___1942_76666.expected_typ);
            sigtab = (uu___1942_76666.sigtab);
            attrtab = (uu___1942_76666.attrtab);
            is_pattern = (uu___1942_76666.is_pattern);
            instantiate_imp = (uu___1942_76666.instantiate_imp);
            effects;
            generalize = (uu___1942_76666.generalize);
            letrecs = (uu___1942_76666.letrecs);
            top_level = (uu___1942_76666.top_level);
            check_uvars = (uu___1942_76666.check_uvars);
            use_eq = (uu___1942_76666.use_eq);
            is_iface = (uu___1942_76666.is_iface);
            admit = (uu___1942_76666.admit);
            lax = (uu___1942_76666.lax);
            lax_universes = (uu___1942_76666.lax_universes);
            phase1 = (uu___1942_76666.phase1);
            failhard = (uu___1942_76666.failhard);
            nosynth = (uu___1942_76666.nosynth);
            uvar_subtyping = (uu___1942_76666.uvar_subtyping);
            tc_term = (uu___1942_76666.tc_term);
            type_of = (uu___1942_76666.type_of);
            universe_of = (uu___1942_76666.universe_of);
            check_type_of = (uu___1942_76666.check_type_of);
            use_bv_sorts = (uu___1942_76666.use_bv_sorts);
            qtbl_name_and_index = (uu___1942_76666.qtbl_name_and_index);
            normalized_eff_names = (uu___1942_76666.normalized_eff_names);
            fv_delta_depths = (uu___1942_76666.fv_delta_depths);
            proof_ns = (uu___1942_76666.proof_ns);
            synth_hook = (uu___1942_76666.synth_hook);
            splice = (uu___1942_76666.splice);
            postprocess = (uu___1942_76666.postprocess);
            is_native_tactic = (uu___1942_76666.is_native_tactic);
            identifier_info = (uu___1942_76666.identifier_info);
            tc_hooks = (uu___1942_76666.tc_hooks);
            dsenv = (uu___1942_76666.dsenv);
            nbe = (uu___1942_76666.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____76696 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____76696  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____76854 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____76855 = l1 u t wp e  in
                                l2 u t uu____76854 uu____76855))
                | uu____76856 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____76928 = inst_tscheme_with lift_t [u]  in
            match uu____76928 with
            | (uu____76935,lift_t1) ->
                let uu____76937 =
                  let uu____76944 =
                    let uu____76945 =
                      let uu____76962 =
                        let uu____76973 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____76982 =
                          let uu____76993 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____76993]  in
                        uu____76973 :: uu____76982  in
                      (lift_t1, uu____76962)  in
                    FStar_Syntax_Syntax.Tm_app uu____76945  in
                  FStar_Syntax_Syntax.mk uu____76944  in
                uu____76937 FStar_Pervasives_Native.None
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
            let uu____77106 = inst_tscheme_with lift_t [u]  in
            match uu____77106 with
            | (uu____77113,lift_t1) ->
                let uu____77115 =
                  let uu____77122 =
                    let uu____77123 =
                      let uu____77140 =
                        let uu____77151 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77160 =
                          let uu____77171 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____77180 =
                            let uu____77191 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____77191]  in
                          uu____77171 :: uu____77180  in
                        uu____77151 :: uu____77160  in
                      (lift_t1, uu____77140)  in
                    FStar_Syntax_Syntax.Tm_app uu____77123  in
                  FStar_Syntax_Syntax.mk uu____77122  in
                uu____77115 FStar_Pervasives_Native.None
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
              let uu____77296 =
                let uu____77297 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____77297
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____77296  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____77306 =
              let uu____77308 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____77308  in
            let uu____77309 =
              let uu____77311 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____77339 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____77339)
                 in
              FStar_Util.dflt "none" uu____77311  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____77306
              uu____77309
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____77368  ->
                    match uu____77368 with
                    | (e,uu____77376) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____77399 =
            match uu____77399 with
            | (i,j) ->
                let uu____77410 = FStar_Ident.lid_equals i j  in
                if uu____77410
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _77417  -> FStar_Pervasives_Native.Some _77417)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____77446 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____77456 = FStar_Ident.lid_equals i k  in
                        if uu____77456
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____77470 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____77470
                                  then []
                                  else
                                    (let uu____77477 =
                                       let uu____77486 =
                                         find_edge order1 (i, k)  in
                                       let uu____77489 =
                                         find_edge order1 (k, j)  in
                                       (uu____77486, uu____77489)  in
                                     match uu____77477 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____77504 =
                                           compose_edges e1 e2  in
                                         [uu____77504]
                                     | uu____77505 -> [])))))
                 in
              FStar_List.append order1 uu____77446  in
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
                   let uu____77535 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____77538 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____77538
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____77535
                   then
                     let uu____77545 =
                       let uu____77551 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____77551)
                        in
                     let uu____77555 = get_range env  in
                     FStar_Errors.raise_error uu____77545 uu____77555
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____77633 = FStar_Ident.lid_equals i j
                                   in
                                if uu____77633
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____77685 =
                                              let uu____77694 =
                                                find_edge order2 (i, k)  in
                                              let uu____77697 =
                                                find_edge order2 (j, k)  in
                                              (uu____77694, uu____77697)  in
                                            match uu____77685 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____77739,uu____77740)
                                                     ->
                                                     let uu____77747 =
                                                       let uu____77754 =
                                                         let uu____77756 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77756
                                                          in
                                                       let uu____77759 =
                                                         let uu____77761 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77761
                                                          in
                                                       (uu____77754,
                                                         uu____77759)
                                                        in
                                                     (match uu____77747 with
                                                      | (true ,true ) ->
                                                          let uu____77778 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____77778
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
                                            | uu____77821 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2069_77894 = env.effects  in
              { decls = (uu___2069_77894.decls); order = order2; joins }  in
            let uu___2072_77895 = env  in
            {
              solver = (uu___2072_77895.solver);
              range = (uu___2072_77895.range);
              curmodule = (uu___2072_77895.curmodule);
              gamma = (uu___2072_77895.gamma);
              gamma_sig = (uu___2072_77895.gamma_sig);
              gamma_cache = (uu___2072_77895.gamma_cache);
              modules = (uu___2072_77895.modules);
              expected_typ = (uu___2072_77895.expected_typ);
              sigtab = (uu___2072_77895.sigtab);
              attrtab = (uu___2072_77895.attrtab);
              is_pattern = (uu___2072_77895.is_pattern);
              instantiate_imp = (uu___2072_77895.instantiate_imp);
              effects;
              generalize = (uu___2072_77895.generalize);
              letrecs = (uu___2072_77895.letrecs);
              top_level = (uu___2072_77895.top_level);
              check_uvars = (uu___2072_77895.check_uvars);
              use_eq = (uu___2072_77895.use_eq);
              is_iface = (uu___2072_77895.is_iface);
              admit = (uu___2072_77895.admit);
              lax = (uu___2072_77895.lax);
              lax_universes = (uu___2072_77895.lax_universes);
              phase1 = (uu___2072_77895.phase1);
              failhard = (uu___2072_77895.failhard);
              nosynth = (uu___2072_77895.nosynth);
              uvar_subtyping = (uu___2072_77895.uvar_subtyping);
              tc_term = (uu___2072_77895.tc_term);
              type_of = (uu___2072_77895.type_of);
              universe_of = (uu___2072_77895.universe_of);
              check_type_of = (uu___2072_77895.check_type_of);
              use_bv_sorts = (uu___2072_77895.use_bv_sorts);
              qtbl_name_and_index = (uu___2072_77895.qtbl_name_and_index);
              normalized_eff_names = (uu___2072_77895.normalized_eff_names);
              fv_delta_depths = (uu___2072_77895.fv_delta_depths);
              proof_ns = (uu___2072_77895.proof_ns);
              synth_hook = (uu___2072_77895.synth_hook);
              splice = (uu___2072_77895.splice);
              postprocess = (uu___2072_77895.postprocess);
              is_native_tactic = (uu___2072_77895.is_native_tactic);
              identifier_info = (uu___2072_77895.identifier_info);
              tc_hooks = (uu___2072_77895.tc_hooks);
              dsenv = (uu___2072_77895.dsenv);
              nbe = (uu___2072_77895.nbe)
            }))
      | uu____77896 -> env
  
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
        | uu____77925 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____77938 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____77938 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____77955 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____77955 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____77980 =
                     let uu____77986 =
                       let uu____77988 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____77996 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____78007 =
                         let uu____78009 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____78009  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____77988 uu____77996 uu____78007
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____77986)
                      in
                   FStar_Errors.raise_error uu____77980
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____78017 =
                     let uu____78028 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____78028 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____78065  ->
                        fun uu____78066  ->
                          match (uu____78065, uu____78066) with
                          | ((x,uu____78096),(t,uu____78098)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____78017
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____78129 =
                     let uu___2110_78130 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2110_78130.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2110_78130.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2110_78130.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2110_78130.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____78129
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____78142 .
    'Auu____78142 ->
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
          let uu____78172 = effect_decl_opt env effect_name  in
          match uu____78172 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____78211 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____78234 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____78273 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____78273
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____78278 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____78278
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____78293 =
                     let uu____78296 = get_range env  in
                     let uu____78297 =
                       let uu____78304 =
                         let uu____78305 =
                           let uu____78322 =
                             let uu____78333 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____78333; wp]  in
                           (repr, uu____78322)  in
                         FStar_Syntax_Syntax.Tm_app uu____78305  in
                       FStar_Syntax_Syntax.mk uu____78304  in
                     uu____78297 FStar_Pervasives_Native.None uu____78296  in
                   FStar_Pervasives_Native.Some uu____78293)
  
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
      | uu____78480 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____78495 =
        let uu____78496 = FStar_Syntax_Subst.compress t  in
        uu____78496.FStar_Syntax_Syntax.n  in
      match uu____78495 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____78500,c) ->
          is_reifiable_comp env c
      | uu____78522 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____78542 =
           let uu____78544 = is_reifiable_effect env l  in
           Prims.op_Negation uu____78544  in
         if uu____78542
         then
           let uu____78547 =
             let uu____78553 =
               let uu____78555 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____78555
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____78553)  in
           let uu____78559 = get_range env  in
           FStar_Errors.raise_error uu____78547 uu____78559
         else ());
        (let uu____78562 = effect_repr_aux true env c u_c  in
         match uu____78562 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2175_78598 = env  in
        {
          solver = (uu___2175_78598.solver);
          range = (uu___2175_78598.range);
          curmodule = (uu___2175_78598.curmodule);
          gamma = (uu___2175_78598.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2175_78598.gamma_cache);
          modules = (uu___2175_78598.modules);
          expected_typ = (uu___2175_78598.expected_typ);
          sigtab = (uu___2175_78598.sigtab);
          attrtab = (uu___2175_78598.attrtab);
          is_pattern = (uu___2175_78598.is_pattern);
          instantiate_imp = (uu___2175_78598.instantiate_imp);
          effects = (uu___2175_78598.effects);
          generalize = (uu___2175_78598.generalize);
          letrecs = (uu___2175_78598.letrecs);
          top_level = (uu___2175_78598.top_level);
          check_uvars = (uu___2175_78598.check_uvars);
          use_eq = (uu___2175_78598.use_eq);
          is_iface = (uu___2175_78598.is_iface);
          admit = (uu___2175_78598.admit);
          lax = (uu___2175_78598.lax);
          lax_universes = (uu___2175_78598.lax_universes);
          phase1 = (uu___2175_78598.phase1);
          failhard = (uu___2175_78598.failhard);
          nosynth = (uu___2175_78598.nosynth);
          uvar_subtyping = (uu___2175_78598.uvar_subtyping);
          tc_term = (uu___2175_78598.tc_term);
          type_of = (uu___2175_78598.type_of);
          universe_of = (uu___2175_78598.universe_of);
          check_type_of = (uu___2175_78598.check_type_of);
          use_bv_sorts = (uu___2175_78598.use_bv_sorts);
          qtbl_name_and_index = (uu___2175_78598.qtbl_name_and_index);
          normalized_eff_names = (uu___2175_78598.normalized_eff_names);
          fv_delta_depths = (uu___2175_78598.fv_delta_depths);
          proof_ns = (uu___2175_78598.proof_ns);
          synth_hook = (uu___2175_78598.synth_hook);
          splice = (uu___2175_78598.splice);
          postprocess = (uu___2175_78598.postprocess);
          is_native_tactic = (uu___2175_78598.is_native_tactic);
          identifier_info = (uu___2175_78598.identifier_info);
          tc_hooks = (uu___2175_78598.tc_hooks);
          dsenv = (uu___2175_78598.dsenv);
          nbe = (uu___2175_78598.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2182_78612 = env  in
      {
        solver = (uu___2182_78612.solver);
        range = (uu___2182_78612.range);
        curmodule = (uu___2182_78612.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2182_78612.gamma_sig);
        gamma_cache = (uu___2182_78612.gamma_cache);
        modules = (uu___2182_78612.modules);
        expected_typ = (uu___2182_78612.expected_typ);
        sigtab = (uu___2182_78612.sigtab);
        attrtab = (uu___2182_78612.attrtab);
        is_pattern = (uu___2182_78612.is_pattern);
        instantiate_imp = (uu___2182_78612.instantiate_imp);
        effects = (uu___2182_78612.effects);
        generalize = (uu___2182_78612.generalize);
        letrecs = (uu___2182_78612.letrecs);
        top_level = (uu___2182_78612.top_level);
        check_uvars = (uu___2182_78612.check_uvars);
        use_eq = (uu___2182_78612.use_eq);
        is_iface = (uu___2182_78612.is_iface);
        admit = (uu___2182_78612.admit);
        lax = (uu___2182_78612.lax);
        lax_universes = (uu___2182_78612.lax_universes);
        phase1 = (uu___2182_78612.phase1);
        failhard = (uu___2182_78612.failhard);
        nosynth = (uu___2182_78612.nosynth);
        uvar_subtyping = (uu___2182_78612.uvar_subtyping);
        tc_term = (uu___2182_78612.tc_term);
        type_of = (uu___2182_78612.type_of);
        universe_of = (uu___2182_78612.universe_of);
        check_type_of = (uu___2182_78612.check_type_of);
        use_bv_sorts = (uu___2182_78612.use_bv_sorts);
        qtbl_name_and_index = (uu___2182_78612.qtbl_name_and_index);
        normalized_eff_names = (uu___2182_78612.normalized_eff_names);
        fv_delta_depths = (uu___2182_78612.fv_delta_depths);
        proof_ns = (uu___2182_78612.proof_ns);
        synth_hook = (uu___2182_78612.synth_hook);
        splice = (uu___2182_78612.splice);
        postprocess = (uu___2182_78612.postprocess);
        is_native_tactic = (uu___2182_78612.is_native_tactic);
        identifier_info = (uu___2182_78612.identifier_info);
        tc_hooks = (uu___2182_78612.tc_hooks);
        dsenv = (uu___2182_78612.dsenv);
        nbe = (uu___2182_78612.nbe)
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
            (let uu___2195_78670 = env  in
             {
               solver = (uu___2195_78670.solver);
               range = (uu___2195_78670.range);
               curmodule = (uu___2195_78670.curmodule);
               gamma = rest;
               gamma_sig = (uu___2195_78670.gamma_sig);
               gamma_cache = (uu___2195_78670.gamma_cache);
               modules = (uu___2195_78670.modules);
               expected_typ = (uu___2195_78670.expected_typ);
               sigtab = (uu___2195_78670.sigtab);
               attrtab = (uu___2195_78670.attrtab);
               is_pattern = (uu___2195_78670.is_pattern);
               instantiate_imp = (uu___2195_78670.instantiate_imp);
               effects = (uu___2195_78670.effects);
               generalize = (uu___2195_78670.generalize);
               letrecs = (uu___2195_78670.letrecs);
               top_level = (uu___2195_78670.top_level);
               check_uvars = (uu___2195_78670.check_uvars);
               use_eq = (uu___2195_78670.use_eq);
               is_iface = (uu___2195_78670.is_iface);
               admit = (uu___2195_78670.admit);
               lax = (uu___2195_78670.lax);
               lax_universes = (uu___2195_78670.lax_universes);
               phase1 = (uu___2195_78670.phase1);
               failhard = (uu___2195_78670.failhard);
               nosynth = (uu___2195_78670.nosynth);
               uvar_subtyping = (uu___2195_78670.uvar_subtyping);
               tc_term = (uu___2195_78670.tc_term);
               type_of = (uu___2195_78670.type_of);
               universe_of = (uu___2195_78670.universe_of);
               check_type_of = (uu___2195_78670.check_type_of);
               use_bv_sorts = (uu___2195_78670.use_bv_sorts);
               qtbl_name_and_index = (uu___2195_78670.qtbl_name_and_index);
               normalized_eff_names = (uu___2195_78670.normalized_eff_names);
               fv_delta_depths = (uu___2195_78670.fv_delta_depths);
               proof_ns = (uu___2195_78670.proof_ns);
               synth_hook = (uu___2195_78670.synth_hook);
               splice = (uu___2195_78670.splice);
               postprocess = (uu___2195_78670.postprocess);
               is_native_tactic = (uu___2195_78670.is_native_tactic);
               identifier_info = (uu___2195_78670.identifier_info);
               tc_hooks = (uu___2195_78670.tc_hooks);
               dsenv = (uu___2195_78670.dsenv);
               nbe = (uu___2195_78670.nbe)
             }))
    | uu____78671 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____78700  ->
             match uu____78700 with | (x,uu____78708) -> push_bv env1 x) env
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
            let uu___2209_78743 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2209_78743.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2209_78743.FStar_Syntax_Syntax.index);
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
      (let uu___2220_78785 = env  in
       {
         solver = (uu___2220_78785.solver);
         range = (uu___2220_78785.range);
         curmodule = (uu___2220_78785.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2220_78785.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2220_78785.sigtab);
         attrtab = (uu___2220_78785.attrtab);
         is_pattern = (uu___2220_78785.is_pattern);
         instantiate_imp = (uu___2220_78785.instantiate_imp);
         effects = (uu___2220_78785.effects);
         generalize = (uu___2220_78785.generalize);
         letrecs = (uu___2220_78785.letrecs);
         top_level = (uu___2220_78785.top_level);
         check_uvars = (uu___2220_78785.check_uvars);
         use_eq = (uu___2220_78785.use_eq);
         is_iface = (uu___2220_78785.is_iface);
         admit = (uu___2220_78785.admit);
         lax = (uu___2220_78785.lax);
         lax_universes = (uu___2220_78785.lax_universes);
         phase1 = (uu___2220_78785.phase1);
         failhard = (uu___2220_78785.failhard);
         nosynth = (uu___2220_78785.nosynth);
         uvar_subtyping = (uu___2220_78785.uvar_subtyping);
         tc_term = (uu___2220_78785.tc_term);
         type_of = (uu___2220_78785.type_of);
         universe_of = (uu___2220_78785.universe_of);
         check_type_of = (uu___2220_78785.check_type_of);
         use_bv_sorts = (uu___2220_78785.use_bv_sorts);
         qtbl_name_and_index = (uu___2220_78785.qtbl_name_and_index);
         normalized_eff_names = (uu___2220_78785.normalized_eff_names);
         fv_delta_depths = (uu___2220_78785.fv_delta_depths);
         proof_ns = (uu___2220_78785.proof_ns);
         synth_hook = (uu___2220_78785.synth_hook);
         splice = (uu___2220_78785.splice);
         postprocess = (uu___2220_78785.postprocess);
         is_native_tactic = (uu___2220_78785.is_native_tactic);
         identifier_info = (uu___2220_78785.identifier_info);
         tc_hooks = (uu___2220_78785.tc_hooks);
         dsenv = (uu___2220_78785.dsenv);
         nbe = (uu___2220_78785.nbe)
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
        let uu____78829 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____78829 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____78857 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____78857)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2235_78873 = env  in
      {
        solver = (uu___2235_78873.solver);
        range = (uu___2235_78873.range);
        curmodule = (uu___2235_78873.curmodule);
        gamma = (uu___2235_78873.gamma);
        gamma_sig = (uu___2235_78873.gamma_sig);
        gamma_cache = (uu___2235_78873.gamma_cache);
        modules = (uu___2235_78873.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2235_78873.sigtab);
        attrtab = (uu___2235_78873.attrtab);
        is_pattern = (uu___2235_78873.is_pattern);
        instantiate_imp = (uu___2235_78873.instantiate_imp);
        effects = (uu___2235_78873.effects);
        generalize = (uu___2235_78873.generalize);
        letrecs = (uu___2235_78873.letrecs);
        top_level = (uu___2235_78873.top_level);
        check_uvars = (uu___2235_78873.check_uvars);
        use_eq = false;
        is_iface = (uu___2235_78873.is_iface);
        admit = (uu___2235_78873.admit);
        lax = (uu___2235_78873.lax);
        lax_universes = (uu___2235_78873.lax_universes);
        phase1 = (uu___2235_78873.phase1);
        failhard = (uu___2235_78873.failhard);
        nosynth = (uu___2235_78873.nosynth);
        uvar_subtyping = (uu___2235_78873.uvar_subtyping);
        tc_term = (uu___2235_78873.tc_term);
        type_of = (uu___2235_78873.type_of);
        universe_of = (uu___2235_78873.universe_of);
        check_type_of = (uu___2235_78873.check_type_of);
        use_bv_sorts = (uu___2235_78873.use_bv_sorts);
        qtbl_name_and_index = (uu___2235_78873.qtbl_name_and_index);
        normalized_eff_names = (uu___2235_78873.normalized_eff_names);
        fv_delta_depths = (uu___2235_78873.fv_delta_depths);
        proof_ns = (uu___2235_78873.proof_ns);
        synth_hook = (uu___2235_78873.synth_hook);
        splice = (uu___2235_78873.splice);
        postprocess = (uu___2235_78873.postprocess);
        is_native_tactic = (uu___2235_78873.is_native_tactic);
        identifier_info = (uu___2235_78873.identifier_info);
        tc_hooks = (uu___2235_78873.tc_hooks);
        dsenv = (uu___2235_78873.dsenv);
        nbe = (uu___2235_78873.nbe)
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
    let uu____78904 = expected_typ env_  in
    ((let uu___2242_78910 = env_  in
      {
        solver = (uu___2242_78910.solver);
        range = (uu___2242_78910.range);
        curmodule = (uu___2242_78910.curmodule);
        gamma = (uu___2242_78910.gamma);
        gamma_sig = (uu___2242_78910.gamma_sig);
        gamma_cache = (uu___2242_78910.gamma_cache);
        modules = (uu___2242_78910.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2242_78910.sigtab);
        attrtab = (uu___2242_78910.attrtab);
        is_pattern = (uu___2242_78910.is_pattern);
        instantiate_imp = (uu___2242_78910.instantiate_imp);
        effects = (uu___2242_78910.effects);
        generalize = (uu___2242_78910.generalize);
        letrecs = (uu___2242_78910.letrecs);
        top_level = (uu___2242_78910.top_level);
        check_uvars = (uu___2242_78910.check_uvars);
        use_eq = false;
        is_iface = (uu___2242_78910.is_iface);
        admit = (uu___2242_78910.admit);
        lax = (uu___2242_78910.lax);
        lax_universes = (uu___2242_78910.lax_universes);
        phase1 = (uu___2242_78910.phase1);
        failhard = (uu___2242_78910.failhard);
        nosynth = (uu___2242_78910.nosynth);
        uvar_subtyping = (uu___2242_78910.uvar_subtyping);
        tc_term = (uu___2242_78910.tc_term);
        type_of = (uu___2242_78910.type_of);
        universe_of = (uu___2242_78910.universe_of);
        check_type_of = (uu___2242_78910.check_type_of);
        use_bv_sorts = (uu___2242_78910.use_bv_sorts);
        qtbl_name_and_index = (uu___2242_78910.qtbl_name_and_index);
        normalized_eff_names = (uu___2242_78910.normalized_eff_names);
        fv_delta_depths = (uu___2242_78910.fv_delta_depths);
        proof_ns = (uu___2242_78910.proof_ns);
        synth_hook = (uu___2242_78910.synth_hook);
        splice = (uu___2242_78910.splice);
        postprocess = (uu___2242_78910.postprocess);
        is_native_tactic = (uu___2242_78910.is_native_tactic);
        identifier_info = (uu___2242_78910.identifier_info);
        tc_hooks = (uu___2242_78910.tc_hooks);
        dsenv = (uu___2242_78910.dsenv);
        nbe = (uu___2242_78910.nbe)
      }), uu____78904)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____78922 =
      let uu____78925 = FStar_Ident.id_of_text ""  in [uu____78925]  in
    FStar_Ident.lid_of_ids uu____78922  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____78932 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____78932
        then
          let uu____78937 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____78937 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2250_78965 = env  in
       {
         solver = (uu___2250_78965.solver);
         range = (uu___2250_78965.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2250_78965.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2250_78965.expected_typ);
         sigtab = (uu___2250_78965.sigtab);
         attrtab = (uu___2250_78965.attrtab);
         is_pattern = (uu___2250_78965.is_pattern);
         instantiate_imp = (uu___2250_78965.instantiate_imp);
         effects = (uu___2250_78965.effects);
         generalize = (uu___2250_78965.generalize);
         letrecs = (uu___2250_78965.letrecs);
         top_level = (uu___2250_78965.top_level);
         check_uvars = (uu___2250_78965.check_uvars);
         use_eq = (uu___2250_78965.use_eq);
         is_iface = (uu___2250_78965.is_iface);
         admit = (uu___2250_78965.admit);
         lax = (uu___2250_78965.lax);
         lax_universes = (uu___2250_78965.lax_universes);
         phase1 = (uu___2250_78965.phase1);
         failhard = (uu___2250_78965.failhard);
         nosynth = (uu___2250_78965.nosynth);
         uvar_subtyping = (uu___2250_78965.uvar_subtyping);
         tc_term = (uu___2250_78965.tc_term);
         type_of = (uu___2250_78965.type_of);
         universe_of = (uu___2250_78965.universe_of);
         check_type_of = (uu___2250_78965.check_type_of);
         use_bv_sorts = (uu___2250_78965.use_bv_sorts);
         qtbl_name_and_index = (uu___2250_78965.qtbl_name_and_index);
         normalized_eff_names = (uu___2250_78965.normalized_eff_names);
         fv_delta_depths = (uu___2250_78965.fv_delta_depths);
         proof_ns = (uu___2250_78965.proof_ns);
         synth_hook = (uu___2250_78965.synth_hook);
         splice = (uu___2250_78965.splice);
         postprocess = (uu___2250_78965.postprocess);
         is_native_tactic = (uu___2250_78965.is_native_tactic);
         identifier_info = (uu___2250_78965.identifier_info);
         tc_hooks = (uu___2250_78965.tc_hooks);
         dsenv = (uu___2250_78965.dsenv);
         nbe = (uu___2250_78965.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79017)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79021,(uu____79022,t)))::tl1
          ->
          let uu____79043 =
            let uu____79046 = FStar_Syntax_Free.uvars t  in
            ext out uu____79046  in
          aux uu____79043 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79049;
            FStar_Syntax_Syntax.index = uu____79050;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79058 =
            let uu____79061 = FStar_Syntax_Free.uvars t  in
            ext out uu____79061  in
          aux uu____79058 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79119)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79123,(uu____79124,t)))::tl1
          ->
          let uu____79145 =
            let uu____79148 = FStar_Syntax_Free.univs t  in
            ext out uu____79148  in
          aux uu____79145 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79151;
            FStar_Syntax_Syntax.index = uu____79152;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79160 =
            let uu____79163 = FStar_Syntax_Free.univs t  in
            ext out uu____79163  in
          aux uu____79160 tl1
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
          let uu____79225 = FStar_Util.set_add uname out  in
          aux uu____79225 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79228,(uu____79229,t)))::tl1
          ->
          let uu____79250 =
            let uu____79253 = FStar_Syntax_Free.univnames t  in
            ext out uu____79253  in
          aux uu____79250 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79256;
            FStar_Syntax_Syntax.index = uu____79257;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79265 =
            let uu____79268 = FStar_Syntax_Free.univnames t  in
            ext out uu____79268  in
          aux uu____79265 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_79289  ->
            match uu___457_79289 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____79293 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____79306 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____79317 =
      let uu____79326 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____79326
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____79317 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____79374 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_79387  ->
              match uu___458_79387 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____79390 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____79390
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____79396) ->
                  let uu____79413 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____79413))
       in
    FStar_All.pipe_right uu____79374 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_79427  ->
    match uu___459_79427 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____79433 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____79433
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____79456  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____79511) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____79544,uu____79545) -> false  in
      let uu____79559 =
        FStar_List.tryFind
          (fun uu____79581  ->
             match uu____79581 with | (p,uu____79592) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____79559 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____79611,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____79641 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____79641
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2393_79663 = e  in
        {
          solver = (uu___2393_79663.solver);
          range = (uu___2393_79663.range);
          curmodule = (uu___2393_79663.curmodule);
          gamma = (uu___2393_79663.gamma);
          gamma_sig = (uu___2393_79663.gamma_sig);
          gamma_cache = (uu___2393_79663.gamma_cache);
          modules = (uu___2393_79663.modules);
          expected_typ = (uu___2393_79663.expected_typ);
          sigtab = (uu___2393_79663.sigtab);
          attrtab = (uu___2393_79663.attrtab);
          is_pattern = (uu___2393_79663.is_pattern);
          instantiate_imp = (uu___2393_79663.instantiate_imp);
          effects = (uu___2393_79663.effects);
          generalize = (uu___2393_79663.generalize);
          letrecs = (uu___2393_79663.letrecs);
          top_level = (uu___2393_79663.top_level);
          check_uvars = (uu___2393_79663.check_uvars);
          use_eq = (uu___2393_79663.use_eq);
          is_iface = (uu___2393_79663.is_iface);
          admit = (uu___2393_79663.admit);
          lax = (uu___2393_79663.lax);
          lax_universes = (uu___2393_79663.lax_universes);
          phase1 = (uu___2393_79663.phase1);
          failhard = (uu___2393_79663.failhard);
          nosynth = (uu___2393_79663.nosynth);
          uvar_subtyping = (uu___2393_79663.uvar_subtyping);
          tc_term = (uu___2393_79663.tc_term);
          type_of = (uu___2393_79663.type_of);
          universe_of = (uu___2393_79663.universe_of);
          check_type_of = (uu___2393_79663.check_type_of);
          use_bv_sorts = (uu___2393_79663.use_bv_sorts);
          qtbl_name_and_index = (uu___2393_79663.qtbl_name_and_index);
          normalized_eff_names = (uu___2393_79663.normalized_eff_names);
          fv_delta_depths = (uu___2393_79663.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2393_79663.synth_hook);
          splice = (uu___2393_79663.splice);
          postprocess = (uu___2393_79663.postprocess);
          is_native_tactic = (uu___2393_79663.is_native_tactic);
          identifier_info = (uu___2393_79663.identifier_info);
          tc_hooks = (uu___2393_79663.tc_hooks);
          dsenv = (uu___2393_79663.dsenv);
          nbe = (uu___2393_79663.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2402_79711 = e  in
      {
        solver = (uu___2402_79711.solver);
        range = (uu___2402_79711.range);
        curmodule = (uu___2402_79711.curmodule);
        gamma = (uu___2402_79711.gamma);
        gamma_sig = (uu___2402_79711.gamma_sig);
        gamma_cache = (uu___2402_79711.gamma_cache);
        modules = (uu___2402_79711.modules);
        expected_typ = (uu___2402_79711.expected_typ);
        sigtab = (uu___2402_79711.sigtab);
        attrtab = (uu___2402_79711.attrtab);
        is_pattern = (uu___2402_79711.is_pattern);
        instantiate_imp = (uu___2402_79711.instantiate_imp);
        effects = (uu___2402_79711.effects);
        generalize = (uu___2402_79711.generalize);
        letrecs = (uu___2402_79711.letrecs);
        top_level = (uu___2402_79711.top_level);
        check_uvars = (uu___2402_79711.check_uvars);
        use_eq = (uu___2402_79711.use_eq);
        is_iface = (uu___2402_79711.is_iface);
        admit = (uu___2402_79711.admit);
        lax = (uu___2402_79711.lax);
        lax_universes = (uu___2402_79711.lax_universes);
        phase1 = (uu___2402_79711.phase1);
        failhard = (uu___2402_79711.failhard);
        nosynth = (uu___2402_79711.nosynth);
        uvar_subtyping = (uu___2402_79711.uvar_subtyping);
        tc_term = (uu___2402_79711.tc_term);
        type_of = (uu___2402_79711.type_of);
        universe_of = (uu___2402_79711.universe_of);
        check_type_of = (uu___2402_79711.check_type_of);
        use_bv_sorts = (uu___2402_79711.use_bv_sorts);
        qtbl_name_and_index = (uu___2402_79711.qtbl_name_and_index);
        normalized_eff_names = (uu___2402_79711.normalized_eff_names);
        fv_delta_depths = (uu___2402_79711.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2402_79711.synth_hook);
        splice = (uu___2402_79711.splice);
        postprocess = (uu___2402_79711.postprocess);
        is_native_tactic = (uu___2402_79711.is_native_tactic);
        identifier_info = (uu___2402_79711.identifier_info);
        tc_hooks = (uu___2402_79711.tc_hooks);
        dsenv = (uu___2402_79711.dsenv);
        nbe = (uu___2402_79711.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____79727 = FStar_Syntax_Free.names t  in
      let uu____79730 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____79727 uu____79730
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____79753 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____79753
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____79763 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____79763
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____79784 =
      match uu____79784 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____79804 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____79804)
       in
    let uu____79812 =
      let uu____79816 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____79816 FStar_List.rev  in
    FStar_All.pipe_right uu____79812 (FStar_String.concat " ")
  
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
                  (let uu____79886 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____79886 with
                   | FStar_Pervasives_Native.Some uu____79890 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____79893 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____79903;
        univ_ineqs = uu____79904; implicits = uu____79905;_} -> true
    | uu____79917 -> false
  
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
          let uu___2446_79948 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2446_79948.deferred);
            univ_ineqs = (uu___2446_79948.univ_ineqs);
            implicits = (uu___2446_79948.implicits)
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
          let uu____79987 = FStar_Options.defensive ()  in
          if uu____79987
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____79993 =
              let uu____79995 =
                let uu____79997 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____79997  in
              Prims.op_Negation uu____79995  in
            (if uu____79993
             then
               let uu____80004 =
                 let uu____80010 =
                   let uu____80012 = FStar_Syntax_Print.term_to_string t  in
                   let uu____80014 =
                     let uu____80016 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____80016
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____80012 uu____80014
                    in
                 (FStar_Errors.Warning_Defensive, uu____80010)  in
               FStar_Errors.log_issue rng uu____80004
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
          let uu____80056 =
            let uu____80058 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80058  in
          if uu____80056
          then ()
          else
            (let uu____80063 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____80063 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____80089 =
            let uu____80091 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80091  in
          if uu____80089
          then ()
          else
            (let uu____80096 = bound_vars e  in
             def_check_closed_in rng msg uu____80096 t)
  
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
          let uu___2483_80135 = g  in
          let uu____80136 =
            let uu____80137 =
              let uu____80138 =
                let uu____80145 =
                  let uu____80146 =
                    let uu____80163 =
                      let uu____80174 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____80174]  in
                    (f, uu____80163)  in
                  FStar_Syntax_Syntax.Tm_app uu____80146  in
                FStar_Syntax_Syntax.mk uu____80145  in
              uu____80138 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _80214  -> FStar_TypeChecker_Common.NonTrivial _80214)
              uu____80137
             in
          {
            guard_f = uu____80136;
            deferred = (uu___2483_80135.deferred);
            univ_ineqs = (uu___2483_80135.univ_ineqs);
            implicits = (uu___2483_80135.implicits)
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
          let uu___2490_80232 = g  in
          let uu____80233 =
            let uu____80234 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80234  in
          {
            guard_f = uu____80233;
            deferred = (uu___2490_80232.deferred);
            univ_ineqs = (uu___2490_80232.univ_ineqs);
            implicits = (uu___2490_80232.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2495_80251 = g  in
          let uu____80252 =
            let uu____80253 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____80253  in
          {
            guard_f = uu____80252;
            deferred = (uu___2495_80251.deferred);
            univ_ineqs = (uu___2495_80251.univ_ineqs);
            implicits = (uu___2495_80251.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2499_80255 = g  in
          let uu____80256 =
            let uu____80257 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80257  in
          {
            guard_f = uu____80256;
            deferred = (uu___2499_80255.deferred);
            univ_ineqs = (uu___2499_80255.univ_ineqs);
            implicits = (uu___2499_80255.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____80264 ->
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
          let uu____80281 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____80281
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____80288 =
      let uu____80289 = FStar_Syntax_Util.unmeta t  in
      uu____80289.FStar_Syntax_Syntax.n  in
    match uu____80288 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____80293 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____80336 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____80336;
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
                       let uu____80431 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____80431
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2554_80438 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2554_80438.deferred);
              univ_ineqs = (uu___2554_80438.univ_ineqs);
              implicits = (uu___2554_80438.implicits)
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
               let uu____80472 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____80472
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
            let uu___2569_80499 = g  in
            let uu____80500 =
              let uu____80501 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____80501  in
            {
              guard_f = uu____80500;
              deferred = (uu___2569_80499.deferred);
              univ_ineqs = (uu___2569_80499.univ_ineqs);
              implicits = (uu___2569_80499.implicits)
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
              let uu____80559 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____80559 with
              | FStar_Pervasives_Native.Some
                  (uu____80584::(tm,uu____80586)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____80650 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____80668 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____80668;
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
                      let uu___2591_80700 = trivial_guard  in
                      {
                        guard_f = (uu___2591_80700.guard_f);
                        deferred = (uu___2591_80700.deferred);
                        univ_ineqs = (uu___2591_80700.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____80718  -> ());
    push = (fun uu____80720  -> ());
    pop = (fun uu____80723  -> ());
    snapshot =
      (fun uu____80726  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____80745  -> fun uu____80746  -> ());
    encode_sig = (fun uu____80761  -> fun uu____80762  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____80768 =
             let uu____80775 = FStar_Options.peek ()  in (e, g, uu____80775)
              in
           [uu____80768]);
    solve = (fun uu____80791  -> fun uu____80792  -> fun uu____80793  -> ());
    finish = (fun uu____80800  -> ());
    refresh = (fun uu____80802  -> ())
  } 