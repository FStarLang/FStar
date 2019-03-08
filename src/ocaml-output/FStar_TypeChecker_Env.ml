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
    match projectee with | Beta  -> true | uu____56083 -> false
  
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Iota  -> true | uu____56094 -> false
  
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Zeta  -> true | uu____56105 -> false
  
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____56117 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Weak  -> true | uu____56136 -> false
  
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | HNF  -> true | uu____56147 -> false
  
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____56158 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____56169 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____56180 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | DoNotUnfoldPureLets  -> true
    | uu____56191 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____56203 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____56225 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____56253 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____56281 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____56306 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____56317 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____56328 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____56339 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____56350 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____56361 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____56372 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____56383 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____56394 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____56405 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____56416 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE  -> true | uu____56427 -> false
  
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____56438 -> false
  
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
      | uu____56498 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____56524 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____56535 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Eager_unfolding_only  -> true
    | uu____56546 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____56558 -> false
  
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
           (fun uu___446_67820  ->
              match uu___446_67820 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____67823 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____67823  in
                  let uu____67824 =
                    let uu____67825 = FStar_Syntax_Subst.compress y  in
                    uu____67825.FStar_Syntax_Syntax.n  in
                  (match uu____67824 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____67829 =
                         let uu___775_67830 = y1  in
                         let uu____67831 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___775_67830.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___775_67830.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____67831
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____67829
                   | uu____67834 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___781_67848 = env  in
      let uu____67849 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___781_67848.solver);
        range = (uu___781_67848.range);
        curmodule = (uu___781_67848.curmodule);
        gamma = uu____67849;
        gamma_sig = (uu___781_67848.gamma_sig);
        gamma_cache = (uu___781_67848.gamma_cache);
        modules = (uu___781_67848.modules);
        expected_typ = (uu___781_67848.expected_typ);
        sigtab = (uu___781_67848.sigtab);
        attrtab = (uu___781_67848.attrtab);
        is_pattern = (uu___781_67848.is_pattern);
        instantiate_imp = (uu___781_67848.instantiate_imp);
        effects = (uu___781_67848.effects);
        generalize = (uu___781_67848.generalize);
        letrecs = (uu___781_67848.letrecs);
        top_level = (uu___781_67848.top_level);
        check_uvars = (uu___781_67848.check_uvars);
        use_eq = (uu___781_67848.use_eq);
        is_iface = (uu___781_67848.is_iface);
        admit = (uu___781_67848.admit);
        lax = (uu___781_67848.lax);
        lax_universes = (uu___781_67848.lax_universes);
        phase1 = (uu___781_67848.phase1);
        failhard = (uu___781_67848.failhard);
        nosynth = (uu___781_67848.nosynth);
        uvar_subtyping = (uu___781_67848.uvar_subtyping);
        tc_term = (uu___781_67848.tc_term);
        type_of = (uu___781_67848.type_of);
        universe_of = (uu___781_67848.universe_of);
        check_type_of = (uu___781_67848.check_type_of);
        use_bv_sorts = (uu___781_67848.use_bv_sorts);
        qtbl_name_and_index = (uu___781_67848.qtbl_name_and_index);
        normalized_eff_names = (uu___781_67848.normalized_eff_names);
        fv_delta_depths = (uu___781_67848.fv_delta_depths);
        proof_ns = (uu___781_67848.proof_ns);
        synth_hook = (uu___781_67848.synth_hook);
        splice = (uu___781_67848.splice);
        postprocess = (uu___781_67848.postprocess);
        is_native_tactic = (uu___781_67848.is_native_tactic);
        identifier_info = (uu___781_67848.identifier_info);
        tc_hooks = (uu___781_67848.tc_hooks);
        dsenv = (uu___781_67848.dsenv);
        nbe = (uu___781_67848.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____67857  -> fun uu____67858  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___788_67880 = env  in
      {
        solver = (uu___788_67880.solver);
        range = (uu___788_67880.range);
        curmodule = (uu___788_67880.curmodule);
        gamma = (uu___788_67880.gamma);
        gamma_sig = (uu___788_67880.gamma_sig);
        gamma_cache = (uu___788_67880.gamma_cache);
        modules = (uu___788_67880.modules);
        expected_typ = (uu___788_67880.expected_typ);
        sigtab = (uu___788_67880.sigtab);
        attrtab = (uu___788_67880.attrtab);
        is_pattern = (uu___788_67880.is_pattern);
        instantiate_imp = (uu___788_67880.instantiate_imp);
        effects = (uu___788_67880.effects);
        generalize = (uu___788_67880.generalize);
        letrecs = (uu___788_67880.letrecs);
        top_level = (uu___788_67880.top_level);
        check_uvars = (uu___788_67880.check_uvars);
        use_eq = (uu___788_67880.use_eq);
        is_iface = (uu___788_67880.is_iface);
        admit = (uu___788_67880.admit);
        lax = (uu___788_67880.lax);
        lax_universes = (uu___788_67880.lax_universes);
        phase1 = (uu___788_67880.phase1);
        failhard = (uu___788_67880.failhard);
        nosynth = (uu___788_67880.nosynth);
        uvar_subtyping = (uu___788_67880.uvar_subtyping);
        tc_term = (uu___788_67880.tc_term);
        type_of = (uu___788_67880.type_of);
        universe_of = (uu___788_67880.universe_of);
        check_type_of = (uu___788_67880.check_type_of);
        use_bv_sorts = (uu___788_67880.use_bv_sorts);
        qtbl_name_and_index = (uu___788_67880.qtbl_name_and_index);
        normalized_eff_names = (uu___788_67880.normalized_eff_names);
        fv_delta_depths = (uu___788_67880.fv_delta_depths);
        proof_ns = (uu___788_67880.proof_ns);
        synth_hook = (uu___788_67880.synth_hook);
        splice = (uu___788_67880.splice);
        postprocess = (uu___788_67880.postprocess);
        is_native_tactic = (uu___788_67880.is_native_tactic);
        identifier_info = (uu___788_67880.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___788_67880.dsenv);
        nbe = (uu___788_67880.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___792_67892 = e  in
      let uu____67893 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___792_67892.solver);
        range = (uu___792_67892.range);
        curmodule = (uu___792_67892.curmodule);
        gamma = (uu___792_67892.gamma);
        gamma_sig = (uu___792_67892.gamma_sig);
        gamma_cache = (uu___792_67892.gamma_cache);
        modules = (uu___792_67892.modules);
        expected_typ = (uu___792_67892.expected_typ);
        sigtab = (uu___792_67892.sigtab);
        attrtab = (uu___792_67892.attrtab);
        is_pattern = (uu___792_67892.is_pattern);
        instantiate_imp = (uu___792_67892.instantiate_imp);
        effects = (uu___792_67892.effects);
        generalize = (uu___792_67892.generalize);
        letrecs = (uu___792_67892.letrecs);
        top_level = (uu___792_67892.top_level);
        check_uvars = (uu___792_67892.check_uvars);
        use_eq = (uu___792_67892.use_eq);
        is_iface = (uu___792_67892.is_iface);
        admit = (uu___792_67892.admit);
        lax = (uu___792_67892.lax);
        lax_universes = (uu___792_67892.lax_universes);
        phase1 = (uu___792_67892.phase1);
        failhard = (uu___792_67892.failhard);
        nosynth = (uu___792_67892.nosynth);
        uvar_subtyping = (uu___792_67892.uvar_subtyping);
        tc_term = (uu___792_67892.tc_term);
        type_of = (uu___792_67892.type_of);
        universe_of = (uu___792_67892.universe_of);
        check_type_of = (uu___792_67892.check_type_of);
        use_bv_sorts = (uu___792_67892.use_bv_sorts);
        qtbl_name_and_index = (uu___792_67892.qtbl_name_and_index);
        normalized_eff_names = (uu___792_67892.normalized_eff_names);
        fv_delta_depths = (uu___792_67892.fv_delta_depths);
        proof_ns = (uu___792_67892.proof_ns);
        synth_hook = (uu___792_67892.synth_hook);
        splice = (uu___792_67892.splice);
        postprocess = (uu___792_67892.postprocess);
        is_native_tactic = (uu___792_67892.is_native_tactic);
        identifier_info = (uu___792_67892.identifier_info);
        tc_hooks = (uu___792_67892.tc_hooks);
        dsenv = uu____67893;
        nbe = (uu___792_67892.nbe)
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
      | (NoDelta ,uu____67922) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____67925,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____67927,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____67930 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____67944 . unit -> 'Auu____67944 FStar_Util.smap =
  fun uu____67951  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____67957 . unit -> 'Auu____67957 FStar_Util.smap =
  fun uu____67964  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____68102 = new_gamma_cache ()  in
                  let uu____68105 = new_sigtab ()  in
                  let uu____68108 = new_sigtab ()  in
                  let uu____68115 =
                    let uu____68130 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____68130, FStar_Pervasives_Native.None)  in
                  let uu____68151 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____68155 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____68159 = FStar_Options.using_facts_from ()  in
                  let uu____68160 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____68163 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____68102;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____68105;
                    attrtab = uu____68108;
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
                    qtbl_name_and_index = uu____68115;
                    normalized_eff_names = uu____68151;
                    fv_delta_depths = uu____68155;
                    proof_ns = uu____68159;
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
                    is_native_tactic = (fun uu____68225  -> false);
                    identifier_info = uu____68160;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____68163;
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
  fun uu____68337  ->
    let uu____68338 = FStar_ST.op_Bang query_indices  in
    match uu____68338 with
    | [] -> failwith "Empty query indices!"
    | uu____68393 ->
        let uu____68403 =
          let uu____68413 =
            let uu____68421 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____68421  in
          let uu____68475 = FStar_ST.op_Bang query_indices  in uu____68413 ::
            uu____68475
           in
        FStar_ST.op_Colon_Equals query_indices uu____68403
  
let (pop_query_indices : unit -> unit) =
  fun uu____68571  ->
    let uu____68572 = FStar_ST.op_Bang query_indices  in
    match uu____68572 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____68699  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____68736  ->
    match uu____68736 with
    | (l,n1) ->
        let uu____68746 = FStar_ST.op_Bang query_indices  in
        (match uu____68746 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____68868 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____68891  ->
    let uu____68892 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____68892
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____68971 =
       let uu____68974 = FStar_ST.op_Bang stack  in env :: uu____68974  in
     FStar_ST.op_Colon_Equals stack uu____68971);
    (let uu___860_69023 = env  in
     let uu____69024 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____69027 = FStar_Util.smap_copy (sigtab env)  in
     let uu____69030 = FStar_Util.smap_copy (attrtab env)  in
     let uu____69037 =
       let uu____69052 =
         let uu____69056 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____69056  in
       let uu____69088 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____69052, uu____69088)  in
     let uu____69137 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____69140 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____69143 =
       let uu____69146 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____69146  in
     {
       solver = (uu___860_69023.solver);
       range = (uu___860_69023.range);
       curmodule = (uu___860_69023.curmodule);
       gamma = (uu___860_69023.gamma);
       gamma_sig = (uu___860_69023.gamma_sig);
       gamma_cache = uu____69024;
       modules = (uu___860_69023.modules);
       expected_typ = (uu___860_69023.expected_typ);
       sigtab = uu____69027;
       attrtab = uu____69030;
       is_pattern = (uu___860_69023.is_pattern);
       instantiate_imp = (uu___860_69023.instantiate_imp);
       effects = (uu___860_69023.effects);
       generalize = (uu___860_69023.generalize);
       letrecs = (uu___860_69023.letrecs);
       top_level = (uu___860_69023.top_level);
       check_uvars = (uu___860_69023.check_uvars);
       use_eq = (uu___860_69023.use_eq);
       is_iface = (uu___860_69023.is_iface);
       admit = (uu___860_69023.admit);
       lax = (uu___860_69023.lax);
       lax_universes = (uu___860_69023.lax_universes);
       phase1 = (uu___860_69023.phase1);
       failhard = (uu___860_69023.failhard);
       nosynth = (uu___860_69023.nosynth);
       uvar_subtyping = (uu___860_69023.uvar_subtyping);
       tc_term = (uu___860_69023.tc_term);
       type_of = (uu___860_69023.type_of);
       universe_of = (uu___860_69023.universe_of);
       check_type_of = (uu___860_69023.check_type_of);
       use_bv_sorts = (uu___860_69023.use_bv_sorts);
       qtbl_name_and_index = uu____69037;
       normalized_eff_names = uu____69137;
       fv_delta_depths = uu____69140;
       proof_ns = (uu___860_69023.proof_ns);
       synth_hook = (uu___860_69023.synth_hook);
       splice = (uu___860_69023.splice);
       postprocess = (uu___860_69023.postprocess);
       is_native_tactic = (uu___860_69023.is_native_tactic);
       identifier_info = uu____69143;
       tc_hooks = (uu___860_69023.tc_hooks);
       dsenv = (uu___860_69023.dsenv);
       nbe = (uu___860_69023.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____69193  ->
    let uu____69194 = FStar_ST.op_Bang stack  in
    match uu____69194 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____69248 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____69338  ->
           let uu____69339 = snapshot_stack env  in
           match uu____69339 with
           | (stack_depth,env1) ->
               let uu____69373 = snapshot_query_indices ()  in
               (match uu____69373 with
                | (query_indices_depth,()) ->
                    let uu____69406 = (env1.solver).snapshot msg  in
                    (match uu____69406 with
                     | (solver_depth,()) ->
                         let uu____69463 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____69463 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___885_69530 = env1  in
                                 {
                                   solver = (uu___885_69530.solver);
                                   range = (uu___885_69530.range);
                                   curmodule = (uu___885_69530.curmodule);
                                   gamma = (uu___885_69530.gamma);
                                   gamma_sig = (uu___885_69530.gamma_sig);
                                   gamma_cache = (uu___885_69530.gamma_cache);
                                   modules = (uu___885_69530.modules);
                                   expected_typ =
                                     (uu___885_69530.expected_typ);
                                   sigtab = (uu___885_69530.sigtab);
                                   attrtab = (uu___885_69530.attrtab);
                                   is_pattern = (uu___885_69530.is_pattern);
                                   instantiate_imp =
                                     (uu___885_69530.instantiate_imp);
                                   effects = (uu___885_69530.effects);
                                   generalize = (uu___885_69530.generalize);
                                   letrecs = (uu___885_69530.letrecs);
                                   top_level = (uu___885_69530.top_level);
                                   check_uvars = (uu___885_69530.check_uvars);
                                   use_eq = (uu___885_69530.use_eq);
                                   is_iface = (uu___885_69530.is_iface);
                                   admit = (uu___885_69530.admit);
                                   lax = (uu___885_69530.lax);
                                   lax_universes =
                                     (uu___885_69530.lax_universes);
                                   phase1 = (uu___885_69530.phase1);
                                   failhard = (uu___885_69530.failhard);
                                   nosynth = (uu___885_69530.nosynth);
                                   uvar_subtyping =
                                     (uu___885_69530.uvar_subtyping);
                                   tc_term = (uu___885_69530.tc_term);
                                   type_of = (uu___885_69530.type_of);
                                   universe_of = (uu___885_69530.universe_of);
                                   check_type_of =
                                     (uu___885_69530.check_type_of);
                                   use_bv_sorts =
                                     (uu___885_69530.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___885_69530.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___885_69530.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___885_69530.fv_delta_depths);
                                   proof_ns = (uu___885_69530.proof_ns);
                                   synth_hook = (uu___885_69530.synth_hook);
                                   splice = (uu___885_69530.splice);
                                   postprocess = (uu___885_69530.postprocess);
                                   is_native_tactic =
                                     (uu___885_69530.is_native_tactic);
                                   identifier_info =
                                     (uu___885_69530.identifier_info);
                                   tc_hooks = (uu___885_69530.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___885_69530.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____69564  ->
             let uu____69565 =
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
             match uu____69565 with
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
                             ((let uu____69745 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____69745
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____69761 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____69761
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____69793,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____69835 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____69865  ->
                  match uu____69865 with
                  | (m,uu____69873) -> FStar_Ident.lid_equals l m))
           in
        (match uu____69835 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___930_69888 = env  in
               {
                 solver = (uu___930_69888.solver);
                 range = (uu___930_69888.range);
                 curmodule = (uu___930_69888.curmodule);
                 gamma = (uu___930_69888.gamma);
                 gamma_sig = (uu___930_69888.gamma_sig);
                 gamma_cache = (uu___930_69888.gamma_cache);
                 modules = (uu___930_69888.modules);
                 expected_typ = (uu___930_69888.expected_typ);
                 sigtab = (uu___930_69888.sigtab);
                 attrtab = (uu___930_69888.attrtab);
                 is_pattern = (uu___930_69888.is_pattern);
                 instantiate_imp = (uu___930_69888.instantiate_imp);
                 effects = (uu___930_69888.effects);
                 generalize = (uu___930_69888.generalize);
                 letrecs = (uu___930_69888.letrecs);
                 top_level = (uu___930_69888.top_level);
                 check_uvars = (uu___930_69888.check_uvars);
                 use_eq = (uu___930_69888.use_eq);
                 is_iface = (uu___930_69888.is_iface);
                 admit = (uu___930_69888.admit);
                 lax = (uu___930_69888.lax);
                 lax_universes = (uu___930_69888.lax_universes);
                 phase1 = (uu___930_69888.phase1);
                 failhard = (uu___930_69888.failhard);
                 nosynth = (uu___930_69888.nosynth);
                 uvar_subtyping = (uu___930_69888.uvar_subtyping);
                 tc_term = (uu___930_69888.tc_term);
                 type_of = (uu___930_69888.type_of);
                 universe_of = (uu___930_69888.universe_of);
                 check_type_of = (uu___930_69888.check_type_of);
                 use_bv_sorts = (uu___930_69888.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___930_69888.normalized_eff_names);
                 fv_delta_depths = (uu___930_69888.fv_delta_depths);
                 proof_ns = (uu___930_69888.proof_ns);
                 synth_hook = (uu___930_69888.synth_hook);
                 splice = (uu___930_69888.splice);
                 postprocess = (uu___930_69888.postprocess);
                 is_native_tactic = (uu___930_69888.is_native_tactic);
                 identifier_info = (uu___930_69888.identifier_info);
                 tc_hooks = (uu___930_69888.tc_hooks);
                 dsenv = (uu___930_69888.dsenv);
                 nbe = (uu___930_69888.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____69905,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___939_69921 = env  in
               {
                 solver = (uu___939_69921.solver);
                 range = (uu___939_69921.range);
                 curmodule = (uu___939_69921.curmodule);
                 gamma = (uu___939_69921.gamma);
                 gamma_sig = (uu___939_69921.gamma_sig);
                 gamma_cache = (uu___939_69921.gamma_cache);
                 modules = (uu___939_69921.modules);
                 expected_typ = (uu___939_69921.expected_typ);
                 sigtab = (uu___939_69921.sigtab);
                 attrtab = (uu___939_69921.attrtab);
                 is_pattern = (uu___939_69921.is_pattern);
                 instantiate_imp = (uu___939_69921.instantiate_imp);
                 effects = (uu___939_69921.effects);
                 generalize = (uu___939_69921.generalize);
                 letrecs = (uu___939_69921.letrecs);
                 top_level = (uu___939_69921.top_level);
                 check_uvars = (uu___939_69921.check_uvars);
                 use_eq = (uu___939_69921.use_eq);
                 is_iface = (uu___939_69921.is_iface);
                 admit = (uu___939_69921.admit);
                 lax = (uu___939_69921.lax);
                 lax_universes = (uu___939_69921.lax_universes);
                 phase1 = (uu___939_69921.phase1);
                 failhard = (uu___939_69921.failhard);
                 nosynth = (uu___939_69921.nosynth);
                 uvar_subtyping = (uu___939_69921.uvar_subtyping);
                 tc_term = (uu___939_69921.tc_term);
                 type_of = (uu___939_69921.type_of);
                 universe_of = (uu___939_69921.universe_of);
                 check_type_of = (uu___939_69921.check_type_of);
                 use_bv_sorts = (uu___939_69921.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___939_69921.normalized_eff_names);
                 fv_delta_depths = (uu___939_69921.fv_delta_depths);
                 proof_ns = (uu___939_69921.proof_ns);
                 synth_hook = (uu___939_69921.synth_hook);
                 splice = (uu___939_69921.splice);
                 postprocess = (uu___939_69921.postprocess);
                 is_native_tactic = (uu___939_69921.is_native_tactic);
                 identifier_info = (uu___939_69921.identifier_info);
                 tc_hooks = (uu___939_69921.tc_hooks);
                 dsenv = (uu___939_69921.dsenv);
                 nbe = (uu___939_69921.nbe)
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
        (let uu___946_69964 = e  in
         {
           solver = (uu___946_69964.solver);
           range = r;
           curmodule = (uu___946_69964.curmodule);
           gamma = (uu___946_69964.gamma);
           gamma_sig = (uu___946_69964.gamma_sig);
           gamma_cache = (uu___946_69964.gamma_cache);
           modules = (uu___946_69964.modules);
           expected_typ = (uu___946_69964.expected_typ);
           sigtab = (uu___946_69964.sigtab);
           attrtab = (uu___946_69964.attrtab);
           is_pattern = (uu___946_69964.is_pattern);
           instantiate_imp = (uu___946_69964.instantiate_imp);
           effects = (uu___946_69964.effects);
           generalize = (uu___946_69964.generalize);
           letrecs = (uu___946_69964.letrecs);
           top_level = (uu___946_69964.top_level);
           check_uvars = (uu___946_69964.check_uvars);
           use_eq = (uu___946_69964.use_eq);
           is_iface = (uu___946_69964.is_iface);
           admit = (uu___946_69964.admit);
           lax = (uu___946_69964.lax);
           lax_universes = (uu___946_69964.lax_universes);
           phase1 = (uu___946_69964.phase1);
           failhard = (uu___946_69964.failhard);
           nosynth = (uu___946_69964.nosynth);
           uvar_subtyping = (uu___946_69964.uvar_subtyping);
           tc_term = (uu___946_69964.tc_term);
           type_of = (uu___946_69964.type_of);
           universe_of = (uu___946_69964.universe_of);
           check_type_of = (uu___946_69964.check_type_of);
           use_bv_sorts = (uu___946_69964.use_bv_sorts);
           qtbl_name_and_index = (uu___946_69964.qtbl_name_and_index);
           normalized_eff_names = (uu___946_69964.normalized_eff_names);
           fv_delta_depths = (uu___946_69964.fv_delta_depths);
           proof_ns = (uu___946_69964.proof_ns);
           synth_hook = (uu___946_69964.synth_hook);
           splice = (uu___946_69964.splice);
           postprocess = (uu___946_69964.postprocess);
           is_native_tactic = (uu___946_69964.is_native_tactic);
           identifier_info = (uu___946_69964.identifier_info);
           tc_hooks = (uu___946_69964.tc_hooks);
           dsenv = (uu___946_69964.dsenv);
           nbe = (uu___946_69964.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____69984 =
        let uu____69985 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____69985 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____69984
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____70040 =
          let uu____70041 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____70041 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70040
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____70096 =
          let uu____70097 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____70097 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____70096
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____70152 =
        let uu____70153 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____70153 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____70152
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___963_70217 = env  in
      {
        solver = (uu___963_70217.solver);
        range = (uu___963_70217.range);
        curmodule = lid;
        gamma = (uu___963_70217.gamma);
        gamma_sig = (uu___963_70217.gamma_sig);
        gamma_cache = (uu___963_70217.gamma_cache);
        modules = (uu___963_70217.modules);
        expected_typ = (uu___963_70217.expected_typ);
        sigtab = (uu___963_70217.sigtab);
        attrtab = (uu___963_70217.attrtab);
        is_pattern = (uu___963_70217.is_pattern);
        instantiate_imp = (uu___963_70217.instantiate_imp);
        effects = (uu___963_70217.effects);
        generalize = (uu___963_70217.generalize);
        letrecs = (uu___963_70217.letrecs);
        top_level = (uu___963_70217.top_level);
        check_uvars = (uu___963_70217.check_uvars);
        use_eq = (uu___963_70217.use_eq);
        is_iface = (uu___963_70217.is_iface);
        admit = (uu___963_70217.admit);
        lax = (uu___963_70217.lax);
        lax_universes = (uu___963_70217.lax_universes);
        phase1 = (uu___963_70217.phase1);
        failhard = (uu___963_70217.failhard);
        nosynth = (uu___963_70217.nosynth);
        uvar_subtyping = (uu___963_70217.uvar_subtyping);
        tc_term = (uu___963_70217.tc_term);
        type_of = (uu___963_70217.type_of);
        universe_of = (uu___963_70217.universe_of);
        check_type_of = (uu___963_70217.check_type_of);
        use_bv_sorts = (uu___963_70217.use_bv_sorts);
        qtbl_name_and_index = (uu___963_70217.qtbl_name_and_index);
        normalized_eff_names = (uu___963_70217.normalized_eff_names);
        fv_delta_depths = (uu___963_70217.fv_delta_depths);
        proof_ns = (uu___963_70217.proof_ns);
        synth_hook = (uu___963_70217.synth_hook);
        splice = (uu___963_70217.splice);
        postprocess = (uu___963_70217.postprocess);
        is_native_tactic = (uu___963_70217.is_native_tactic);
        identifier_info = (uu___963_70217.identifier_info);
        tc_hooks = (uu___963_70217.tc_hooks);
        dsenv = (uu___963_70217.dsenv);
        nbe = (uu___963_70217.nbe)
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
      let uu____70248 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____70248
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____70261 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____70261)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____70276 =
      let uu____70278 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____70278  in
    (FStar_Errors.Fatal_VariableNotFound, uu____70276)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____70287  ->
    let uu____70288 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____70288
  
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
      | ((formals,t),uu____70388) ->
          let vs = mk_univ_subst formals us  in
          let uu____70412 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____70412)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___447_70429  ->
    match uu___447_70429 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____70455  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____70475 = inst_tscheme t  in
      match uu____70475 with
      | (us,t1) ->
          let uu____70486 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____70486)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____70507  ->
          match uu____70507 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____70529 =
                         let uu____70531 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____70535 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____70539 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____70541 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____70531 uu____70535 uu____70539 uu____70541
                          in
                       failwith uu____70529)
                    else ();
                    (let uu____70546 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____70546))
               | uu____70555 ->
                   let uu____70556 =
                     let uu____70558 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____70558
                      in
                   failwith uu____70556)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____70570 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____70581 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____70592 -> false
  
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
             | ([],uu____70640) -> Maybe
             | (uu____70647,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____70667 -> No  in
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
          let uu____70761 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____70761 with
          | FStar_Pervasives_Native.None  ->
              let uu____70784 =
                FStar_Util.find_map env.gamma
                  (fun uu___448_70828  ->
                     match uu___448_70828 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____70867 = FStar_Ident.lid_equals lid l  in
                         if uu____70867
                         then
                           let uu____70890 =
                             let uu____70909 =
                               let uu____70924 = inst_tscheme t  in
                               FStar_Util.Inl uu____70924  in
                             let uu____70939 = FStar_Ident.range_of_lid l  in
                             (uu____70909, uu____70939)  in
                           FStar_Pervasives_Native.Some uu____70890
                         else FStar_Pervasives_Native.None
                     | uu____70992 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____70784
                (fun uu____71030  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___449_71039  ->
                        match uu___449_71039 with
                        | (uu____71042,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____71044);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____71045;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____71046;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____71047;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____71048;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____71068 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____71068
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
                                  uu____71120 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____71127 -> cache t  in
                            let uu____71128 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____71128 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____71134 =
                                   let uu____71135 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____71135)
                                    in
                                 maybe_cache uu____71134)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____71206 = find_in_sigtab env lid  in
         match uu____71206 with
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
      let uu____71287 = lookup_qname env lid  in
      match uu____71287 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____71308,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____71422 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____71422 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____71467 =
          let uu____71470 = lookup_attr env1 attr  in se1 :: uu____71470  in
        FStar_Util.smap_add (attrtab env1) attr uu____71467  in
      FStar_List.iter
        (fun attr  ->
           let uu____71480 =
             let uu____71481 = FStar_Syntax_Subst.compress attr  in
             uu____71481.FStar_Syntax_Syntax.n  in
           match uu____71480 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____71485 =
                 let uu____71487 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____71487.FStar_Ident.str  in
               add_one1 env se uu____71485
           | uu____71488 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____71511) ->
          add_sigelts env ses
      | uu____71520 ->
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
            | uu____71535 -> ()))

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
        (fun uu___450_71567  ->
           match uu___450_71567 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____71585 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____71647,lb::[]),uu____71649) ->
            let uu____71658 =
              let uu____71667 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____71676 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____71667, uu____71676)  in
            FStar_Pervasives_Native.Some uu____71658
        | FStar_Syntax_Syntax.Sig_let ((uu____71689,lbs),uu____71691) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____71723 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____71736 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____71736
                     then
                       let uu____71749 =
                         let uu____71758 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____71767 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____71758, uu____71767)  in
                       FStar_Pervasives_Native.Some uu____71749
                     else FStar_Pervasives_Native.None)
        | uu____71790 -> FStar_Pervasives_Native.None
  
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
          let uu____71850 =
            let uu____71859 =
              let uu____71864 =
                let uu____71865 =
                  let uu____71868 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____71868
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____71865)  in
              inst_tscheme1 uu____71864  in
            (uu____71859, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71850
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____71890,uu____71891) ->
          let uu____71896 =
            let uu____71905 =
              let uu____71910 =
                let uu____71911 =
                  let uu____71914 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____71914  in
                (us, uu____71911)  in
              inst_tscheme1 uu____71910  in
            (uu____71905, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____71896
      | uu____71933 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____72022 =
          match uu____72022 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____72118,uvs,t,uu____72121,uu____72122,uu____72123);
                      FStar_Syntax_Syntax.sigrng = uu____72124;
                      FStar_Syntax_Syntax.sigquals = uu____72125;
                      FStar_Syntax_Syntax.sigmeta = uu____72126;
                      FStar_Syntax_Syntax.sigattrs = uu____72127;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72150 =
                     let uu____72159 = inst_tscheme1 (uvs, t)  in
                     (uu____72159, rng)  in
                   FStar_Pervasives_Native.Some uu____72150
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____72183;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____72185;
                      FStar_Syntax_Syntax.sigattrs = uu____72186;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____72203 =
                     let uu____72205 = in_cur_mod env l  in uu____72205 = Yes
                      in
                   if uu____72203
                   then
                     let uu____72217 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____72217
                      then
                        let uu____72233 =
                          let uu____72242 = inst_tscheme1 (uvs, t)  in
                          (uu____72242, rng)  in
                        FStar_Pervasives_Native.Some uu____72233
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____72275 =
                        let uu____72284 = inst_tscheme1 (uvs, t)  in
                        (uu____72284, rng)  in
                      FStar_Pervasives_Native.Some uu____72275)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72309,uu____72310);
                      FStar_Syntax_Syntax.sigrng = uu____72311;
                      FStar_Syntax_Syntax.sigquals = uu____72312;
                      FStar_Syntax_Syntax.sigmeta = uu____72313;
                      FStar_Syntax_Syntax.sigattrs = uu____72314;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____72355 =
                          let uu____72364 = inst_tscheme1 (uvs, k)  in
                          (uu____72364, rng)  in
                        FStar_Pervasives_Native.Some uu____72355
                    | uu____72385 ->
                        let uu____72386 =
                          let uu____72395 =
                            let uu____72400 =
                              let uu____72401 =
                                let uu____72404 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72404
                                 in
                              (uvs, uu____72401)  in
                            inst_tscheme1 uu____72400  in
                          (uu____72395, rng)  in
                        FStar_Pervasives_Native.Some uu____72386)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____72427,uu____72428);
                      FStar_Syntax_Syntax.sigrng = uu____72429;
                      FStar_Syntax_Syntax.sigquals = uu____72430;
                      FStar_Syntax_Syntax.sigmeta = uu____72431;
                      FStar_Syntax_Syntax.sigattrs = uu____72432;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____72474 =
                          let uu____72483 = inst_tscheme_with (uvs, k) us  in
                          (uu____72483, rng)  in
                        FStar_Pervasives_Native.Some uu____72474
                    | uu____72504 ->
                        let uu____72505 =
                          let uu____72514 =
                            let uu____72519 =
                              let uu____72520 =
                                let uu____72523 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____72523
                                 in
                              (uvs, uu____72520)  in
                            inst_tscheme_with uu____72519 us  in
                          (uu____72514, rng)  in
                        FStar_Pervasives_Native.Some uu____72505)
               | FStar_Util.Inr se ->
                   let uu____72559 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____72580;
                          FStar_Syntax_Syntax.sigrng = uu____72581;
                          FStar_Syntax_Syntax.sigquals = uu____72582;
                          FStar_Syntax_Syntax.sigmeta = uu____72583;
                          FStar_Syntax_Syntax.sigattrs = uu____72584;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____72599 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____72559
                     (FStar_Util.map_option
                        (fun uu____72647  ->
                           match uu____72647 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____72678 =
          let uu____72689 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____72689 mapper  in
        match uu____72678 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____72763 =
              let uu____72774 =
                let uu____72781 =
                  let uu___1290_72784 = t  in
                  let uu____72785 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___1290_72784.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____72785;
                    FStar_Syntax_Syntax.vars =
                      (uu___1290_72784.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____72781)  in
              (uu____72774, r)  in
            FStar_Pervasives_Native.Some uu____72763
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____72834 = lookup_qname env l  in
      match uu____72834 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____72855 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____72909 = try_lookup_bv env bv  in
      match uu____72909 with
      | FStar_Pervasives_Native.None  ->
          let uu____72924 = variable_not_found bv  in
          FStar_Errors.raise_error uu____72924 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____72940 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____72941 =
            let uu____72942 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____72942  in
          (uu____72940, uu____72941)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____72964 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____72964 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____73030 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____73030  in
          let uu____73031 =
            let uu____73040 =
              let uu____73045 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____73045)  in
            (uu____73040, r1)  in
          FStar_Pervasives_Native.Some uu____73031
  
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
        let uu____73080 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____73080 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____73113,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____73138 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____73138  in
            let uu____73139 =
              let uu____73144 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____73144, r1)  in
            FStar_Pervasives_Native.Some uu____73139
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____73168 = try_lookup_lid env l  in
      match uu____73168 with
      | FStar_Pervasives_Native.None  ->
          let uu____73195 = name_not_found l  in
          let uu____73201 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____73195 uu____73201
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___451_73244  ->
              match uu___451_73244 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____73248 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____73269 = lookup_qname env lid  in
      match uu____73269 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73278,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73281;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____73283;
              FStar_Syntax_Syntax.sigattrs = uu____73284;_},FStar_Pervasives_Native.None
            ),uu____73285)
          ->
          let uu____73334 =
            let uu____73341 =
              let uu____73342 =
                let uu____73345 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____73345 t  in
              (uvs, uu____73342)  in
            (uu____73341, q)  in
          FStar_Pervasives_Native.Some uu____73334
      | uu____73358 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73380 = lookup_qname env lid  in
      match uu____73380 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____73385,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____73388;
              FStar_Syntax_Syntax.sigquals = uu____73389;
              FStar_Syntax_Syntax.sigmeta = uu____73390;
              FStar_Syntax_Syntax.sigattrs = uu____73391;_},FStar_Pervasives_Native.None
            ),uu____73392)
          ->
          let uu____73441 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73441 (uvs, t)
      | uu____73446 ->
          let uu____73447 = name_not_found lid  in
          let uu____73453 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73447 uu____73453
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____73473 = lookup_qname env lid  in
      match uu____73473 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73478,uvs,t,uu____73481,uu____73482,uu____73483);
              FStar_Syntax_Syntax.sigrng = uu____73484;
              FStar_Syntax_Syntax.sigquals = uu____73485;
              FStar_Syntax_Syntax.sigmeta = uu____73486;
              FStar_Syntax_Syntax.sigattrs = uu____73487;_},FStar_Pervasives_Native.None
            ),uu____73488)
          ->
          let uu____73543 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____73543 (uvs, t)
      | uu____73548 ->
          let uu____73549 = name_not_found lid  in
          let uu____73555 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____73549 uu____73555
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____73578 = lookup_qname env lid  in
      match uu____73578 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____73586,uu____73587,uu____73588,uu____73589,uu____73590,dcs);
              FStar_Syntax_Syntax.sigrng = uu____73592;
              FStar_Syntax_Syntax.sigquals = uu____73593;
              FStar_Syntax_Syntax.sigmeta = uu____73594;
              FStar_Syntax_Syntax.sigattrs = uu____73595;_},uu____73596),uu____73597)
          -> (true, dcs)
      | uu____73660 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____73676 = lookup_qname env lid  in
      match uu____73676 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____73677,uu____73678,uu____73679,l,uu____73681,uu____73682);
              FStar_Syntax_Syntax.sigrng = uu____73683;
              FStar_Syntax_Syntax.sigquals = uu____73684;
              FStar_Syntax_Syntax.sigmeta = uu____73685;
              FStar_Syntax_Syntax.sigattrs = uu____73686;_},uu____73687),uu____73688)
          -> l
      | uu____73745 ->
          let uu____73746 =
            let uu____73748 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____73748  in
          failwith uu____73746
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____73818)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____73875) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____73899 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____73899
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____73934 -> FStar_Pervasives_Native.None)
          | uu____73943 -> FStar_Pervasives_Native.None
  
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
        let uu____74005 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____74005
  
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
        let uu____74038 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____74038
  
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
             (FStar_Util.Inl uu____74090,uu____74091) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____74140),uu____74141) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____74190 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____74208 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____74218 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____74235 ->
                  let uu____74242 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____74242
              | FStar_Syntax_Syntax.Sig_let ((uu____74243,lbs),uu____74245)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____74261 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____74261
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____74268 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____74276 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____74277 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____74284 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74285 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____74286 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74287 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____74300 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____74318 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____74318
           (fun d_opt  ->
              let uu____74331 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____74331
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____74341 =
                   let uu____74344 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____74344  in
                 match uu____74341 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____74345 =
                       let uu____74347 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____74347
                        in
                     failwith uu____74345
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____74352 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____74352
                       then
                         let uu____74355 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____74357 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____74359 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____74355 uu____74357 uu____74359
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
        (FStar_Util.Inr (se,uu____74384),uu____74385) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____74434 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____74456),uu____74457) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____74506 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____74528 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____74528
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____74551 = lookup_attrs_of_lid env fv_lid1  in
        match uu____74551 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____74575 =
                      let uu____74576 = FStar_Syntax_Util.un_uinst tm  in
                      uu____74576.FStar_Syntax_Syntax.n  in
                    match uu____74575 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____74581 -> false))
  
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
      let uu____74615 = lookup_qname env ftv  in
      match uu____74615 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____74619) ->
          let uu____74664 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____74664 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____74685,t),r) ->
               let uu____74700 =
                 let uu____74701 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____74701 t  in
               FStar_Pervasives_Native.Some uu____74700)
      | uu____74702 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____74714 = try_lookup_effect_lid env ftv  in
      match uu____74714 with
      | FStar_Pervasives_Native.None  ->
          let uu____74717 = name_not_found ftv  in
          let uu____74723 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____74717 uu____74723
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
        let uu____74747 = lookup_qname env lid0  in
        match uu____74747 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____74758);
                FStar_Syntax_Syntax.sigrng = uu____74759;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____74761;
                FStar_Syntax_Syntax.sigattrs = uu____74762;_},FStar_Pervasives_Native.None
              ),uu____74763)
            ->
            let lid1 =
              let uu____74817 =
                let uu____74818 = FStar_Ident.range_of_lid lid  in
                let uu____74819 =
                  let uu____74820 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____74820  in
                FStar_Range.set_use_range uu____74818 uu____74819  in
              FStar_Ident.set_lid_range lid uu____74817  in
            let uu____74821 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___452_74827  ->
                      match uu___452_74827 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____74830 -> false))
               in
            if uu____74821
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____74849 =
                      let uu____74851 =
                        let uu____74853 = get_range env  in
                        FStar_Range.string_of_range uu____74853  in
                      let uu____74854 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____74856 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____74851 uu____74854 uu____74856
                       in
                    failwith uu____74849)
                  in
               match (binders, univs1) with
               | ([],uu____74877) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____74903,uu____74904::uu____74905::uu____74906) ->
                   let uu____74927 =
                     let uu____74929 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____74931 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____74929 uu____74931
                      in
                   failwith uu____74927
               | uu____74942 ->
                   let uu____74957 =
                     let uu____74962 =
                       let uu____74963 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____74963)  in
                     inst_tscheme_with uu____74962 insts  in
                   (match uu____74957 with
                    | (uu____74976,t) ->
                        let t1 =
                          let uu____74979 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____74979 t  in
                        let uu____74980 =
                          let uu____74981 = FStar_Syntax_Subst.compress t1
                             in
                          uu____74981.FStar_Syntax_Syntax.n  in
                        (match uu____74980 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____75016 -> failwith "Impossible")))
        | uu____75024 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____75048 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____75048 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____75061,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____75068 = find1 l2  in
            (match uu____75068 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____75075 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____75075 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____75079 = find1 l  in
            (match uu____75079 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____75084 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____75084
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____75099 = lookup_qname env l1  in
      match uu____75099 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____75102;
              FStar_Syntax_Syntax.sigrng = uu____75103;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____75105;
              FStar_Syntax_Syntax.sigattrs = uu____75106;_},uu____75107),uu____75108)
          -> q
      | uu____75159 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____75183 =
          let uu____75184 =
            let uu____75186 = FStar_Util.string_of_int i  in
            let uu____75188 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____75186 uu____75188
             in
          failwith uu____75184  in
        let uu____75191 = lookup_datacon env lid  in
        match uu____75191 with
        | (uu____75196,t) ->
            let uu____75198 =
              let uu____75199 = FStar_Syntax_Subst.compress t  in
              uu____75199.FStar_Syntax_Syntax.n  in
            (match uu____75198 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____75203) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____75247 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____75247
                      FStar_Pervasives_Native.fst)
             | uu____75258 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75272 = lookup_qname env l  in
      match uu____75272 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____75274,uu____75275,uu____75276);
              FStar_Syntax_Syntax.sigrng = uu____75277;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75279;
              FStar_Syntax_Syntax.sigattrs = uu____75280;_},uu____75281),uu____75282)
          ->
          FStar_Util.for_some
            (fun uu___453_75335  ->
               match uu___453_75335 with
               | FStar_Syntax_Syntax.Projector uu____75337 -> true
               | uu____75343 -> false) quals
      | uu____75345 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75359 = lookup_qname env lid  in
      match uu____75359 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____75361,uu____75362,uu____75363,uu____75364,uu____75365,uu____75366);
              FStar_Syntax_Syntax.sigrng = uu____75367;
              FStar_Syntax_Syntax.sigquals = uu____75368;
              FStar_Syntax_Syntax.sigmeta = uu____75369;
              FStar_Syntax_Syntax.sigattrs = uu____75370;_},uu____75371),uu____75372)
          -> true
      | uu____75430 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75444 = lookup_qname env lid  in
      match uu____75444 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75446,uu____75447,uu____75448,uu____75449,uu____75450,uu____75451);
              FStar_Syntax_Syntax.sigrng = uu____75452;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____75454;
              FStar_Syntax_Syntax.sigattrs = uu____75455;_},uu____75456),uu____75457)
          ->
          FStar_Util.for_some
            (fun uu___454_75518  ->
               match uu___454_75518 with
               | FStar_Syntax_Syntax.RecordType uu____75520 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____75530 -> true
               | uu____75540 -> false) quals
      | uu____75542 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____75552,uu____75553);
            FStar_Syntax_Syntax.sigrng = uu____75554;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____75556;
            FStar_Syntax_Syntax.sigattrs = uu____75557;_},uu____75558),uu____75559)
        ->
        FStar_Util.for_some
          (fun uu___455_75616  ->
             match uu___455_75616 with
             | FStar_Syntax_Syntax.Action uu____75618 -> true
             | uu____75620 -> false) quals
    | uu____75622 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____75636 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____75636
  
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
      let uu____75653 =
        let uu____75654 = FStar_Syntax_Util.un_uinst head1  in
        uu____75654.FStar_Syntax_Syntax.n  in
      match uu____75653 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____75660 ->
               true
           | uu____75663 -> false)
      | uu____75665 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____75679 = lookup_qname env l  in
      match uu____75679 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____75682),uu____75683) ->
          FStar_Util.for_some
            (fun uu___456_75731  ->
               match uu___456_75731 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____75734 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____75736 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____75812 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____75830) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____75848 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____75856 ->
                 FStar_Pervasives_Native.Some true
             | uu____75875 -> FStar_Pervasives_Native.Some false)
         in
      let uu____75878 =
        let uu____75882 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____75882 mapper  in
      match uu____75878 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____75942 = lookup_qname env lid  in
      match uu____75942 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____75946,uu____75947,tps,uu____75949,uu____75950,uu____75951);
              FStar_Syntax_Syntax.sigrng = uu____75952;
              FStar_Syntax_Syntax.sigquals = uu____75953;
              FStar_Syntax_Syntax.sigmeta = uu____75954;
              FStar_Syntax_Syntax.sigattrs = uu____75955;_},uu____75956),uu____75957)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____76023 -> FStar_Pervasives_Native.None
  
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
           (fun uu____76069  ->
              match uu____76069 with
              | (d,uu____76078) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____76094 = effect_decl_opt env l  in
      match uu____76094 with
      | FStar_Pervasives_Native.None  ->
          let uu____76109 = name_not_found l  in
          let uu____76115 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____76109 uu____76115
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____76138  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____76157  ->
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
        let uu____76189 = FStar_Ident.lid_equals l1 l2  in
        if uu____76189
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____76200 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____76200
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____76211 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____76264  ->
                        match uu____76264 with
                        | (m1,m2,uu____76278,uu____76279,uu____76280) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____76211 with
              | FStar_Pervasives_Native.None  ->
                  let uu____76297 =
                    let uu____76303 =
                      let uu____76305 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____76307 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____76305
                        uu____76307
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____76303)
                     in
                  FStar_Errors.raise_error uu____76297 env.range
              | FStar_Pervasives_Native.Some
                  (uu____76317,uu____76318,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____76352 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____76352
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
  'Auu____76372 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____76372) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____76401 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____76427  ->
                match uu____76427 with
                | (d,uu____76434) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____76401 with
      | FStar_Pervasives_Native.None  ->
          let uu____76445 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____76445
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____76460 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____76460 with
           | (uu____76475,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____76493)::(wp,uu____76495)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____76551 -> failwith "Impossible"))
  
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
          let uu____76609 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____76609
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____76614 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____76614
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
                  let uu____76625 = get_range env  in
                  let uu____76626 =
                    let uu____76633 =
                      let uu____76634 =
                        let uu____76651 =
                          let uu____76662 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____76662]  in
                        (null_wp, uu____76651)  in
                      FStar_Syntax_Syntax.Tm_app uu____76634  in
                    FStar_Syntax_Syntax.mk uu____76633  in
                  uu____76626 FStar_Pervasives_Native.None uu____76625  in
                let uu____76702 =
                  let uu____76703 =
                    let uu____76714 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____76714]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____76703;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____76702))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1944_76752 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1944_76752.order);
              joins = (uu___1944_76752.joins)
            }  in
          let uu___1947_76761 = env  in
          {
            solver = (uu___1947_76761.solver);
            range = (uu___1947_76761.range);
            curmodule = (uu___1947_76761.curmodule);
            gamma = (uu___1947_76761.gamma);
            gamma_sig = (uu___1947_76761.gamma_sig);
            gamma_cache = (uu___1947_76761.gamma_cache);
            modules = (uu___1947_76761.modules);
            expected_typ = (uu___1947_76761.expected_typ);
            sigtab = (uu___1947_76761.sigtab);
            attrtab = (uu___1947_76761.attrtab);
            is_pattern = (uu___1947_76761.is_pattern);
            instantiate_imp = (uu___1947_76761.instantiate_imp);
            effects;
            generalize = (uu___1947_76761.generalize);
            letrecs = (uu___1947_76761.letrecs);
            top_level = (uu___1947_76761.top_level);
            check_uvars = (uu___1947_76761.check_uvars);
            use_eq = (uu___1947_76761.use_eq);
            is_iface = (uu___1947_76761.is_iface);
            admit = (uu___1947_76761.admit);
            lax = (uu___1947_76761.lax);
            lax_universes = (uu___1947_76761.lax_universes);
            phase1 = (uu___1947_76761.phase1);
            failhard = (uu___1947_76761.failhard);
            nosynth = (uu___1947_76761.nosynth);
            uvar_subtyping = (uu___1947_76761.uvar_subtyping);
            tc_term = (uu___1947_76761.tc_term);
            type_of = (uu___1947_76761.type_of);
            universe_of = (uu___1947_76761.universe_of);
            check_type_of = (uu___1947_76761.check_type_of);
            use_bv_sorts = (uu___1947_76761.use_bv_sorts);
            qtbl_name_and_index = (uu___1947_76761.qtbl_name_and_index);
            normalized_eff_names = (uu___1947_76761.normalized_eff_names);
            fv_delta_depths = (uu___1947_76761.fv_delta_depths);
            proof_ns = (uu___1947_76761.proof_ns);
            synth_hook = (uu___1947_76761.synth_hook);
            splice = (uu___1947_76761.splice);
            postprocess = (uu___1947_76761.postprocess);
            is_native_tactic = (uu___1947_76761.is_native_tactic);
            identifier_info = (uu___1947_76761.identifier_info);
            tc_hooks = (uu___1947_76761.tc_hooks);
            dsenv = (uu___1947_76761.dsenv);
            nbe = (uu___1947_76761.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____76791 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____76791  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____76949 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____76950 = l1 u t wp e  in
                                l2 u t uu____76949 uu____76950))
                | uu____76951 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____77023 = inst_tscheme_with lift_t [u]  in
            match uu____77023 with
            | (uu____77030,lift_t1) ->
                let uu____77032 =
                  let uu____77039 =
                    let uu____77040 =
                      let uu____77057 =
                        let uu____77068 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77077 =
                          let uu____77088 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____77088]  in
                        uu____77068 :: uu____77077  in
                      (lift_t1, uu____77057)  in
                    FStar_Syntax_Syntax.Tm_app uu____77040  in
                  FStar_Syntax_Syntax.mk uu____77039  in
                uu____77032 FStar_Pervasives_Native.None
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
            let uu____77201 = inst_tscheme_with lift_t [u]  in
            match uu____77201 with
            | (uu____77208,lift_t1) ->
                let uu____77210 =
                  let uu____77217 =
                    let uu____77218 =
                      let uu____77235 =
                        let uu____77246 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____77255 =
                          let uu____77266 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____77275 =
                            let uu____77286 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____77286]  in
                          uu____77266 :: uu____77275  in
                        uu____77246 :: uu____77255  in
                      (lift_t1, uu____77235)  in
                    FStar_Syntax_Syntax.Tm_app uu____77218  in
                  FStar_Syntax_Syntax.mk uu____77217  in
                uu____77210 FStar_Pervasives_Native.None
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
              let uu____77391 =
                let uu____77392 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____77392
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____77391  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____77401 =
              let uu____77403 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____77403  in
            let uu____77404 =
              let uu____77406 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____77434 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____77434)
                 in
              FStar_Util.dflt "none" uu____77406  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____77401
              uu____77404
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____77463  ->
                    match uu____77463 with
                    | (e,uu____77471) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____77494 =
            match uu____77494 with
            | (i,j) ->
                let uu____77505 = FStar_Ident.lid_equals i j  in
                if uu____77505
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _77512  -> FStar_Pervasives_Native.Some _77512)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____77541 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____77551 = FStar_Ident.lid_equals i k  in
                        if uu____77551
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____77565 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____77565
                                  then []
                                  else
                                    (let uu____77572 =
                                       let uu____77581 =
                                         find_edge order1 (i, k)  in
                                       let uu____77584 =
                                         find_edge order1 (k, j)  in
                                       (uu____77581, uu____77584)  in
                                     match uu____77572 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____77599 =
                                           compose_edges e1 e2  in
                                         [uu____77599]
                                     | uu____77600 -> [])))))
                 in
              FStar_List.append order1 uu____77541  in
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
                   let uu____77630 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____77633 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____77633
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____77630
                   then
                     let uu____77640 =
                       let uu____77646 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____77646)
                        in
                     let uu____77650 = get_range env  in
                     FStar_Errors.raise_error uu____77640 uu____77650
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____77728 = FStar_Ident.lid_equals i j
                                   in
                                if uu____77728
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____77780 =
                                              let uu____77789 =
                                                find_edge order2 (i, k)  in
                                              let uu____77792 =
                                                find_edge order2 (j, k)  in
                                              (uu____77789, uu____77792)  in
                                            match uu____77780 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____77834,uu____77835)
                                                     ->
                                                     let uu____77842 =
                                                       let uu____77849 =
                                                         let uu____77851 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77851
                                                          in
                                                       let uu____77854 =
                                                         let uu____77856 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____77856
                                                          in
                                                       (uu____77849,
                                                         uu____77854)
                                                        in
                                                     (match uu____77842 with
                                                      | (true ,true ) ->
                                                          let uu____77873 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____77873
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
                                            | uu____77916 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___2074_77989 = env.effects  in
              { decls = (uu___2074_77989.decls); order = order2; joins }  in
            let uu___2077_77990 = env  in
            {
              solver = (uu___2077_77990.solver);
              range = (uu___2077_77990.range);
              curmodule = (uu___2077_77990.curmodule);
              gamma = (uu___2077_77990.gamma);
              gamma_sig = (uu___2077_77990.gamma_sig);
              gamma_cache = (uu___2077_77990.gamma_cache);
              modules = (uu___2077_77990.modules);
              expected_typ = (uu___2077_77990.expected_typ);
              sigtab = (uu___2077_77990.sigtab);
              attrtab = (uu___2077_77990.attrtab);
              is_pattern = (uu___2077_77990.is_pattern);
              instantiate_imp = (uu___2077_77990.instantiate_imp);
              effects;
              generalize = (uu___2077_77990.generalize);
              letrecs = (uu___2077_77990.letrecs);
              top_level = (uu___2077_77990.top_level);
              check_uvars = (uu___2077_77990.check_uvars);
              use_eq = (uu___2077_77990.use_eq);
              is_iface = (uu___2077_77990.is_iface);
              admit = (uu___2077_77990.admit);
              lax = (uu___2077_77990.lax);
              lax_universes = (uu___2077_77990.lax_universes);
              phase1 = (uu___2077_77990.phase1);
              failhard = (uu___2077_77990.failhard);
              nosynth = (uu___2077_77990.nosynth);
              uvar_subtyping = (uu___2077_77990.uvar_subtyping);
              tc_term = (uu___2077_77990.tc_term);
              type_of = (uu___2077_77990.type_of);
              universe_of = (uu___2077_77990.universe_of);
              check_type_of = (uu___2077_77990.check_type_of);
              use_bv_sorts = (uu___2077_77990.use_bv_sorts);
              qtbl_name_and_index = (uu___2077_77990.qtbl_name_and_index);
              normalized_eff_names = (uu___2077_77990.normalized_eff_names);
              fv_delta_depths = (uu___2077_77990.fv_delta_depths);
              proof_ns = (uu___2077_77990.proof_ns);
              synth_hook = (uu___2077_77990.synth_hook);
              splice = (uu___2077_77990.splice);
              postprocess = (uu___2077_77990.postprocess);
              is_native_tactic = (uu___2077_77990.is_native_tactic);
              identifier_info = (uu___2077_77990.identifier_info);
              tc_hooks = (uu___2077_77990.tc_hooks);
              dsenv = (uu___2077_77990.dsenv);
              nbe = (uu___2077_77990.nbe)
            }))
      | uu____77991 -> env
  
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
        | uu____78020 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____78033 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____78033 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____78050 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____78050 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____78075 =
                     let uu____78081 =
                       let uu____78083 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____78091 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____78102 =
                         let uu____78104 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____78104  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____78083 uu____78091 uu____78102
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____78081)
                      in
                   FStar_Errors.raise_error uu____78075
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____78112 =
                     let uu____78123 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____78123 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____78160  ->
                        fun uu____78161  ->
                          match (uu____78160, uu____78161) with
                          | ((x,uu____78191),(t,uu____78193)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____78112
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____78224 =
                     let uu___2115_78225 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___2115_78225.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2115_78225.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___2115_78225.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___2115_78225.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____78224
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____78237 .
    'Auu____78237 ->
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
          let uu____78267 = effect_decl_opt env effect_name  in
          match uu____78267 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____78306 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____78329 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____78368 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____78368
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____78373 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____78373
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____78388 =
                     let uu____78391 = get_range env  in
                     let uu____78392 =
                       let uu____78399 =
                         let uu____78400 =
                           let uu____78417 =
                             let uu____78428 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____78428; wp]  in
                           (repr, uu____78417)  in
                         FStar_Syntax_Syntax.Tm_app uu____78400  in
                       FStar_Syntax_Syntax.mk uu____78399  in
                     uu____78392 FStar_Pervasives_Native.None uu____78391  in
                   FStar_Pervasives_Native.Some uu____78388)
  
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
      | uu____78575 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____78590 =
        let uu____78591 = FStar_Syntax_Subst.compress t  in
        uu____78591.FStar_Syntax_Syntax.n  in
      match uu____78590 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____78595,c) ->
          is_reifiable_comp env c
      | uu____78617 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____78637 =
           let uu____78639 = is_reifiable_effect env l  in
           Prims.op_Negation uu____78639  in
         if uu____78637
         then
           let uu____78642 =
             let uu____78648 =
               let uu____78650 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____78650
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____78648)  in
           let uu____78654 = get_range env  in
           FStar_Errors.raise_error uu____78642 uu____78654
         else ());
        (let uu____78657 = effect_repr_aux true env c u_c  in
         match uu____78657 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___2180_78693 = env  in
        {
          solver = (uu___2180_78693.solver);
          range = (uu___2180_78693.range);
          curmodule = (uu___2180_78693.curmodule);
          gamma = (uu___2180_78693.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___2180_78693.gamma_cache);
          modules = (uu___2180_78693.modules);
          expected_typ = (uu___2180_78693.expected_typ);
          sigtab = (uu___2180_78693.sigtab);
          attrtab = (uu___2180_78693.attrtab);
          is_pattern = (uu___2180_78693.is_pattern);
          instantiate_imp = (uu___2180_78693.instantiate_imp);
          effects = (uu___2180_78693.effects);
          generalize = (uu___2180_78693.generalize);
          letrecs = (uu___2180_78693.letrecs);
          top_level = (uu___2180_78693.top_level);
          check_uvars = (uu___2180_78693.check_uvars);
          use_eq = (uu___2180_78693.use_eq);
          is_iface = (uu___2180_78693.is_iface);
          admit = (uu___2180_78693.admit);
          lax = (uu___2180_78693.lax);
          lax_universes = (uu___2180_78693.lax_universes);
          phase1 = (uu___2180_78693.phase1);
          failhard = (uu___2180_78693.failhard);
          nosynth = (uu___2180_78693.nosynth);
          uvar_subtyping = (uu___2180_78693.uvar_subtyping);
          tc_term = (uu___2180_78693.tc_term);
          type_of = (uu___2180_78693.type_of);
          universe_of = (uu___2180_78693.universe_of);
          check_type_of = (uu___2180_78693.check_type_of);
          use_bv_sorts = (uu___2180_78693.use_bv_sorts);
          qtbl_name_and_index = (uu___2180_78693.qtbl_name_and_index);
          normalized_eff_names = (uu___2180_78693.normalized_eff_names);
          fv_delta_depths = (uu___2180_78693.fv_delta_depths);
          proof_ns = (uu___2180_78693.proof_ns);
          synth_hook = (uu___2180_78693.synth_hook);
          splice = (uu___2180_78693.splice);
          postprocess = (uu___2180_78693.postprocess);
          is_native_tactic = (uu___2180_78693.is_native_tactic);
          identifier_info = (uu___2180_78693.identifier_info);
          tc_hooks = (uu___2180_78693.tc_hooks);
          dsenv = (uu___2180_78693.dsenv);
          nbe = (uu___2180_78693.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___2187_78707 = env  in
      {
        solver = (uu___2187_78707.solver);
        range = (uu___2187_78707.range);
        curmodule = (uu___2187_78707.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___2187_78707.gamma_sig);
        gamma_cache = (uu___2187_78707.gamma_cache);
        modules = (uu___2187_78707.modules);
        expected_typ = (uu___2187_78707.expected_typ);
        sigtab = (uu___2187_78707.sigtab);
        attrtab = (uu___2187_78707.attrtab);
        is_pattern = (uu___2187_78707.is_pattern);
        instantiate_imp = (uu___2187_78707.instantiate_imp);
        effects = (uu___2187_78707.effects);
        generalize = (uu___2187_78707.generalize);
        letrecs = (uu___2187_78707.letrecs);
        top_level = (uu___2187_78707.top_level);
        check_uvars = (uu___2187_78707.check_uvars);
        use_eq = (uu___2187_78707.use_eq);
        is_iface = (uu___2187_78707.is_iface);
        admit = (uu___2187_78707.admit);
        lax = (uu___2187_78707.lax);
        lax_universes = (uu___2187_78707.lax_universes);
        phase1 = (uu___2187_78707.phase1);
        failhard = (uu___2187_78707.failhard);
        nosynth = (uu___2187_78707.nosynth);
        uvar_subtyping = (uu___2187_78707.uvar_subtyping);
        tc_term = (uu___2187_78707.tc_term);
        type_of = (uu___2187_78707.type_of);
        universe_of = (uu___2187_78707.universe_of);
        check_type_of = (uu___2187_78707.check_type_of);
        use_bv_sorts = (uu___2187_78707.use_bv_sorts);
        qtbl_name_and_index = (uu___2187_78707.qtbl_name_and_index);
        normalized_eff_names = (uu___2187_78707.normalized_eff_names);
        fv_delta_depths = (uu___2187_78707.fv_delta_depths);
        proof_ns = (uu___2187_78707.proof_ns);
        synth_hook = (uu___2187_78707.synth_hook);
        splice = (uu___2187_78707.splice);
        postprocess = (uu___2187_78707.postprocess);
        is_native_tactic = (uu___2187_78707.is_native_tactic);
        identifier_info = (uu___2187_78707.identifier_info);
        tc_hooks = (uu___2187_78707.tc_hooks);
        dsenv = (uu___2187_78707.dsenv);
        nbe = (uu___2187_78707.nbe)
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
            (let uu___2200_78765 = env  in
             {
               solver = (uu___2200_78765.solver);
               range = (uu___2200_78765.range);
               curmodule = (uu___2200_78765.curmodule);
               gamma = rest;
               gamma_sig = (uu___2200_78765.gamma_sig);
               gamma_cache = (uu___2200_78765.gamma_cache);
               modules = (uu___2200_78765.modules);
               expected_typ = (uu___2200_78765.expected_typ);
               sigtab = (uu___2200_78765.sigtab);
               attrtab = (uu___2200_78765.attrtab);
               is_pattern = (uu___2200_78765.is_pattern);
               instantiate_imp = (uu___2200_78765.instantiate_imp);
               effects = (uu___2200_78765.effects);
               generalize = (uu___2200_78765.generalize);
               letrecs = (uu___2200_78765.letrecs);
               top_level = (uu___2200_78765.top_level);
               check_uvars = (uu___2200_78765.check_uvars);
               use_eq = (uu___2200_78765.use_eq);
               is_iface = (uu___2200_78765.is_iface);
               admit = (uu___2200_78765.admit);
               lax = (uu___2200_78765.lax);
               lax_universes = (uu___2200_78765.lax_universes);
               phase1 = (uu___2200_78765.phase1);
               failhard = (uu___2200_78765.failhard);
               nosynth = (uu___2200_78765.nosynth);
               uvar_subtyping = (uu___2200_78765.uvar_subtyping);
               tc_term = (uu___2200_78765.tc_term);
               type_of = (uu___2200_78765.type_of);
               universe_of = (uu___2200_78765.universe_of);
               check_type_of = (uu___2200_78765.check_type_of);
               use_bv_sorts = (uu___2200_78765.use_bv_sorts);
               qtbl_name_and_index = (uu___2200_78765.qtbl_name_and_index);
               normalized_eff_names = (uu___2200_78765.normalized_eff_names);
               fv_delta_depths = (uu___2200_78765.fv_delta_depths);
               proof_ns = (uu___2200_78765.proof_ns);
               synth_hook = (uu___2200_78765.synth_hook);
               splice = (uu___2200_78765.splice);
               postprocess = (uu___2200_78765.postprocess);
               is_native_tactic = (uu___2200_78765.is_native_tactic);
               identifier_info = (uu___2200_78765.identifier_info);
               tc_hooks = (uu___2200_78765.tc_hooks);
               dsenv = (uu___2200_78765.dsenv);
               nbe = (uu___2200_78765.nbe)
             }))
    | uu____78766 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____78795  ->
             match uu____78795 with | (x,uu____78803) -> push_bv env1 x) env
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
            let uu___2214_78838 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___2214_78838.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___2214_78838.FStar_Syntax_Syntax.index);
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
      (let uu___2225_78880 = env  in
       {
         solver = (uu___2225_78880.solver);
         range = (uu___2225_78880.range);
         curmodule = (uu___2225_78880.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2225_78880.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___2225_78880.sigtab);
         attrtab = (uu___2225_78880.attrtab);
         is_pattern = (uu___2225_78880.is_pattern);
         instantiate_imp = (uu___2225_78880.instantiate_imp);
         effects = (uu___2225_78880.effects);
         generalize = (uu___2225_78880.generalize);
         letrecs = (uu___2225_78880.letrecs);
         top_level = (uu___2225_78880.top_level);
         check_uvars = (uu___2225_78880.check_uvars);
         use_eq = (uu___2225_78880.use_eq);
         is_iface = (uu___2225_78880.is_iface);
         admit = (uu___2225_78880.admit);
         lax = (uu___2225_78880.lax);
         lax_universes = (uu___2225_78880.lax_universes);
         phase1 = (uu___2225_78880.phase1);
         failhard = (uu___2225_78880.failhard);
         nosynth = (uu___2225_78880.nosynth);
         uvar_subtyping = (uu___2225_78880.uvar_subtyping);
         tc_term = (uu___2225_78880.tc_term);
         type_of = (uu___2225_78880.type_of);
         universe_of = (uu___2225_78880.universe_of);
         check_type_of = (uu___2225_78880.check_type_of);
         use_bv_sorts = (uu___2225_78880.use_bv_sorts);
         qtbl_name_and_index = (uu___2225_78880.qtbl_name_and_index);
         normalized_eff_names = (uu___2225_78880.normalized_eff_names);
         fv_delta_depths = (uu___2225_78880.fv_delta_depths);
         proof_ns = (uu___2225_78880.proof_ns);
         synth_hook = (uu___2225_78880.synth_hook);
         splice = (uu___2225_78880.splice);
         postprocess = (uu___2225_78880.postprocess);
         is_native_tactic = (uu___2225_78880.is_native_tactic);
         identifier_info = (uu___2225_78880.identifier_info);
         tc_hooks = (uu___2225_78880.tc_hooks);
         dsenv = (uu___2225_78880.dsenv);
         nbe = (uu___2225_78880.nbe)
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
        let uu____78924 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____78924 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____78952 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____78952)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___2240_78968 = env  in
      {
        solver = (uu___2240_78968.solver);
        range = (uu___2240_78968.range);
        curmodule = (uu___2240_78968.curmodule);
        gamma = (uu___2240_78968.gamma);
        gamma_sig = (uu___2240_78968.gamma_sig);
        gamma_cache = (uu___2240_78968.gamma_cache);
        modules = (uu___2240_78968.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___2240_78968.sigtab);
        attrtab = (uu___2240_78968.attrtab);
        is_pattern = (uu___2240_78968.is_pattern);
        instantiate_imp = (uu___2240_78968.instantiate_imp);
        effects = (uu___2240_78968.effects);
        generalize = (uu___2240_78968.generalize);
        letrecs = (uu___2240_78968.letrecs);
        top_level = (uu___2240_78968.top_level);
        check_uvars = (uu___2240_78968.check_uvars);
        use_eq = false;
        is_iface = (uu___2240_78968.is_iface);
        admit = (uu___2240_78968.admit);
        lax = (uu___2240_78968.lax);
        lax_universes = (uu___2240_78968.lax_universes);
        phase1 = (uu___2240_78968.phase1);
        failhard = (uu___2240_78968.failhard);
        nosynth = (uu___2240_78968.nosynth);
        uvar_subtyping = (uu___2240_78968.uvar_subtyping);
        tc_term = (uu___2240_78968.tc_term);
        type_of = (uu___2240_78968.type_of);
        universe_of = (uu___2240_78968.universe_of);
        check_type_of = (uu___2240_78968.check_type_of);
        use_bv_sorts = (uu___2240_78968.use_bv_sorts);
        qtbl_name_and_index = (uu___2240_78968.qtbl_name_and_index);
        normalized_eff_names = (uu___2240_78968.normalized_eff_names);
        fv_delta_depths = (uu___2240_78968.fv_delta_depths);
        proof_ns = (uu___2240_78968.proof_ns);
        synth_hook = (uu___2240_78968.synth_hook);
        splice = (uu___2240_78968.splice);
        postprocess = (uu___2240_78968.postprocess);
        is_native_tactic = (uu___2240_78968.is_native_tactic);
        identifier_info = (uu___2240_78968.identifier_info);
        tc_hooks = (uu___2240_78968.tc_hooks);
        dsenv = (uu___2240_78968.dsenv);
        nbe = (uu___2240_78968.nbe)
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
    let uu____78999 = expected_typ env_  in
    ((let uu___2247_79005 = env_  in
      {
        solver = (uu___2247_79005.solver);
        range = (uu___2247_79005.range);
        curmodule = (uu___2247_79005.curmodule);
        gamma = (uu___2247_79005.gamma);
        gamma_sig = (uu___2247_79005.gamma_sig);
        gamma_cache = (uu___2247_79005.gamma_cache);
        modules = (uu___2247_79005.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___2247_79005.sigtab);
        attrtab = (uu___2247_79005.attrtab);
        is_pattern = (uu___2247_79005.is_pattern);
        instantiate_imp = (uu___2247_79005.instantiate_imp);
        effects = (uu___2247_79005.effects);
        generalize = (uu___2247_79005.generalize);
        letrecs = (uu___2247_79005.letrecs);
        top_level = (uu___2247_79005.top_level);
        check_uvars = (uu___2247_79005.check_uvars);
        use_eq = false;
        is_iface = (uu___2247_79005.is_iface);
        admit = (uu___2247_79005.admit);
        lax = (uu___2247_79005.lax);
        lax_universes = (uu___2247_79005.lax_universes);
        phase1 = (uu___2247_79005.phase1);
        failhard = (uu___2247_79005.failhard);
        nosynth = (uu___2247_79005.nosynth);
        uvar_subtyping = (uu___2247_79005.uvar_subtyping);
        tc_term = (uu___2247_79005.tc_term);
        type_of = (uu___2247_79005.type_of);
        universe_of = (uu___2247_79005.universe_of);
        check_type_of = (uu___2247_79005.check_type_of);
        use_bv_sorts = (uu___2247_79005.use_bv_sorts);
        qtbl_name_and_index = (uu___2247_79005.qtbl_name_and_index);
        normalized_eff_names = (uu___2247_79005.normalized_eff_names);
        fv_delta_depths = (uu___2247_79005.fv_delta_depths);
        proof_ns = (uu___2247_79005.proof_ns);
        synth_hook = (uu___2247_79005.synth_hook);
        splice = (uu___2247_79005.splice);
        postprocess = (uu___2247_79005.postprocess);
        is_native_tactic = (uu___2247_79005.is_native_tactic);
        identifier_info = (uu___2247_79005.identifier_info);
        tc_hooks = (uu___2247_79005.tc_hooks);
        dsenv = (uu___2247_79005.dsenv);
        nbe = (uu___2247_79005.nbe)
      }), uu____78999)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____79017 =
      let uu____79020 = FStar_Ident.id_of_text ""  in [uu____79020]  in
    FStar_Ident.lid_of_ids uu____79017  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____79027 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____79027
        then
          let uu____79032 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____79032 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___2255_79060 = env  in
       {
         solver = (uu___2255_79060.solver);
         range = (uu___2255_79060.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___2255_79060.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___2255_79060.expected_typ);
         sigtab = (uu___2255_79060.sigtab);
         attrtab = (uu___2255_79060.attrtab);
         is_pattern = (uu___2255_79060.is_pattern);
         instantiate_imp = (uu___2255_79060.instantiate_imp);
         effects = (uu___2255_79060.effects);
         generalize = (uu___2255_79060.generalize);
         letrecs = (uu___2255_79060.letrecs);
         top_level = (uu___2255_79060.top_level);
         check_uvars = (uu___2255_79060.check_uvars);
         use_eq = (uu___2255_79060.use_eq);
         is_iface = (uu___2255_79060.is_iface);
         admit = (uu___2255_79060.admit);
         lax = (uu___2255_79060.lax);
         lax_universes = (uu___2255_79060.lax_universes);
         phase1 = (uu___2255_79060.phase1);
         failhard = (uu___2255_79060.failhard);
         nosynth = (uu___2255_79060.nosynth);
         uvar_subtyping = (uu___2255_79060.uvar_subtyping);
         tc_term = (uu___2255_79060.tc_term);
         type_of = (uu___2255_79060.type_of);
         universe_of = (uu___2255_79060.universe_of);
         check_type_of = (uu___2255_79060.check_type_of);
         use_bv_sorts = (uu___2255_79060.use_bv_sorts);
         qtbl_name_and_index = (uu___2255_79060.qtbl_name_and_index);
         normalized_eff_names = (uu___2255_79060.normalized_eff_names);
         fv_delta_depths = (uu___2255_79060.fv_delta_depths);
         proof_ns = (uu___2255_79060.proof_ns);
         synth_hook = (uu___2255_79060.synth_hook);
         splice = (uu___2255_79060.splice);
         postprocess = (uu___2255_79060.postprocess);
         is_native_tactic = (uu___2255_79060.is_native_tactic);
         identifier_info = (uu___2255_79060.identifier_info);
         tc_hooks = (uu___2255_79060.tc_hooks);
         dsenv = (uu___2255_79060.dsenv);
         nbe = (uu___2255_79060.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79112)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79116,(uu____79117,t)))::tl1
          ->
          let uu____79138 =
            let uu____79141 = FStar_Syntax_Free.uvars t  in
            ext out uu____79141  in
          aux uu____79138 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79144;
            FStar_Syntax_Syntax.index = uu____79145;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79153 =
            let uu____79156 = FStar_Syntax_Free.uvars t  in
            ext out uu____79156  in
          aux uu____79153 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____79214)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79218,(uu____79219,t)))::tl1
          ->
          let uu____79240 =
            let uu____79243 = FStar_Syntax_Free.univs t  in
            ext out uu____79243  in
          aux uu____79240 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79246;
            FStar_Syntax_Syntax.index = uu____79247;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79255 =
            let uu____79258 = FStar_Syntax_Free.univs t  in
            ext out uu____79258  in
          aux uu____79255 tl1
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
          let uu____79320 = FStar_Util.set_add uname out  in
          aux uu____79320 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____79323,(uu____79324,t)))::tl1
          ->
          let uu____79345 =
            let uu____79348 = FStar_Syntax_Free.univnames t  in
            ext out uu____79348  in
          aux uu____79345 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____79351;
            FStar_Syntax_Syntax.index = uu____79352;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____79360 =
            let uu____79363 = FStar_Syntax_Free.univnames t  in
            ext out uu____79363  in
          aux uu____79360 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___457_79384  ->
            match uu___457_79384 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____79388 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____79401 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____79412 =
      let uu____79421 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____79421
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____79412 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____79469 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___458_79482  ->
              match uu___458_79482 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____79485 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____79485
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____79491) ->
                  let uu____79508 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____79508))
       in
    FStar_All.pipe_right uu____79469 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___459_79522  ->
    match uu___459_79522 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____79528 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____79528
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____79551  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____79606) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____79639,uu____79640) -> false  in
      let uu____79654 =
        FStar_List.tryFind
          (fun uu____79676  ->
             match uu____79676 with | (p,uu____79687) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____79654 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____79706,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____79736 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____79736
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___2398_79758 = e  in
        {
          solver = (uu___2398_79758.solver);
          range = (uu___2398_79758.range);
          curmodule = (uu___2398_79758.curmodule);
          gamma = (uu___2398_79758.gamma);
          gamma_sig = (uu___2398_79758.gamma_sig);
          gamma_cache = (uu___2398_79758.gamma_cache);
          modules = (uu___2398_79758.modules);
          expected_typ = (uu___2398_79758.expected_typ);
          sigtab = (uu___2398_79758.sigtab);
          attrtab = (uu___2398_79758.attrtab);
          is_pattern = (uu___2398_79758.is_pattern);
          instantiate_imp = (uu___2398_79758.instantiate_imp);
          effects = (uu___2398_79758.effects);
          generalize = (uu___2398_79758.generalize);
          letrecs = (uu___2398_79758.letrecs);
          top_level = (uu___2398_79758.top_level);
          check_uvars = (uu___2398_79758.check_uvars);
          use_eq = (uu___2398_79758.use_eq);
          is_iface = (uu___2398_79758.is_iface);
          admit = (uu___2398_79758.admit);
          lax = (uu___2398_79758.lax);
          lax_universes = (uu___2398_79758.lax_universes);
          phase1 = (uu___2398_79758.phase1);
          failhard = (uu___2398_79758.failhard);
          nosynth = (uu___2398_79758.nosynth);
          uvar_subtyping = (uu___2398_79758.uvar_subtyping);
          tc_term = (uu___2398_79758.tc_term);
          type_of = (uu___2398_79758.type_of);
          universe_of = (uu___2398_79758.universe_of);
          check_type_of = (uu___2398_79758.check_type_of);
          use_bv_sorts = (uu___2398_79758.use_bv_sorts);
          qtbl_name_and_index = (uu___2398_79758.qtbl_name_and_index);
          normalized_eff_names = (uu___2398_79758.normalized_eff_names);
          fv_delta_depths = (uu___2398_79758.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___2398_79758.synth_hook);
          splice = (uu___2398_79758.splice);
          postprocess = (uu___2398_79758.postprocess);
          is_native_tactic = (uu___2398_79758.is_native_tactic);
          identifier_info = (uu___2398_79758.identifier_info);
          tc_hooks = (uu___2398_79758.tc_hooks);
          dsenv = (uu___2398_79758.dsenv);
          nbe = (uu___2398_79758.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___2407_79806 = e  in
      {
        solver = (uu___2407_79806.solver);
        range = (uu___2407_79806.range);
        curmodule = (uu___2407_79806.curmodule);
        gamma = (uu___2407_79806.gamma);
        gamma_sig = (uu___2407_79806.gamma_sig);
        gamma_cache = (uu___2407_79806.gamma_cache);
        modules = (uu___2407_79806.modules);
        expected_typ = (uu___2407_79806.expected_typ);
        sigtab = (uu___2407_79806.sigtab);
        attrtab = (uu___2407_79806.attrtab);
        is_pattern = (uu___2407_79806.is_pattern);
        instantiate_imp = (uu___2407_79806.instantiate_imp);
        effects = (uu___2407_79806.effects);
        generalize = (uu___2407_79806.generalize);
        letrecs = (uu___2407_79806.letrecs);
        top_level = (uu___2407_79806.top_level);
        check_uvars = (uu___2407_79806.check_uvars);
        use_eq = (uu___2407_79806.use_eq);
        is_iface = (uu___2407_79806.is_iface);
        admit = (uu___2407_79806.admit);
        lax = (uu___2407_79806.lax);
        lax_universes = (uu___2407_79806.lax_universes);
        phase1 = (uu___2407_79806.phase1);
        failhard = (uu___2407_79806.failhard);
        nosynth = (uu___2407_79806.nosynth);
        uvar_subtyping = (uu___2407_79806.uvar_subtyping);
        tc_term = (uu___2407_79806.tc_term);
        type_of = (uu___2407_79806.type_of);
        universe_of = (uu___2407_79806.universe_of);
        check_type_of = (uu___2407_79806.check_type_of);
        use_bv_sorts = (uu___2407_79806.use_bv_sorts);
        qtbl_name_and_index = (uu___2407_79806.qtbl_name_and_index);
        normalized_eff_names = (uu___2407_79806.normalized_eff_names);
        fv_delta_depths = (uu___2407_79806.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___2407_79806.synth_hook);
        splice = (uu___2407_79806.splice);
        postprocess = (uu___2407_79806.postprocess);
        is_native_tactic = (uu___2407_79806.is_native_tactic);
        identifier_info = (uu___2407_79806.identifier_info);
        tc_hooks = (uu___2407_79806.tc_hooks);
        dsenv = (uu___2407_79806.dsenv);
        nbe = (uu___2407_79806.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____79822 = FStar_Syntax_Free.names t  in
      let uu____79825 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____79822 uu____79825
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____79848 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____79848
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____79858 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____79858
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____79879 =
      match uu____79879 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____79899 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____79899)
       in
    let uu____79907 =
      let uu____79911 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____79911 FStar_List.rev  in
    FStar_All.pipe_right uu____79907 (FStar_String.concat " ")
  
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
                  (let uu____79981 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____79981 with
                   | FStar_Pervasives_Native.Some uu____79985 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____79988 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____79998;
        univ_ineqs = uu____79999; implicits = uu____80000;_} -> true
    | uu____80012 -> false
  
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
          let uu___2451_80043 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2451_80043.deferred);
            univ_ineqs = (uu___2451_80043.univ_ineqs);
            implicits = (uu___2451_80043.implicits)
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
          let uu____80082 = FStar_Options.defensive ()  in
          if uu____80082
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____80088 =
              let uu____80090 =
                let uu____80092 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____80092  in
              Prims.op_Negation uu____80090  in
            (if uu____80088
             then
               let uu____80099 =
                 let uu____80105 =
                   let uu____80107 = FStar_Syntax_Print.term_to_string t  in
                   let uu____80109 =
                     let uu____80111 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____80111
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____80107 uu____80109
                    in
                 (FStar_Errors.Warning_Defensive, uu____80105)  in
               FStar_Errors.log_issue rng uu____80099
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
          let uu____80151 =
            let uu____80153 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80153  in
          if uu____80151
          then ()
          else
            (let uu____80158 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____80158 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____80184 =
            let uu____80186 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____80186  in
          if uu____80184
          then ()
          else
            (let uu____80191 = bound_vars e  in
             def_check_closed_in rng msg uu____80191 t)
  
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
          let uu___2488_80230 = g  in
          let uu____80231 =
            let uu____80232 =
              let uu____80233 =
                let uu____80240 =
                  let uu____80241 =
                    let uu____80258 =
                      let uu____80269 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____80269]  in
                    (f, uu____80258)  in
                  FStar_Syntax_Syntax.Tm_app uu____80241  in
                FStar_Syntax_Syntax.mk uu____80240  in
              uu____80233 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _80309  -> FStar_TypeChecker_Common.NonTrivial _80309)
              uu____80232
             in
          {
            guard_f = uu____80231;
            deferred = (uu___2488_80230.deferred);
            univ_ineqs = (uu___2488_80230.univ_ineqs);
            implicits = (uu___2488_80230.implicits)
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
          let uu___2495_80327 = g  in
          let uu____80328 =
            let uu____80329 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80329  in
          {
            guard_f = uu____80328;
            deferred = (uu___2495_80327.deferred);
            univ_ineqs = (uu___2495_80327.univ_ineqs);
            implicits = (uu___2495_80327.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2500_80346 = g  in
          let uu____80347 =
            let uu____80348 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____80348  in
          {
            guard_f = uu____80347;
            deferred = (uu___2500_80346.deferred);
            univ_ineqs = (uu___2500_80346.univ_ineqs);
            implicits = (uu___2500_80346.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2504_80350 = g  in
          let uu____80351 =
            let uu____80352 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____80352  in
          {
            guard_f = uu____80351;
            deferred = (uu___2504_80350.deferred);
            univ_ineqs = (uu___2504_80350.univ_ineqs);
            implicits = (uu___2504_80350.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____80359 ->
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
          let uu____80376 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____80376
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____80383 =
      let uu____80384 = FStar_Syntax_Util.unmeta t  in
      uu____80384.FStar_Syntax_Syntax.n  in
    match uu____80383 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____80388 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____80431 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____80431;
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
                       let uu____80526 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____80526
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2559_80533 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2559_80533.deferred);
              univ_ineqs = (uu___2559_80533.univ_ineqs);
              implicits = (uu___2559_80533.implicits)
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
               let uu____80567 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____80567
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
            let uu___2574_80594 = g  in
            let uu____80595 =
              let uu____80596 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____80596  in
            {
              guard_f = uu____80595;
              deferred = (uu___2574_80594.deferred);
              univ_ineqs = (uu___2574_80594.univ_ineqs);
              implicits = (uu___2574_80594.implicits)
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
              let uu____80654 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____80654 with
              | FStar_Pervasives_Native.Some
                  (uu____80679::(tm,uu____80681)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____80745 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____80763 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____80763;
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
                      let uu___2596_80795 = trivial_guard  in
                      {
                        guard_f = (uu___2596_80795.guard_f);
                        deferred = (uu___2596_80795.deferred);
                        univ_ineqs = (uu___2596_80795.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____80813  -> ());
    push = (fun uu____80815  -> ());
    pop = (fun uu____80818  -> ());
    snapshot =
      (fun uu____80821  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____80840  -> fun uu____80841  -> ());
    encode_sig = (fun uu____80856  -> fun uu____80857  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____80863 =
             let uu____80870 = FStar_Options.peek ()  in (e, g, uu____80870)
              in
           [uu____80863]);
    solve = (fun uu____80886  -> fun uu____80887  -> fun uu____80888  -> ());
    finish = (fun uu____80895  -> ());
    refresh = (fun uu____80897  -> ())
  } 