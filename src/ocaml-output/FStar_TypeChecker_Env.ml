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
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
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
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
    }
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> decls 
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> order 
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun projectee  -> match projectee with | { decls; order; joins;_} -> joins 
type name_prefix = Prims.string Prims.list
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
    ;
  use_bv_sorts: Prims.bool ;
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
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
  snapshot:
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2
    ;
  rollback:
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit
    ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
    ;
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
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
    ;
  implicits: implicit Prims.list }
and implicit =
  {
  imp_reason: Prims.string ;
  imp_uvar: FStar_Syntax_Syntax.ctx_uvar ;
  imp_tm: FStar_Syntax_Syntax.term ;
  imp_range: FStar_Range.range ;
  imp_meta:
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
    }
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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list)
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3)
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3)
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
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
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
  solver_t ->
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { init = init1; push = push1; pop = pop1; snapshot = snapshot1;
        rollback = rollback1; encode_modul; encode_sig; preprocess; solve;
        finish = finish1; refresh;_} -> snapshot1
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit)
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
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list)
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
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
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
    | { imp_reason; imp_uvar; imp_tm; imp_range; imp_meta;_} -> imp_reason
  
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range; imp_meta;_} -> imp_uvar
  
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range; imp_meta;_} -> imp_tm
  
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range; imp_meta;_} -> imp_range
  
let (__proj__Mkimplicit__item__imp_meta :
  implicit ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { imp_reason; imp_uvar; imp_tm; imp_range; imp_meta;_} -> imp_meta
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding,sig_binding) FStar_Util.either -> unit)
  =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook;_} -> tc_push_in_gamma_hook
  
type solver_depth_t =
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
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
           (fun uu___233_12055  ->
              match uu___233_12055 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____12058 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____12058  in
                  let uu____12059 =
                    let uu____12060 = FStar_Syntax_Subst.compress y  in
                    uu____12060.FStar_Syntax_Syntax.n  in
                  (match uu____12059 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____12064 =
                         let uu___247_12065 = y1  in
                         let uu____12066 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___247_12065.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___247_12065.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____12066
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____12064
                   | uu____12069 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___248_12083 = env  in
      let uu____12084 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___248_12083.solver);
        range = (uu___248_12083.range);
        curmodule = (uu___248_12083.curmodule);
        gamma = uu____12084;
        gamma_sig = (uu___248_12083.gamma_sig);
        gamma_cache = (uu___248_12083.gamma_cache);
        modules = (uu___248_12083.modules);
        expected_typ = (uu___248_12083.expected_typ);
        sigtab = (uu___248_12083.sigtab);
        attrtab = (uu___248_12083.attrtab);
        is_pattern = (uu___248_12083.is_pattern);
        instantiate_imp = (uu___248_12083.instantiate_imp);
        effects = (uu___248_12083.effects);
        generalize = (uu___248_12083.generalize);
        letrecs = (uu___248_12083.letrecs);
        top_level = (uu___248_12083.top_level);
        check_uvars = (uu___248_12083.check_uvars);
        use_eq = (uu___248_12083.use_eq);
        is_iface = (uu___248_12083.is_iface);
        admit = (uu___248_12083.admit);
        lax = (uu___248_12083.lax);
        lax_universes = (uu___248_12083.lax_universes);
        phase1 = (uu___248_12083.phase1);
        failhard = (uu___248_12083.failhard);
        nosynth = (uu___248_12083.nosynth);
        uvar_subtyping = (uu___248_12083.uvar_subtyping);
        tc_term = (uu___248_12083.tc_term);
        type_of = (uu___248_12083.type_of);
        universe_of = (uu___248_12083.universe_of);
        check_type_of = (uu___248_12083.check_type_of);
        use_bv_sorts = (uu___248_12083.use_bv_sorts);
        qtbl_name_and_index = (uu___248_12083.qtbl_name_and_index);
        normalized_eff_names = (uu___248_12083.normalized_eff_names);
        fv_delta_depths = (uu___248_12083.fv_delta_depths);
        proof_ns = (uu___248_12083.proof_ns);
        synth_hook = (uu___248_12083.synth_hook);
        splice = (uu___248_12083.splice);
        postprocess = (uu___248_12083.postprocess);
        is_native_tactic = (uu___248_12083.is_native_tactic);
        identifier_info = (uu___248_12083.identifier_info);
        tc_hooks = (uu___248_12083.tc_hooks);
        dsenv = (uu___248_12083.dsenv);
        nbe = (uu___248_12083.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____12092  -> fun uu____12093  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___249_12115 = env  in
      {
        solver = (uu___249_12115.solver);
        range = (uu___249_12115.range);
        curmodule = (uu___249_12115.curmodule);
        gamma = (uu___249_12115.gamma);
        gamma_sig = (uu___249_12115.gamma_sig);
        gamma_cache = (uu___249_12115.gamma_cache);
        modules = (uu___249_12115.modules);
        expected_typ = (uu___249_12115.expected_typ);
        sigtab = (uu___249_12115.sigtab);
        attrtab = (uu___249_12115.attrtab);
        is_pattern = (uu___249_12115.is_pattern);
        instantiate_imp = (uu___249_12115.instantiate_imp);
        effects = (uu___249_12115.effects);
        generalize = (uu___249_12115.generalize);
        letrecs = (uu___249_12115.letrecs);
        top_level = (uu___249_12115.top_level);
        check_uvars = (uu___249_12115.check_uvars);
        use_eq = (uu___249_12115.use_eq);
        is_iface = (uu___249_12115.is_iface);
        admit = (uu___249_12115.admit);
        lax = (uu___249_12115.lax);
        lax_universes = (uu___249_12115.lax_universes);
        phase1 = (uu___249_12115.phase1);
        failhard = (uu___249_12115.failhard);
        nosynth = (uu___249_12115.nosynth);
        uvar_subtyping = (uu___249_12115.uvar_subtyping);
        tc_term = (uu___249_12115.tc_term);
        type_of = (uu___249_12115.type_of);
        universe_of = (uu___249_12115.universe_of);
        check_type_of = (uu___249_12115.check_type_of);
        use_bv_sorts = (uu___249_12115.use_bv_sorts);
        qtbl_name_and_index = (uu___249_12115.qtbl_name_and_index);
        normalized_eff_names = (uu___249_12115.normalized_eff_names);
        fv_delta_depths = (uu___249_12115.fv_delta_depths);
        proof_ns = (uu___249_12115.proof_ns);
        synth_hook = (uu___249_12115.synth_hook);
        splice = (uu___249_12115.splice);
        postprocess = (uu___249_12115.postprocess);
        is_native_tactic = (uu___249_12115.is_native_tactic);
        identifier_info = (uu___249_12115.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___249_12115.dsenv);
        nbe = (uu___249_12115.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___250_12127 = e  in
      let uu____12128 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___250_12127.solver);
        range = (uu___250_12127.range);
        curmodule = (uu___250_12127.curmodule);
        gamma = (uu___250_12127.gamma);
        gamma_sig = (uu___250_12127.gamma_sig);
        gamma_cache = (uu___250_12127.gamma_cache);
        modules = (uu___250_12127.modules);
        expected_typ = (uu___250_12127.expected_typ);
        sigtab = (uu___250_12127.sigtab);
        attrtab = (uu___250_12127.attrtab);
        is_pattern = (uu___250_12127.is_pattern);
        instantiate_imp = (uu___250_12127.instantiate_imp);
        effects = (uu___250_12127.effects);
        generalize = (uu___250_12127.generalize);
        letrecs = (uu___250_12127.letrecs);
        top_level = (uu___250_12127.top_level);
        check_uvars = (uu___250_12127.check_uvars);
        use_eq = (uu___250_12127.use_eq);
        is_iface = (uu___250_12127.is_iface);
        admit = (uu___250_12127.admit);
        lax = (uu___250_12127.lax);
        lax_universes = (uu___250_12127.lax_universes);
        phase1 = (uu___250_12127.phase1);
        failhard = (uu___250_12127.failhard);
        nosynth = (uu___250_12127.nosynth);
        uvar_subtyping = (uu___250_12127.uvar_subtyping);
        tc_term = (uu___250_12127.tc_term);
        type_of = (uu___250_12127.type_of);
        universe_of = (uu___250_12127.universe_of);
        check_type_of = (uu___250_12127.check_type_of);
        use_bv_sorts = (uu___250_12127.use_bv_sorts);
        qtbl_name_and_index = (uu___250_12127.qtbl_name_and_index);
        normalized_eff_names = (uu___250_12127.normalized_eff_names);
        fv_delta_depths = (uu___250_12127.fv_delta_depths);
        proof_ns = (uu___250_12127.proof_ns);
        synth_hook = (uu___250_12127.synth_hook);
        splice = (uu___250_12127.splice);
        postprocess = (uu___250_12127.postprocess);
        is_native_tactic = (uu___250_12127.is_native_tactic);
        identifier_info = (uu___250_12127.identifier_info);
        tc_hooks = (uu___250_12127.tc_hooks);
        dsenv = uu____12128;
        nbe = (uu___250_12127.nbe)
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
      | (NoDelta ,uu____12157) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12160,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12162,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12165 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____12179 . unit -> 'Auu____12179 FStar_Util.smap =
  fun uu____12186  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12192 . unit -> 'Auu____12192 FStar_Util.smap =
  fun uu____12199  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
           FStar_Pervasives_Native.tuple3)
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
             FStar_Pervasives_Native.tuple3)
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
                  let uu____12337 = new_gamma_cache ()  in
                  let uu____12340 = new_sigtab ()  in
                  let uu____12343 = new_sigtab ()  in
                  let uu____12350 =
                    let uu____12365 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12365, FStar_Pervasives_Native.None)  in
                  let uu____12386 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12390 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12394 = FStar_Options.using_facts_from ()  in
                  let uu____12395 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12398 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12337;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12340;
                    attrtab = uu____12343;
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
                    qtbl_name_and_index = uu____12350;
                    normalized_eff_names = uu____12386;
                    fv_delta_depths = uu____12390;
                    proof_ns = uu____12394;
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
                    is_native_tactic = (fun uu____12460  -> false);
                    identifier_info = uu____12395;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12398;
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
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____12572  ->
    let uu____12573 = FStar_ST.op_Bang query_indices  in
    match uu____12573 with
    | [] -> failwith "Empty query indices!"
    | uu____12628 ->
        let uu____12638 =
          let uu____12648 =
            let uu____12656 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12656  in
          let uu____12710 = FStar_ST.op_Bang query_indices  in uu____12648 ::
            uu____12710
           in
        FStar_ST.op_Colon_Equals query_indices uu____12638
  
let (pop_query_indices : unit -> unit) =
  fun uu____12806  ->
    let uu____12807 = FStar_ST.op_Bang query_indices  in
    match uu____12807 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____12934  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____12971  ->
    match uu____12971 with
    | (l,n1) ->
        let uu____12981 = FStar_ST.op_Bang query_indices  in
        (match uu____12981 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____13103 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____13126  ->
    let uu____13127 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____13127
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13206 =
       let uu____13209 = FStar_ST.op_Bang stack  in env :: uu____13209  in
     FStar_ST.op_Colon_Equals stack uu____13206);
    (let uu___251_13258 = env  in
     let uu____13259 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13262 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13265 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13272 =
       let uu____13287 =
         let uu____13291 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13291  in
       let uu____13323 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13287, uu____13323)  in
     let uu____13372 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13375 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13378 =
       let uu____13381 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13381  in
     {
       solver = (uu___251_13258.solver);
       range = (uu___251_13258.range);
       curmodule = (uu___251_13258.curmodule);
       gamma = (uu___251_13258.gamma);
       gamma_sig = (uu___251_13258.gamma_sig);
       gamma_cache = uu____13259;
       modules = (uu___251_13258.modules);
       expected_typ = (uu___251_13258.expected_typ);
       sigtab = uu____13262;
       attrtab = uu____13265;
       is_pattern = (uu___251_13258.is_pattern);
       instantiate_imp = (uu___251_13258.instantiate_imp);
       effects = (uu___251_13258.effects);
       generalize = (uu___251_13258.generalize);
       letrecs = (uu___251_13258.letrecs);
       top_level = (uu___251_13258.top_level);
       check_uvars = (uu___251_13258.check_uvars);
       use_eq = (uu___251_13258.use_eq);
       is_iface = (uu___251_13258.is_iface);
       admit = (uu___251_13258.admit);
       lax = (uu___251_13258.lax);
       lax_universes = (uu___251_13258.lax_universes);
       phase1 = (uu___251_13258.phase1);
       failhard = (uu___251_13258.failhard);
       nosynth = (uu___251_13258.nosynth);
       uvar_subtyping = (uu___251_13258.uvar_subtyping);
       tc_term = (uu___251_13258.tc_term);
       type_of = (uu___251_13258.type_of);
       universe_of = (uu___251_13258.universe_of);
       check_type_of = (uu___251_13258.check_type_of);
       use_bv_sorts = (uu___251_13258.use_bv_sorts);
       qtbl_name_and_index = uu____13272;
       normalized_eff_names = uu____13372;
       fv_delta_depths = uu____13375;
       proof_ns = (uu___251_13258.proof_ns);
       synth_hook = (uu___251_13258.synth_hook);
       splice = (uu___251_13258.splice);
       postprocess = (uu___251_13258.postprocess);
       is_native_tactic = (uu___251_13258.is_native_tactic);
       identifier_info = uu____13378;
       tc_hooks = (uu___251_13258.tc_hooks);
       dsenv = (uu___251_13258.dsenv);
       nbe = (uu___251_13258.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13428  ->
    let uu____13429 = FStar_ST.op_Bang stack  in
    match uu____13429 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13483 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2)
  = fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t =
  (Prims.int,Prims.int,solver_depth_t,Prims.int)
    FStar_Pervasives_Native.tuple4
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t,env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13573  ->
           let uu____13574 = snapshot_stack env  in
           match uu____13574 with
           | (stack_depth,env1) ->
               let uu____13608 = snapshot_query_indices ()  in
               (match uu____13608 with
                | (query_indices_depth,()) ->
                    let uu____13641 = (env1.solver).snapshot msg  in
                    (match uu____13641 with
                     | (solver_depth,()) ->
                         let uu____13698 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13698 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___252_13765 = env1  in
                                 {
                                   solver = (uu___252_13765.solver);
                                   range = (uu___252_13765.range);
                                   curmodule = (uu___252_13765.curmodule);
                                   gamma = (uu___252_13765.gamma);
                                   gamma_sig = (uu___252_13765.gamma_sig);
                                   gamma_cache = (uu___252_13765.gamma_cache);
                                   modules = (uu___252_13765.modules);
                                   expected_typ =
                                     (uu___252_13765.expected_typ);
                                   sigtab = (uu___252_13765.sigtab);
                                   attrtab = (uu___252_13765.attrtab);
                                   is_pattern = (uu___252_13765.is_pattern);
                                   instantiate_imp =
                                     (uu___252_13765.instantiate_imp);
                                   effects = (uu___252_13765.effects);
                                   generalize = (uu___252_13765.generalize);
                                   letrecs = (uu___252_13765.letrecs);
                                   top_level = (uu___252_13765.top_level);
                                   check_uvars = (uu___252_13765.check_uvars);
                                   use_eq = (uu___252_13765.use_eq);
                                   is_iface = (uu___252_13765.is_iface);
                                   admit = (uu___252_13765.admit);
                                   lax = (uu___252_13765.lax);
                                   lax_universes =
                                     (uu___252_13765.lax_universes);
                                   phase1 = (uu___252_13765.phase1);
                                   failhard = (uu___252_13765.failhard);
                                   nosynth = (uu___252_13765.nosynth);
                                   uvar_subtyping =
                                     (uu___252_13765.uvar_subtyping);
                                   tc_term = (uu___252_13765.tc_term);
                                   type_of = (uu___252_13765.type_of);
                                   universe_of = (uu___252_13765.universe_of);
                                   check_type_of =
                                     (uu___252_13765.check_type_of);
                                   use_bv_sorts =
                                     (uu___252_13765.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___252_13765.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___252_13765.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___252_13765.fv_delta_depths);
                                   proof_ns = (uu___252_13765.proof_ns);
                                   synth_hook = (uu___252_13765.synth_hook);
                                   splice = (uu___252_13765.splice);
                                   postprocess = (uu___252_13765.postprocess);
                                   is_native_tactic =
                                     (uu___252_13765.is_native_tactic);
                                   identifier_info =
                                     (uu___252_13765.identifier_info);
                                   tc_hooks = (uu___252_13765.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___252_13765.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13799  ->
             let uu____13800 =
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
             match uu____13800 with
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
                             ((let uu____13980 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13980
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13996 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13996
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____14028,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____14070 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____14100  ->
                  match uu____14100 with
                  | (m,uu____14108) -> FStar_Ident.lid_equals l m))
           in
        (match uu____14070 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___253_14123 = env  in
               {
                 solver = (uu___253_14123.solver);
                 range = (uu___253_14123.range);
                 curmodule = (uu___253_14123.curmodule);
                 gamma = (uu___253_14123.gamma);
                 gamma_sig = (uu___253_14123.gamma_sig);
                 gamma_cache = (uu___253_14123.gamma_cache);
                 modules = (uu___253_14123.modules);
                 expected_typ = (uu___253_14123.expected_typ);
                 sigtab = (uu___253_14123.sigtab);
                 attrtab = (uu___253_14123.attrtab);
                 is_pattern = (uu___253_14123.is_pattern);
                 instantiate_imp = (uu___253_14123.instantiate_imp);
                 effects = (uu___253_14123.effects);
                 generalize = (uu___253_14123.generalize);
                 letrecs = (uu___253_14123.letrecs);
                 top_level = (uu___253_14123.top_level);
                 check_uvars = (uu___253_14123.check_uvars);
                 use_eq = (uu___253_14123.use_eq);
                 is_iface = (uu___253_14123.is_iface);
                 admit = (uu___253_14123.admit);
                 lax = (uu___253_14123.lax);
                 lax_universes = (uu___253_14123.lax_universes);
                 phase1 = (uu___253_14123.phase1);
                 failhard = (uu___253_14123.failhard);
                 nosynth = (uu___253_14123.nosynth);
                 uvar_subtyping = (uu___253_14123.uvar_subtyping);
                 tc_term = (uu___253_14123.tc_term);
                 type_of = (uu___253_14123.type_of);
                 universe_of = (uu___253_14123.universe_of);
                 check_type_of = (uu___253_14123.check_type_of);
                 use_bv_sorts = (uu___253_14123.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___253_14123.normalized_eff_names);
                 fv_delta_depths = (uu___253_14123.fv_delta_depths);
                 proof_ns = (uu___253_14123.proof_ns);
                 synth_hook = (uu___253_14123.synth_hook);
                 splice = (uu___253_14123.splice);
                 postprocess = (uu___253_14123.postprocess);
                 is_native_tactic = (uu___253_14123.is_native_tactic);
                 identifier_info = (uu___253_14123.identifier_info);
                 tc_hooks = (uu___253_14123.tc_hooks);
                 dsenv = (uu___253_14123.dsenv);
                 nbe = (uu___253_14123.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____14140,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___254_14156 = env  in
               {
                 solver = (uu___254_14156.solver);
                 range = (uu___254_14156.range);
                 curmodule = (uu___254_14156.curmodule);
                 gamma = (uu___254_14156.gamma);
                 gamma_sig = (uu___254_14156.gamma_sig);
                 gamma_cache = (uu___254_14156.gamma_cache);
                 modules = (uu___254_14156.modules);
                 expected_typ = (uu___254_14156.expected_typ);
                 sigtab = (uu___254_14156.sigtab);
                 attrtab = (uu___254_14156.attrtab);
                 is_pattern = (uu___254_14156.is_pattern);
                 instantiate_imp = (uu___254_14156.instantiate_imp);
                 effects = (uu___254_14156.effects);
                 generalize = (uu___254_14156.generalize);
                 letrecs = (uu___254_14156.letrecs);
                 top_level = (uu___254_14156.top_level);
                 check_uvars = (uu___254_14156.check_uvars);
                 use_eq = (uu___254_14156.use_eq);
                 is_iface = (uu___254_14156.is_iface);
                 admit = (uu___254_14156.admit);
                 lax = (uu___254_14156.lax);
                 lax_universes = (uu___254_14156.lax_universes);
                 phase1 = (uu___254_14156.phase1);
                 failhard = (uu___254_14156.failhard);
                 nosynth = (uu___254_14156.nosynth);
                 uvar_subtyping = (uu___254_14156.uvar_subtyping);
                 tc_term = (uu___254_14156.tc_term);
                 type_of = (uu___254_14156.type_of);
                 universe_of = (uu___254_14156.universe_of);
                 check_type_of = (uu___254_14156.check_type_of);
                 use_bv_sorts = (uu___254_14156.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___254_14156.normalized_eff_names);
                 fv_delta_depths = (uu___254_14156.fv_delta_depths);
                 proof_ns = (uu___254_14156.proof_ns);
                 synth_hook = (uu___254_14156.synth_hook);
                 splice = (uu___254_14156.splice);
                 postprocess = (uu___254_14156.postprocess);
                 is_native_tactic = (uu___254_14156.is_native_tactic);
                 identifier_info = (uu___254_14156.identifier_info);
                 tc_hooks = (uu___254_14156.tc_hooks);
                 dsenv = (uu___254_14156.dsenv);
                 nbe = (uu___254_14156.nbe)
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
        (let uu___255_14199 = e  in
         {
           solver = (uu___255_14199.solver);
           range = r;
           curmodule = (uu___255_14199.curmodule);
           gamma = (uu___255_14199.gamma);
           gamma_sig = (uu___255_14199.gamma_sig);
           gamma_cache = (uu___255_14199.gamma_cache);
           modules = (uu___255_14199.modules);
           expected_typ = (uu___255_14199.expected_typ);
           sigtab = (uu___255_14199.sigtab);
           attrtab = (uu___255_14199.attrtab);
           is_pattern = (uu___255_14199.is_pattern);
           instantiate_imp = (uu___255_14199.instantiate_imp);
           effects = (uu___255_14199.effects);
           generalize = (uu___255_14199.generalize);
           letrecs = (uu___255_14199.letrecs);
           top_level = (uu___255_14199.top_level);
           check_uvars = (uu___255_14199.check_uvars);
           use_eq = (uu___255_14199.use_eq);
           is_iface = (uu___255_14199.is_iface);
           admit = (uu___255_14199.admit);
           lax = (uu___255_14199.lax);
           lax_universes = (uu___255_14199.lax_universes);
           phase1 = (uu___255_14199.phase1);
           failhard = (uu___255_14199.failhard);
           nosynth = (uu___255_14199.nosynth);
           uvar_subtyping = (uu___255_14199.uvar_subtyping);
           tc_term = (uu___255_14199.tc_term);
           type_of = (uu___255_14199.type_of);
           universe_of = (uu___255_14199.universe_of);
           check_type_of = (uu___255_14199.check_type_of);
           use_bv_sorts = (uu___255_14199.use_bv_sorts);
           qtbl_name_and_index = (uu___255_14199.qtbl_name_and_index);
           normalized_eff_names = (uu___255_14199.normalized_eff_names);
           fv_delta_depths = (uu___255_14199.fv_delta_depths);
           proof_ns = (uu___255_14199.proof_ns);
           synth_hook = (uu___255_14199.synth_hook);
           splice = (uu___255_14199.splice);
           postprocess = (uu___255_14199.postprocess);
           is_native_tactic = (uu___255_14199.is_native_tactic);
           identifier_info = (uu___255_14199.identifier_info);
           tc_hooks = (uu___255_14199.tc_hooks);
           dsenv = (uu___255_14199.dsenv);
           nbe = (uu___255_14199.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____14219 =
        let uu____14220 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____14220 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14219
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14275 =
          let uu____14276 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14276 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14275
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14331 =
          let uu____14332 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14332 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14331
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14387 =
        let uu____14388 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14388 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14387
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___256_14452 = env  in
      {
        solver = (uu___256_14452.solver);
        range = (uu___256_14452.range);
        curmodule = lid;
        gamma = (uu___256_14452.gamma);
        gamma_sig = (uu___256_14452.gamma_sig);
        gamma_cache = (uu___256_14452.gamma_cache);
        modules = (uu___256_14452.modules);
        expected_typ = (uu___256_14452.expected_typ);
        sigtab = (uu___256_14452.sigtab);
        attrtab = (uu___256_14452.attrtab);
        is_pattern = (uu___256_14452.is_pattern);
        instantiate_imp = (uu___256_14452.instantiate_imp);
        effects = (uu___256_14452.effects);
        generalize = (uu___256_14452.generalize);
        letrecs = (uu___256_14452.letrecs);
        top_level = (uu___256_14452.top_level);
        check_uvars = (uu___256_14452.check_uvars);
        use_eq = (uu___256_14452.use_eq);
        is_iface = (uu___256_14452.is_iface);
        admit = (uu___256_14452.admit);
        lax = (uu___256_14452.lax);
        lax_universes = (uu___256_14452.lax_universes);
        phase1 = (uu___256_14452.phase1);
        failhard = (uu___256_14452.failhard);
        nosynth = (uu___256_14452.nosynth);
        uvar_subtyping = (uu___256_14452.uvar_subtyping);
        tc_term = (uu___256_14452.tc_term);
        type_of = (uu___256_14452.type_of);
        universe_of = (uu___256_14452.universe_of);
        check_type_of = (uu___256_14452.check_type_of);
        use_bv_sorts = (uu___256_14452.use_bv_sorts);
        qtbl_name_and_index = (uu___256_14452.qtbl_name_and_index);
        normalized_eff_names = (uu___256_14452.normalized_eff_names);
        fv_delta_depths = (uu___256_14452.fv_delta_depths);
        proof_ns = (uu___256_14452.proof_ns);
        synth_hook = (uu___256_14452.synth_hook);
        splice = (uu___256_14452.splice);
        postprocess = (uu___256_14452.postprocess);
        is_native_tactic = (uu___256_14452.is_native_tactic);
        identifier_info = (uu___256_14452.identifier_info);
        tc_hooks = (uu___256_14452.tc_hooks);
        dsenv = (uu___256_14452.dsenv);
        nbe = (uu___256_14452.nbe)
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
      let uu____14483 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14483
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____14496 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14496)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____14511 =
      let uu____14513 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14513  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14511)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14522  ->
    let uu____14523 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14523
  
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
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____14623) ->
          let vs = mk_univ_subst formals us  in
          let uu____14647 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14647)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___234_14664  ->
    match uu___234_14664 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14690  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun t  ->
      let uu____14710 = inst_tscheme t  in
      match uu____14710 with
      | (us,t1) ->
          let uu____14721 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14721)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14742  ->
          match uu____14742 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____14764 =
                         let uu____14766 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____14770 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____14774 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____14776 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____14766 uu____14770 uu____14774 uu____14776
                          in
                       failwith uu____14764)
                    else ();
                    (let uu____14781 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____14781))
               | uu____14790 ->
                   let uu____14791 =
                     let uu____14793 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____14793
                      in
                   failwith uu____14791)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14805 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14816 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14827 -> false
  
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
             | ([],uu____14875) -> Maybe
             | (uu____14882,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14902 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
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
          let uu____14996 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14996 with
          | FStar_Pervasives_Native.None  ->
              let uu____15019 =
                FStar_Util.find_map env.gamma
                  (fun uu___235_15063  ->
                     match uu___235_15063 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____15102 = FStar_Ident.lid_equals lid l  in
                         if uu____15102
                         then
                           let uu____15125 =
                             let uu____15144 =
                               let uu____15159 = inst_tscheme t  in
                               FStar_Util.Inl uu____15159  in
                             let uu____15174 = FStar_Ident.range_of_lid l  in
                             (uu____15144, uu____15174)  in
                           FStar_Pervasives_Native.Some uu____15125
                         else FStar_Pervasives_Native.None
                     | uu____15227 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____15019
                (fun uu____15265  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___236_15274  ->
                        match uu___236_15274 with
                        | (uu____15277,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15279);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15280;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15281;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15282;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15283;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15303 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15303
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
                                  uu____15355 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15362 -> cache t  in
                            let uu____15363 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15363 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15369 =
                                   let uu____15370 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15370)
                                    in
                                 maybe_cache uu____15369)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15441 = find_in_sigtab env lid  in
         match uu____15441 with
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
      let uu____15522 = lookup_qname env lid  in
      match uu____15522 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15543,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15657 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15657 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15702 =
          let uu____15705 = lookup_attr env1 attr  in se1 :: uu____15705  in
        FStar_Util.smap_add (attrtab env1) attr uu____15702  in
      FStar_List.iter
        (fun attr  ->
           let uu____15715 =
             let uu____15716 = FStar_Syntax_Subst.compress attr  in
             uu____15716.FStar_Syntax_Syntax.n  in
           match uu____15715 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15720 =
                 let uu____15722 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15722.FStar_Ident.str  in
               add_one1 env se uu____15720
           | uu____15723 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15746) ->
          add_sigelts env ses
      | uu____15755 ->
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
            | uu____15770 -> ()))

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___237_15802  ->
           match uu___237_15802 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15820 -> FStar_Pervasives_Native.None)
  
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____15882,lb::[]),uu____15884) ->
            let uu____15893 =
              let uu____15902 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15911 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15902, uu____15911)  in
            FStar_Pervasives_Native.Some uu____15893
        | FStar_Syntax_Syntax.Sig_let ((uu____15924,lbs),uu____15926) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15958 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15971 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15971
                     then
                       let uu____15984 =
                         let uu____15993 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____16002 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15993, uu____16002)  in
                       FStar_Pervasives_Native.Some uu____15984
                     else FStar_Pervasives_Native.None)
        | uu____16025 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____16085 =
            let uu____16094 =
              let uu____16099 =
                let uu____16100 =
                  let uu____16103 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____16103
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____16100)  in
              inst_tscheme1 uu____16099  in
            (uu____16094, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16085
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____16125,uu____16126) ->
          let uu____16131 =
            let uu____16140 =
              let uu____16145 =
                let uu____16146 =
                  let uu____16149 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____16149  in
                (us, uu____16146)  in
              inst_tscheme1 uu____16145  in
            (uu____16140, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____16131
      | uu____16168 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                          FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____16257 =
          match uu____16257 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16353,uvs,t,uu____16356,uu____16357,uu____16358);
                      FStar_Syntax_Syntax.sigrng = uu____16359;
                      FStar_Syntax_Syntax.sigquals = uu____16360;
                      FStar_Syntax_Syntax.sigmeta = uu____16361;
                      FStar_Syntax_Syntax.sigattrs = uu____16362;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16385 =
                     let uu____16394 = inst_tscheme1 (uvs, t)  in
                     (uu____16394, rng)  in
                   FStar_Pervasives_Native.Some uu____16385
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16418;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16420;
                      FStar_Syntax_Syntax.sigattrs = uu____16421;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16438 =
                     let uu____16440 = in_cur_mod env l  in uu____16440 = Yes
                      in
                   if uu____16438
                   then
                     let uu____16452 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16452
                      then
                        let uu____16468 =
                          let uu____16477 = inst_tscheme1 (uvs, t)  in
                          (uu____16477, rng)  in
                        FStar_Pervasives_Native.Some uu____16468
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16510 =
                        let uu____16519 = inst_tscheme1 (uvs, t)  in
                        (uu____16519, rng)  in
                      FStar_Pervasives_Native.Some uu____16510)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16544,uu____16545);
                      FStar_Syntax_Syntax.sigrng = uu____16546;
                      FStar_Syntax_Syntax.sigquals = uu____16547;
                      FStar_Syntax_Syntax.sigmeta = uu____16548;
                      FStar_Syntax_Syntax.sigattrs = uu____16549;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16590 =
                          let uu____16599 = inst_tscheme1 (uvs, k)  in
                          (uu____16599, rng)  in
                        FStar_Pervasives_Native.Some uu____16590
                    | uu____16620 ->
                        let uu____16621 =
                          let uu____16630 =
                            let uu____16635 =
                              let uu____16636 =
                                let uu____16639 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16639
                                 in
                              (uvs, uu____16636)  in
                            inst_tscheme1 uu____16635  in
                          (uu____16630, rng)  in
                        FStar_Pervasives_Native.Some uu____16621)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16662,uu____16663);
                      FStar_Syntax_Syntax.sigrng = uu____16664;
                      FStar_Syntax_Syntax.sigquals = uu____16665;
                      FStar_Syntax_Syntax.sigmeta = uu____16666;
                      FStar_Syntax_Syntax.sigattrs = uu____16667;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16709 =
                          let uu____16718 = inst_tscheme_with (uvs, k) us  in
                          (uu____16718, rng)  in
                        FStar_Pervasives_Native.Some uu____16709
                    | uu____16739 ->
                        let uu____16740 =
                          let uu____16749 =
                            let uu____16754 =
                              let uu____16755 =
                                let uu____16758 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16758
                                 in
                              (uvs, uu____16755)  in
                            inst_tscheme_with uu____16754 us  in
                          (uu____16749, rng)  in
                        FStar_Pervasives_Native.Some uu____16740)
               | FStar_Util.Inr se ->
                   let uu____16794 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16815;
                          FStar_Syntax_Syntax.sigrng = uu____16816;
                          FStar_Syntax_Syntax.sigquals = uu____16817;
                          FStar_Syntax_Syntax.sigmeta = uu____16818;
                          FStar_Syntax_Syntax.sigattrs = uu____16819;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16834 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____16794
                     (FStar_Util.map_option
                        (fun uu____16882  ->
                           match uu____16882 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16913 =
          let uu____16924 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16924 mapper  in
        match uu____16913 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____16998 =
              let uu____17009 =
                let uu____17016 =
                  let uu___257_17019 = t  in
                  let uu____17020 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___257_17019.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____17020;
                    FStar_Syntax_Syntax.vars =
                      (uu___257_17019.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____17016)  in
              (uu____17009, r)  in
            FStar_Pervasives_Native.Some uu____16998
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____17069 = lookup_qname env l  in
      match uu____17069 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____17090 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____17144 = try_lookup_bv env bv  in
      match uu____17144 with
      | FStar_Pervasives_Native.None  ->
          let uu____17159 = variable_not_found bv  in
          FStar_Errors.raise_error uu____17159 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____17175 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____17176 =
            let uu____17177 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____17177  in
          (uu____17175, uu____17176)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____17199 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____17199 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17265 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17265  in
          let uu____17266 =
            let uu____17275 =
              let uu____17280 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17280)  in
            (uu____17275, r1)  in
          FStar_Pervasives_Native.Some uu____17266
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____17315 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17315 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17348,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17373 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17373  in
            let uu____17374 =
              let uu____17379 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17379, r1)  in
            FStar_Pervasives_Native.Some uu____17374
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____17403 = try_lookup_lid env l  in
      match uu____17403 with
      | FStar_Pervasives_Native.None  ->
          let uu____17430 = name_not_found l  in
          let uu____17436 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17430 uu____17436
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___238_17479  ->
              match uu___238_17479 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17483 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17504 = lookup_qname env lid  in
      match uu____17504 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17513,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17516;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17518;
              FStar_Syntax_Syntax.sigattrs = uu____17519;_},FStar_Pervasives_Native.None
            ),uu____17520)
          ->
          let uu____17569 =
            let uu____17576 =
              let uu____17577 =
                let uu____17580 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17580 t  in
              (uvs, uu____17577)  in
            (uu____17576, q)  in
          FStar_Pervasives_Native.Some uu____17569
      | uu____17593 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____17615 = lookup_qname env lid  in
      match uu____17615 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17620,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17623;
              FStar_Syntax_Syntax.sigquals = uu____17624;
              FStar_Syntax_Syntax.sigmeta = uu____17625;
              FStar_Syntax_Syntax.sigattrs = uu____17626;_},FStar_Pervasives_Native.None
            ),uu____17627)
          ->
          let uu____17676 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17676 (uvs, t)
      | uu____17681 ->
          let uu____17682 = name_not_found lid  in
          let uu____17688 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17682 uu____17688
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____17708 = lookup_qname env lid  in
      match uu____17708 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17713,uvs,t,uu____17716,uu____17717,uu____17718);
              FStar_Syntax_Syntax.sigrng = uu____17719;
              FStar_Syntax_Syntax.sigquals = uu____17720;
              FStar_Syntax_Syntax.sigmeta = uu____17721;
              FStar_Syntax_Syntax.sigattrs = uu____17722;_},FStar_Pervasives_Native.None
            ),uu____17723)
          ->
          let uu____17778 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17778 (uvs, t)
      | uu____17783 ->
          let uu____17784 = name_not_found lid  in
          let uu____17790 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17784 uu____17790
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____17813 = lookup_qname env lid  in
      match uu____17813 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17821,uu____17822,uu____17823,uu____17824,uu____17825,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17827;
              FStar_Syntax_Syntax.sigquals = uu____17828;
              FStar_Syntax_Syntax.sigmeta = uu____17829;
              FStar_Syntax_Syntax.sigattrs = uu____17830;_},uu____17831),uu____17832)
          -> (true, dcs)
      | uu____17895 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17911 = lookup_qname env lid  in
      match uu____17911 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17912,uu____17913,uu____17914,l,uu____17916,uu____17917);
              FStar_Syntax_Syntax.sigrng = uu____17918;
              FStar_Syntax_Syntax.sigquals = uu____17919;
              FStar_Syntax_Syntax.sigmeta = uu____17920;
              FStar_Syntax_Syntax.sigattrs = uu____17921;_},uu____17922),uu____17923)
          -> l
      | uu____17980 ->
          let uu____17981 =
            let uu____17983 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____17983  in
          failwith uu____17981
  
let (lookup_definition_qninfo_aux :
  Prims.bool ->
    delta_level Prims.list ->
      FStar_Ident.lident ->
        qninfo ->
          (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                      FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18053)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____18110) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____18134 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____18134
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____18169 -> FStar_Pervasives_Native.None)
          | uu____18178 -> FStar_Pervasives_Native.None
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        lookup_definition_qninfo_aux true delta_levels lid qninfo
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____18240 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18240
  
let (lookup_nonrec_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____18273 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18273
  
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
             (FStar_Util.Inl uu____18325,uu____18326) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18375),uu____18376) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18425 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18443 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18453 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18470 ->
                  let uu____18477 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18477
              | FStar_Syntax_Syntax.Sig_let ((uu____18478,lbs),uu____18480)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18496 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18496
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18503 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18511 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18512 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18519 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18520 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18521 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18522 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18535 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18553 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18553
           (fun d_opt  ->
              let uu____18566 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18566
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18576 =
                   let uu____18579 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18579  in
                 match uu____18576 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18580 =
                       let uu____18582 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18582
                        in
                     failwith uu____18580
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18587 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18587
                       then
                         let uu____18590 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18592 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18594 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18590 uu____18592 uu____18594
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
        (FStar_Util.Inr (se,uu____18619),uu____18620) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18669 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18691),uu____18692) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18741 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18763 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18763
  
let (fv_has_attr :
  env -> FStar_Syntax_Syntax.fv -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv  ->
      fun attr_lid  ->
        let uu____18786 =
          lookup_attrs_of_lid env
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____18786 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18810 =
                      let uu____18811 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18811.FStar_Syntax_Syntax.n  in
                    match uu____18810 with
                    | FStar_Syntax_Syntax.Tm_fvar fv1 ->
                        FStar_Syntax_Syntax.fv_eq_lid fv1 attr_lid
                    | uu____18816 -> false))
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____18833 = lookup_qname env ftv  in
      match uu____18833 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18837) ->
          let uu____18882 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____18882 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____18903,t),r) ->
               let uu____18918 =
                 let uu____18919 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____18919 t  in
               FStar_Pervasives_Native.Some uu____18918)
      | uu____18920 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____18932 = try_lookup_effect_lid env ftv  in
      match uu____18932 with
      | FStar_Pervasives_Native.None  ->
          let uu____18935 = name_not_found ftv  in
          let uu____18941 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____18935 uu____18941
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____18965 = lookup_qname env lid0  in
        match uu____18965 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____18976);
                FStar_Syntax_Syntax.sigrng = uu____18977;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____18979;
                FStar_Syntax_Syntax.sigattrs = uu____18980;_},FStar_Pervasives_Native.None
              ),uu____18981)
            ->
            let lid1 =
              let uu____19035 =
                let uu____19036 = FStar_Ident.range_of_lid lid  in
                let uu____19037 =
                  let uu____19038 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____19038  in
                FStar_Range.set_use_range uu____19036 uu____19037  in
              FStar_Ident.set_lid_range lid uu____19035  in
            let uu____19039 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___239_19045  ->
                      match uu___239_19045 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____19048 -> false))
               in
            if uu____19039
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____19067 =
                      let uu____19069 =
                        let uu____19071 = get_range env  in
                        FStar_Range.string_of_range uu____19071  in
                      let uu____19072 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____19074 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____19069 uu____19072 uu____19074
                       in
                    failwith uu____19067)
                  in
               match (binders, univs1) with
               | ([],uu____19095) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____19121,uu____19122::uu____19123::uu____19124) ->
                   let uu____19145 =
                     let uu____19147 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____19149 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____19147 uu____19149
                      in
                   failwith uu____19145
               | uu____19160 ->
                   let uu____19175 =
                     let uu____19180 =
                       let uu____19181 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____19181)  in
                     inst_tscheme_with uu____19180 insts  in
                   (match uu____19175 with
                    | (uu____19194,t) ->
                        let t1 =
                          let uu____19197 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____19197 t  in
                        let uu____19198 =
                          let uu____19199 = FStar_Syntax_Subst.compress t1
                             in
                          uu____19199.FStar_Syntax_Syntax.n  in
                        (match uu____19198 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19234 -> failwith "Impossible")))
        | uu____19242 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19266 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19266 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19279,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19286 = find1 l2  in
            (match uu____19286 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19293 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19293 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19297 = find1 l  in
            (match uu____19297 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19302 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19302
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19317 = lookup_qname env l1  in
      match uu____19317 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19320;
              FStar_Syntax_Syntax.sigrng = uu____19321;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19323;
              FStar_Syntax_Syntax.sigattrs = uu____19324;_},uu____19325),uu____19326)
          -> q
      | uu____19377 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19401 =
          let uu____19402 =
            let uu____19404 = FStar_Util.string_of_int i  in
            let uu____19406 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19404 uu____19406
             in
          failwith uu____19402  in
        let uu____19409 = lookup_datacon env lid  in
        match uu____19409 with
        | (uu____19414,t) ->
            let uu____19416 =
              let uu____19417 = FStar_Syntax_Subst.compress t  in
              uu____19417.FStar_Syntax_Syntax.n  in
            (match uu____19416 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19421) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19465 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19465
                      FStar_Pervasives_Native.fst)
             | uu____19476 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19490 = lookup_qname env l  in
      match uu____19490 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19492,uu____19493,uu____19494);
              FStar_Syntax_Syntax.sigrng = uu____19495;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19497;
              FStar_Syntax_Syntax.sigattrs = uu____19498;_},uu____19499),uu____19500)
          ->
          FStar_Util.for_some
            (fun uu___240_19553  ->
               match uu___240_19553 with
               | FStar_Syntax_Syntax.Projector uu____19555 -> true
               | uu____19561 -> false) quals
      | uu____19563 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19577 = lookup_qname env lid  in
      match uu____19577 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19579,uu____19580,uu____19581,uu____19582,uu____19583,uu____19584);
              FStar_Syntax_Syntax.sigrng = uu____19585;
              FStar_Syntax_Syntax.sigquals = uu____19586;
              FStar_Syntax_Syntax.sigmeta = uu____19587;
              FStar_Syntax_Syntax.sigattrs = uu____19588;_},uu____19589),uu____19590)
          -> true
      | uu____19648 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19662 = lookup_qname env lid  in
      match uu____19662 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19664,uu____19665,uu____19666,uu____19667,uu____19668,uu____19669);
              FStar_Syntax_Syntax.sigrng = uu____19670;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19672;
              FStar_Syntax_Syntax.sigattrs = uu____19673;_},uu____19674),uu____19675)
          ->
          FStar_Util.for_some
            (fun uu___241_19736  ->
               match uu___241_19736 with
               | FStar_Syntax_Syntax.RecordType uu____19738 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19748 -> true
               | uu____19758 -> false) quals
      | uu____19760 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19770,uu____19771);
            FStar_Syntax_Syntax.sigrng = uu____19772;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19774;
            FStar_Syntax_Syntax.sigattrs = uu____19775;_},uu____19776),uu____19777)
        ->
        FStar_Util.for_some
          (fun uu___242_19834  ->
             match uu___242_19834 with
             | FStar_Syntax_Syntax.Action uu____19836 -> true
             | uu____19838 -> false) quals
    | uu____19840 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19854 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____19854
  
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
      let uu____19871 =
        let uu____19872 = FStar_Syntax_Util.un_uinst head1  in
        uu____19872.FStar_Syntax_Syntax.n  in
      match uu____19871 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____19878 ->
               true
           | uu____19881 -> false)
      | uu____19883 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19897 = lookup_qname env l  in
      match uu____19897 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____19900),uu____19901) ->
          FStar_Util.for_some
            (fun uu___243_19949  ->
               match uu___243_19949 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____19952 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____19954 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____20030 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____20048) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____20066 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____20074 ->
                 FStar_Pervasives_Native.Some true
             | uu____20093 -> FStar_Pervasives_Native.Some false)
         in
      let uu____20096 =
        let uu____20100 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____20100 mapper  in
      match uu____20096 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____20160 = lookup_qname env lid  in
      match uu____20160 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____20164,uu____20165,tps,uu____20167,uu____20168,uu____20169);
              FStar_Syntax_Syntax.sigrng = uu____20170;
              FStar_Syntax_Syntax.sigquals = uu____20171;
              FStar_Syntax_Syntax.sigmeta = uu____20172;
              FStar_Syntax_Syntax.sigattrs = uu____20173;_},uu____20174),uu____20175)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20241 -> FStar_Pervasives_Native.None
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____20287  ->
              match uu____20287 with
              | (d,uu____20296) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20312 = effect_decl_opt env l  in
      match uu____20312 with
      | FStar_Pervasives_Native.None  ->
          let uu____20327 = name_not_found l  in
          let uu____20333 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20327 uu____20333
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20356  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20375  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20407 = FStar_Ident.lid_equals l1 l2  in
        if uu____20407
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20418 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20418
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20429 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20482  ->
                        match uu____20482 with
                        | (m1,m2,uu____20496,uu____20497,uu____20498) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20429 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20515 =
                    let uu____20521 =
                      let uu____20523 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20525 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20523
                        uu____20525
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20521)
                     in
                  FStar_Errors.raise_error uu____20515 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20535,uu____20536,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20570 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20570
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
  'Auu____20590 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____20590)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____20619 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20645  ->
                match uu____20645 with
                | (d,uu____20652) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20619 with
      | FStar_Pervasives_Native.None  ->
          let uu____20663 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20663
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20678 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____20678 with
           | (uu____20693,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20711)::(wp,uu____20713)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20769 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
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
          let uu____20827 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____20827
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____20832 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____20832
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
                  let uu____20843 = get_range env  in
                  let uu____20844 =
                    let uu____20851 =
                      let uu____20852 =
                        let uu____20869 =
                          let uu____20880 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____20880]  in
                        (null_wp, uu____20869)  in
                      FStar_Syntax_Syntax.Tm_app uu____20852  in
                    FStar_Syntax_Syntax.mk uu____20851  in
                  uu____20844 FStar_Pervasives_Native.None uu____20843  in
                let uu____20920 =
                  let uu____20921 =
                    let uu____20932 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____20932]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____20921;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____20920))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___258_20970 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___258_20970.order);
              joins = (uu___258_20970.joins)
            }  in
          let uu___259_20979 = env  in
          {
            solver = (uu___259_20979.solver);
            range = (uu___259_20979.range);
            curmodule = (uu___259_20979.curmodule);
            gamma = (uu___259_20979.gamma);
            gamma_sig = (uu___259_20979.gamma_sig);
            gamma_cache = (uu___259_20979.gamma_cache);
            modules = (uu___259_20979.modules);
            expected_typ = (uu___259_20979.expected_typ);
            sigtab = (uu___259_20979.sigtab);
            attrtab = (uu___259_20979.attrtab);
            is_pattern = (uu___259_20979.is_pattern);
            instantiate_imp = (uu___259_20979.instantiate_imp);
            effects;
            generalize = (uu___259_20979.generalize);
            letrecs = (uu___259_20979.letrecs);
            top_level = (uu___259_20979.top_level);
            check_uvars = (uu___259_20979.check_uvars);
            use_eq = (uu___259_20979.use_eq);
            is_iface = (uu___259_20979.is_iface);
            admit = (uu___259_20979.admit);
            lax = (uu___259_20979.lax);
            lax_universes = (uu___259_20979.lax_universes);
            phase1 = (uu___259_20979.phase1);
            failhard = (uu___259_20979.failhard);
            nosynth = (uu___259_20979.nosynth);
            uvar_subtyping = (uu___259_20979.uvar_subtyping);
            tc_term = (uu___259_20979.tc_term);
            type_of = (uu___259_20979.type_of);
            universe_of = (uu___259_20979.universe_of);
            check_type_of = (uu___259_20979.check_type_of);
            use_bv_sorts = (uu___259_20979.use_bv_sorts);
            qtbl_name_and_index = (uu___259_20979.qtbl_name_and_index);
            normalized_eff_names = (uu___259_20979.normalized_eff_names);
            fv_delta_depths = (uu___259_20979.fv_delta_depths);
            proof_ns = (uu___259_20979.proof_ns);
            synth_hook = (uu___259_20979.synth_hook);
            splice = (uu___259_20979.splice);
            postprocess = (uu___259_20979.postprocess);
            is_native_tactic = (uu___259_20979.is_native_tactic);
            identifier_info = (uu___259_20979.identifier_info);
            tc_hooks = (uu___259_20979.tc_hooks);
            dsenv = (uu___259_20979.dsenv);
            nbe = (uu___259_20979.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____21009 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____21009  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____21167 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____21168 = l1 u t wp e  in
                                l2 u t uu____21167 uu____21168))
                | uu____21169 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21241 = inst_tscheme_with lift_t [u]  in
            match uu____21241 with
            | (uu____21248,lift_t1) ->
                let uu____21250 =
                  let uu____21257 =
                    let uu____21258 =
                      let uu____21275 =
                        let uu____21286 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21295 =
                          let uu____21306 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21306]  in
                        uu____21286 :: uu____21295  in
                      (lift_t1, uu____21275)  in
                    FStar_Syntax_Syntax.Tm_app uu____21258  in
                  FStar_Syntax_Syntax.mk uu____21257  in
                uu____21250 FStar_Pervasives_Native.None
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
            let uu____21419 = inst_tscheme_with lift_t [u]  in
            match uu____21419 with
            | (uu____21426,lift_t1) ->
                let uu____21428 =
                  let uu____21435 =
                    let uu____21436 =
                      let uu____21453 =
                        let uu____21464 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21473 =
                          let uu____21484 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21493 =
                            let uu____21504 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21504]  in
                          uu____21484 :: uu____21493  in
                        uu____21464 :: uu____21473  in
                      (lift_t1, uu____21453)  in
                    FStar_Syntax_Syntax.Tm_app uu____21436  in
                  FStar_Syntax_Syntax.mk uu____21435  in
                uu____21428 FStar_Pervasives_Native.None
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
              let uu____21609 =
                let uu____21610 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21610
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21609  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21619 =
              let uu____21621 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21621  in
            let uu____21622 =
              let uu____21624 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21652 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21652)
                 in
              FStar_Util.dflt "none" uu____21624  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21619
              uu____21622
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21681  ->
                    match uu____21681 with
                    | (e,uu____21689) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21712 =
            match uu____21712 with
            | (i,j) ->
                let uu____21723 = FStar_Ident.lid_equals i j  in
                if uu____21723
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
              let uu____21758 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____21768 = FStar_Ident.lid_equals i k  in
                        if uu____21768
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____21782 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____21782
                                  then []
                                  else
                                    (let uu____21789 =
                                       let uu____21798 =
                                         find_edge order1 (i, k)  in
                                       let uu____21801 =
                                         find_edge order1 (k, j)  in
                                       (uu____21798, uu____21801)  in
                                     match uu____21789 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____21816 =
                                           compose_edges e1 e2  in
                                         [uu____21816]
                                     | uu____21817 -> [])))))
                 in
              FStar_List.append order1 uu____21758  in
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
                   let uu____21847 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____21850 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____21850
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____21847
                   then
                     let uu____21857 =
                       let uu____21863 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____21863)
                        in
                     let uu____21867 = get_range env  in
                     FStar_Errors.raise_error uu____21857 uu____21867
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____21945 = FStar_Ident.lid_equals i j
                                   in
                                if uu____21945
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____21997 =
                                              let uu____22006 =
                                                find_edge order2 (i, k)  in
                                              let uu____22009 =
                                                find_edge order2 (j, k)  in
                                              (uu____22006, uu____22009)  in
                                            match uu____21997 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____22051,uu____22052)
                                                     ->
                                                     let uu____22059 =
                                                       let uu____22066 =
                                                         let uu____22068 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22068
                                                          in
                                                       let uu____22071 =
                                                         let uu____22073 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____22073
                                                          in
                                                       (uu____22066,
                                                         uu____22071)
                                                        in
                                                     (match uu____22059 with
                                                      | (true ,true ) ->
                                                          let uu____22090 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____22090
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
                                            | uu____22133 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___260_22206 = env.effects  in
              { decls = (uu___260_22206.decls); order = order2; joins }  in
            let uu___261_22207 = env  in
            {
              solver = (uu___261_22207.solver);
              range = (uu___261_22207.range);
              curmodule = (uu___261_22207.curmodule);
              gamma = (uu___261_22207.gamma);
              gamma_sig = (uu___261_22207.gamma_sig);
              gamma_cache = (uu___261_22207.gamma_cache);
              modules = (uu___261_22207.modules);
              expected_typ = (uu___261_22207.expected_typ);
              sigtab = (uu___261_22207.sigtab);
              attrtab = (uu___261_22207.attrtab);
              is_pattern = (uu___261_22207.is_pattern);
              instantiate_imp = (uu___261_22207.instantiate_imp);
              effects;
              generalize = (uu___261_22207.generalize);
              letrecs = (uu___261_22207.letrecs);
              top_level = (uu___261_22207.top_level);
              check_uvars = (uu___261_22207.check_uvars);
              use_eq = (uu___261_22207.use_eq);
              is_iface = (uu___261_22207.is_iface);
              admit = (uu___261_22207.admit);
              lax = (uu___261_22207.lax);
              lax_universes = (uu___261_22207.lax_universes);
              phase1 = (uu___261_22207.phase1);
              failhard = (uu___261_22207.failhard);
              nosynth = (uu___261_22207.nosynth);
              uvar_subtyping = (uu___261_22207.uvar_subtyping);
              tc_term = (uu___261_22207.tc_term);
              type_of = (uu___261_22207.type_of);
              universe_of = (uu___261_22207.universe_of);
              check_type_of = (uu___261_22207.check_type_of);
              use_bv_sorts = (uu___261_22207.use_bv_sorts);
              qtbl_name_and_index = (uu___261_22207.qtbl_name_and_index);
              normalized_eff_names = (uu___261_22207.normalized_eff_names);
              fv_delta_depths = (uu___261_22207.fv_delta_depths);
              proof_ns = (uu___261_22207.proof_ns);
              synth_hook = (uu___261_22207.synth_hook);
              splice = (uu___261_22207.splice);
              postprocess = (uu___261_22207.postprocess);
              is_native_tactic = (uu___261_22207.is_native_tactic);
              identifier_info = (uu___261_22207.identifier_info);
              tc_hooks = (uu___261_22207.tc_hooks);
              dsenv = (uu___261_22207.dsenv);
              nbe = (uu___261_22207.nbe)
            }))
      | uu____22208 -> env
  
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
        | uu____22237 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22250 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22250 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22267 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22267 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____22292 =
                     let uu____22298 =
                       let uu____22300 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22308 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22319 =
                         let uu____22321 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22321  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22300 uu____22308 uu____22319
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22298)
                      in
                   FStar_Errors.raise_error uu____22292
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22329 =
                     let uu____22340 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22340 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22377  ->
                        fun uu____22378  ->
                          match (uu____22377, uu____22378) with
                          | ((x,uu____22408),(t,uu____22410)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22329
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22441 =
                     let uu___262_22442 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___262_22442.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___262_22442.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___262_22442.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___262_22442.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22441
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22454 .
    'Auu____22454 ->
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
          let uu____22484 = effect_decl_opt env effect_name  in
          match uu____22484 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22523 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22546 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22585 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.strcat uu____22585
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22590 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22590
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22605 =
                     let uu____22608 = get_range env  in
                     let uu____22609 =
                       let uu____22616 =
                         let uu____22617 =
                           let uu____22634 =
                             let uu____22645 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22645; wp]  in
                           (repr, uu____22634)  in
                         FStar_Syntax_Syntax.Tm_app uu____22617  in
                       FStar_Syntax_Syntax.mk uu____22616  in
                     uu____22609 FStar_Pervasives_Native.None uu____22608  in
                   FStar_Pervasives_Native.Some uu____22605)
  
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
      | uu____22775 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22790 =
        let uu____22791 = FStar_Syntax_Subst.compress t  in
        uu____22791.FStar_Syntax_Syntax.n  in
      match uu____22790 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22795,c) ->
          is_reifiable_comp env c
      | uu____22817 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22837 =
           let uu____22839 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22839  in
         if uu____22837
         then
           let uu____22842 =
             let uu____22848 =
               let uu____22850 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22850
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22848)  in
           let uu____22854 = get_range env  in
           FStar_Errors.raise_error uu____22842 uu____22854
         else ());
        (let uu____22857 = effect_repr_aux true env c u_c  in
         match uu____22857 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___263_22893 = env  in
        {
          solver = (uu___263_22893.solver);
          range = (uu___263_22893.range);
          curmodule = (uu___263_22893.curmodule);
          gamma = (uu___263_22893.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___263_22893.gamma_cache);
          modules = (uu___263_22893.modules);
          expected_typ = (uu___263_22893.expected_typ);
          sigtab = (uu___263_22893.sigtab);
          attrtab = (uu___263_22893.attrtab);
          is_pattern = (uu___263_22893.is_pattern);
          instantiate_imp = (uu___263_22893.instantiate_imp);
          effects = (uu___263_22893.effects);
          generalize = (uu___263_22893.generalize);
          letrecs = (uu___263_22893.letrecs);
          top_level = (uu___263_22893.top_level);
          check_uvars = (uu___263_22893.check_uvars);
          use_eq = (uu___263_22893.use_eq);
          is_iface = (uu___263_22893.is_iface);
          admit = (uu___263_22893.admit);
          lax = (uu___263_22893.lax);
          lax_universes = (uu___263_22893.lax_universes);
          phase1 = (uu___263_22893.phase1);
          failhard = (uu___263_22893.failhard);
          nosynth = (uu___263_22893.nosynth);
          uvar_subtyping = (uu___263_22893.uvar_subtyping);
          tc_term = (uu___263_22893.tc_term);
          type_of = (uu___263_22893.type_of);
          universe_of = (uu___263_22893.universe_of);
          check_type_of = (uu___263_22893.check_type_of);
          use_bv_sorts = (uu___263_22893.use_bv_sorts);
          qtbl_name_and_index = (uu___263_22893.qtbl_name_and_index);
          normalized_eff_names = (uu___263_22893.normalized_eff_names);
          fv_delta_depths = (uu___263_22893.fv_delta_depths);
          proof_ns = (uu___263_22893.proof_ns);
          synth_hook = (uu___263_22893.synth_hook);
          splice = (uu___263_22893.splice);
          postprocess = (uu___263_22893.postprocess);
          is_native_tactic = (uu___263_22893.is_native_tactic);
          identifier_info = (uu___263_22893.identifier_info);
          tc_hooks = (uu___263_22893.tc_hooks);
          dsenv = (uu___263_22893.dsenv);
          nbe = (uu___263_22893.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___264_22907 = env  in
      {
        solver = (uu___264_22907.solver);
        range = (uu___264_22907.range);
        curmodule = (uu___264_22907.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___264_22907.gamma_sig);
        gamma_cache = (uu___264_22907.gamma_cache);
        modules = (uu___264_22907.modules);
        expected_typ = (uu___264_22907.expected_typ);
        sigtab = (uu___264_22907.sigtab);
        attrtab = (uu___264_22907.attrtab);
        is_pattern = (uu___264_22907.is_pattern);
        instantiate_imp = (uu___264_22907.instantiate_imp);
        effects = (uu___264_22907.effects);
        generalize = (uu___264_22907.generalize);
        letrecs = (uu___264_22907.letrecs);
        top_level = (uu___264_22907.top_level);
        check_uvars = (uu___264_22907.check_uvars);
        use_eq = (uu___264_22907.use_eq);
        is_iface = (uu___264_22907.is_iface);
        admit = (uu___264_22907.admit);
        lax = (uu___264_22907.lax);
        lax_universes = (uu___264_22907.lax_universes);
        phase1 = (uu___264_22907.phase1);
        failhard = (uu___264_22907.failhard);
        nosynth = (uu___264_22907.nosynth);
        uvar_subtyping = (uu___264_22907.uvar_subtyping);
        tc_term = (uu___264_22907.tc_term);
        type_of = (uu___264_22907.type_of);
        universe_of = (uu___264_22907.universe_of);
        check_type_of = (uu___264_22907.check_type_of);
        use_bv_sorts = (uu___264_22907.use_bv_sorts);
        qtbl_name_and_index = (uu___264_22907.qtbl_name_and_index);
        normalized_eff_names = (uu___264_22907.normalized_eff_names);
        fv_delta_depths = (uu___264_22907.fv_delta_depths);
        proof_ns = (uu___264_22907.proof_ns);
        synth_hook = (uu___264_22907.synth_hook);
        splice = (uu___264_22907.splice);
        postprocess = (uu___264_22907.postprocess);
        is_native_tactic = (uu___264_22907.is_native_tactic);
        identifier_info = (uu___264_22907.identifier_info);
        tc_hooks = (uu___264_22907.tc_hooks);
        dsenv = (uu___264_22907.dsenv);
        nbe = (uu___264_22907.nbe)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  ->
    fun x  -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
  
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env  ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___265_22965 = env  in
             {
               solver = (uu___265_22965.solver);
               range = (uu___265_22965.range);
               curmodule = (uu___265_22965.curmodule);
               gamma = rest;
               gamma_sig = (uu___265_22965.gamma_sig);
               gamma_cache = (uu___265_22965.gamma_cache);
               modules = (uu___265_22965.modules);
               expected_typ = (uu___265_22965.expected_typ);
               sigtab = (uu___265_22965.sigtab);
               attrtab = (uu___265_22965.attrtab);
               is_pattern = (uu___265_22965.is_pattern);
               instantiate_imp = (uu___265_22965.instantiate_imp);
               effects = (uu___265_22965.effects);
               generalize = (uu___265_22965.generalize);
               letrecs = (uu___265_22965.letrecs);
               top_level = (uu___265_22965.top_level);
               check_uvars = (uu___265_22965.check_uvars);
               use_eq = (uu___265_22965.use_eq);
               is_iface = (uu___265_22965.is_iface);
               admit = (uu___265_22965.admit);
               lax = (uu___265_22965.lax);
               lax_universes = (uu___265_22965.lax_universes);
               phase1 = (uu___265_22965.phase1);
               failhard = (uu___265_22965.failhard);
               nosynth = (uu___265_22965.nosynth);
               uvar_subtyping = (uu___265_22965.uvar_subtyping);
               tc_term = (uu___265_22965.tc_term);
               type_of = (uu___265_22965.type_of);
               universe_of = (uu___265_22965.universe_of);
               check_type_of = (uu___265_22965.check_type_of);
               use_bv_sorts = (uu___265_22965.use_bv_sorts);
               qtbl_name_and_index = (uu___265_22965.qtbl_name_and_index);
               normalized_eff_names = (uu___265_22965.normalized_eff_names);
               fv_delta_depths = (uu___265_22965.fv_delta_depths);
               proof_ns = (uu___265_22965.proof_ns);
               synth_hook = (uu___265_22965.synth_hook);
               splice = (uu___265_22965.splice);
               postprocess = (uu___265_22965.postprocess);
               is_native_tactic = (uu___265_22965.is_native_tactic);
               identifier_info = (uu___265_22965.identifier_info);
               tc_hooks = (uu___265_22965.tc_hooks);
               dsenv = (uu___265_22965.dsenv);
               nbe = (uu___265_22965.nbe)
             }))
    | uu____22966 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____22995  ->
             match uu____22995 with | (x,uu____23003) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___266_23038 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___266_23038.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___266_23038.FStar_Syntax_Syntax.index);
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
      (let uu___267_23080 = env  in
       {
         solver = (uu___267_23080.solver);
         range = (uu___267_23080.range);
         curmodule = (uu___267_23080.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___267_23080.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___267_23080.sigtab);
         attrtab = (uu___267_23080.attrtab);
         is_pattern = (uu___267_23080.is_pattern);
         instantiate_imp = (uu___267_23080.instantiate_imp);
         effects = (uu___267_23080.effects);
         generalize = (uu___267_23080.generalize);
         letrecs = (uu___267_23080.letrecs);
         top_level = (uu___267_23080.top_level);
         check_uvars = (uu___267_23080.check_uvars);
         use_eq = (uu___267_23080.use_eq);
         is_iface = (uu___267_23080.is_iface);
         admit = (uu___267_23080.admit);
         lax = (uu___267_23080.lax);
         lax_universes = (uu___267_23080.lax_universes);
         phase1 = (uu___267_23080.phase1);
         failhard = (uu___267_23080.failhard);
         nosynth = (uu___267_23080.nosynth);
         uvar_subtyping = (uu___267_23080.uvar_subtyping);
         tc_term = (uu___267_23080.tc_term);
         type_of = (uu___267_23080.type_of);
         universe_of = (uu___267_23080.universe_of);
         check_type_of = (uu___267_23080.check_type_of);
         use_bv_sorts = (uu___267_23080.use_bv_sorts);
         qtbl_name_and_index = (uu___267_23080.qtbl_name_and_index);
         normalized_eff_names = (uu___267_23080.normalized_eff_names);
         fv_delta_depths = (uu___267_23080.fv_delta_depths);
         proof_ns = (uu___267_23080.proof_ns);
         synth_hook = (uu___267_23080.synth_hook);
         splice = (uu___267_23080.splice);
         postprocess = (uu___267_23080.postprocess);
         is_native_tactic = (uu___267_23080.is_native_tactic);
         identifier_info = (uu___267_23080.identifier_info);
         tc_hooks = (uu___267_23080.tc_hooks);
         dsenv = (uu___267_23080.dsenv);
         nbe = (uu___267_23080.nbe)
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
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____23124 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____23124 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____23152 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____23152)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___268_23168 = env  in
      {
        solver = (uu___268_23168.solver);
        range = (uu___268_23168.range);
        curmodule = (uu___268_23168.curmodule);
        gamma = (uu___268_23168.gamma);
        gamma_sig = (uu___268_23168.gamma_sig);
        gamma_cache = (uu___268_23168.gamma_cache);
        modules = (uu___268_23168.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___268_23168.sigtab);
        attrtab = (uu___268_23168.attrtab);
        is_pattern = (uu___268_23168.is_pattern);
        instantiate_imp = (uu___268_23168.instantiate_imp);
        effects = (uu___268_23168.effects);
        generalize = (uu___268_23168.generalize);
        letrecs = (uu___268_23168.letrecs);
        top_level = (uu___268_23168.top_level);
        check_uvars = (uu___268_23168.check_uvars);
        use_eq = false;
        is_iface = (uu___268_23168.is_iface);
        admit = (uu___268_23168.admit);
        lax = (uu___268_23168.lax);
        lax_universes = (uu___268_23168.lax_universes);
        phase1 = (uu___268_23168.phase1);
        failhard = (uu___268_23168.failhard);
        nosynth = (uu___268_23168.nosynth);
        uvar_subtyping = (uu___268_23168.uvar_subtyping);
        tc_term = (uu___268_23168.tc_term);
        type_of = (uu___268_23168.type_of);
        universe_of = (uu___268_23168.universe_of);
        check_type_of = (uu___268_23168.check_type_of);
        use_bv_sorts = (uu___268_23168.use_bv_sorts);
        qtbl_name_and_index = (uu___268_23168.qtbl_name_and_index);
        normalized_eff_names = (uu___268_23168.normalized_eff_names);
        fv_delta_depths = (uu___268_23168.fv_delta_depths);
        proof_ns = (uu___268_23168.proof_ns);
        synth_hook = (uu___268_23168.synth_hook);
        splice = (uu___268_23168.splice);
        postprocess = (uu___268_23168.postprocess);
        is_native_tactic = (uu___268_23168.is_native_tactic);
        identifier_info = (uu___268_23168.identifier_info);
        tc_hooks = (uu___268_23168.tc_hooks);
        dsenv = (uu___268_23168.dsenv);
        nbe = (uu___268_23168.nbe)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun env_  ->
    let uu____23199 = expected_typ env_  in
    ((let uu___269_23205 = env_  in
      {
        solver = (uu___269_23205.solver);
        range = (uu___269_23205.range);
        curmodule = (uu___269_23205.curmodule);
        gamma = (uu___269_23205.gamma);
        gamma_sig = (uu___269_23205.gamma_sig);
        gamma_cache = (uu___269_23205.gamma_cache);
        modules = (uu___269_23205.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___269_23205.sigtab);
        attrtab = (uu___269_23205.attrtab);
        is_pattern = (uu___269_23205.is_pattern);
        instantiate_imp = (uu___269_23205.instantiate_imp);
        effects = (uu___269_23205.effects);
        generalize = (uu___269_23205.generalize);
        letrecs = (uu___269_23205.letrecs);
        top_level = (uu___269_23205.top_level);
        check_uvars = (uu___269_23205.check_uvars);
        use_eq = false;
        is_iface = (uu___269_23205.is_iface);
        admit = (uu___269_23205.admit);
        lax = (uu___269_23205.lax);
        lax_universes = (uu___269_23205.lax_universes);
        phase1 = (uu___269_23205.phase1);
        failhard = (uu___269_23205.failhard);
        nosynth = (uu___269_23205.nosynth);
        uvar_subtyping = (uu___269_23205.uvar_subtyping);
        tc_term = (uu___269_23205.tc_term);
        type_of = (uu___269_23205.type_of);
        universe_of = (uu___269_23205.universe_of);
        check_type_of = (uu___269_23205.check_type_of);
        use_bv_sorts = (uu___269_23205.use_bv_sorts);
        qtbl_name_and_index = (uu___269_23205.qtbl_name_and_index);
        normalized_eff_names = (uu___269_23205.normalized_eff_names);
        fv_delta_depths = (uu___269_23205.fv_delta_depths);
        proof_ns = (uu___269_23205.proof_ns);
        synth_hook = (uu___269_23205.synth_hook);
        splice = (uu___269_23205.splice);
        postprocess = (uu___269_23205.postprocess);
        is_native_tactic = (uu___269_23205.is_native_tactic);
        identifier_info = (uu___269_23205.identifier_info);
        tc_hooks = (uu___269_23205.tc_hooks);
        dsenv = (uu___269_23205.dsenv);
        nbe = (uu___269_23205.nbe)
      }), uu____23199)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23217 =
      let uu____23220 = FStar_Ident.id_of_text ""  in [uu____23220]  in
    FStar_Ident.lid_of_ids uu____23217  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23227 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23227
        then
          let uu____23232 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23232 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___270_23260 = env  in
       {
         solver = (uu___270_23260.solver);
         range = (uu___270_23260.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___270_23260.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___270_23260.expected_typ);
         sigtab = (uu___270_23260.sigtab);
         attrtab = (uu___270_23260.attrtab);
         is_pattern = (uu___270_23260.is_pattern);
         instantiate_imp = (uu___270_23260.instantiate_imp);
         effects = (uu___270_23260.effects);
         generalize = (uu___270_23260.generalize);
         letrecs = (uu___270_23260.letrecs);
         top_level = (uu___270_23260.top_level);
         check_uvars = (uu___270_23260.check_uvars);
         use_eq = (uu___270_23260.use_eq);
         is_iface = (uu___270_23260.is_iface);
         admit = (uu___270_23260.admit);
         lax = (uu___270_23260.lax);
         lax_universes = (uu___270_23260.lax_universes);
         phase1 = (uu___270_23260.phase1);
         failhard = (uu___270_23260.failhard);
         nosynth = (uu___270_23260.nosynth);
         uvar_subtyping = (uu___270_23260.uvar_subtyping);
         tc_term = (uu___270_23260.tc_term);
         type_of = (uu___270_23260.type_of);
         universe_of = (uu___270_23260.universe_of);
         check_type_of = (uu___270_23260.check_type_of);
         use_bv_sorts = (uu___270_23260.use_bv_sorts);
         qtbl_name_and_index = (uu___270_23260.qtbl_name_and_index);
         normalized_eff_names = (uu___270_23260.normalized_eff_names);
         fv_delta_depths = (uu___270_23260.fv_delta_depths);
         proof_ns = (uu___270_23260.proof_ns);
         synth_hook = (uu___270_23260.synth_hook);
         splice = (uu___270_23260.splice);
         postprocess = (uu___270_23260.postprocess);
         is_native_tactic = (uu___270_23260.is_native_tactic);
         identifier_info = (uu___270_23260.identifier_info);
         tc_hooks = (uu___270_23260.tc_hooks);
         dsenv = (uu___270_23260.dsenv);
         nbe = (uu___270_23260.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23312)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23316,(uu____23317,t)))::tl1
          ->
          let uu____23338 =
            let uu____23341 = FStar_Syntax_Free.uvars t  in
            ext out uu____23341  in
          aux uu____23338 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23344;
            FStar_Syntax_Syntax.index = uu____23345;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23353 =
            let uu____23356 = FStar_Syntax_Free.uvars t  in
            ext out uu____23356  in
          aux uu____23353 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23414)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23418,(uu____23419,t)))::tl1
          ->
          let uu____23440 =
            let uu____23443 = FStar_Syntax_Free.univs t  in
            ext out uu____23443  in
          aux uu____23440 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23446;
            FStar_Syntax_Syntax.index = uu____23447;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23455 =
            let uu____23458 = FStar_Syntax_Free.univs t  in
            ext out uu____23458  in
          aux uu____23455 tl1
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
          let uu____23520 = FStar_Util.set_add uname out  in
          aux uu____23520 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23523,(uu____23524,t)))::tl1
          ->
          let uu____23545 =
            let uu____23548 = FStar_Syntax_Free.univnames t  in
            ext out uu____23548  in
          aux uu____23545 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23551;
            FStar_Syntax_Syntax.index = uu____23552;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23560 =
            let uu____23563 = FStar_Syntax_Free.univnames t  in
            ext out uu____23563  in
          aux uu____23560 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___244_23584  ->
            match uu___244_23584 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23588 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23601 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23612 =
      let uu____23621 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23621
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23612 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23669 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___245_23682  ->
              match uu___245_23682 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23685 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.strcat "Binding_var " uu____23685
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23691) ->
                  let uu____23708 = FStar_Ident.string_of_lid l  in
                  Prims.strcat "Binding_lid " uu____23708))
       in
    FStar_All.pipe_right uu____23669 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___246_23722  ->
    match uu___246_23722 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23728 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.strcat "Unfold " uu____23728
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23751  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23806) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____23839,uu____23840) -> false  in
      let uu____23854 =
        FStar_List.tryFind
          (fun uu____23876  ->
             match uu____23876 with | (p,uu____23887) -> list_prefix p path)
          env.proof_ns
         in
      match uu____23854 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23906,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23936 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23936
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___271_23958 = e  in
        {
          solver = (uu___271_23958.solver);
          range = (uu___271_23958.range);
          curmodule = (uu___271_23958.curmodule);
          gamma = (uu___271_23958.gamma);
          gamma_sig = (uu___271_23958.gamma_sig);
          gamma_cache = (uu___271_23958.gamma_cache);
          modules = (uu___271_23958.modules);
          expected_typ = (uu___271_23958.expected_typ);
          sigtab = (uu___271_23958.sigtab);
          attrtab = (uu___271_23958.attrtab);
          is_pattern = (uu___271_23958.is_pattern);
          instantiate_imp = (uu___271_23958.instantiate_imp);
          effects = (uu___271_23958.effects);
          generalize = (uu___271_23958.generalize);
          letrecs = (uu___271_23958.letrecs);
          top_level = (uu___271_23958.top_level);
          check_uvars = (uu___271_23958.check_uvars);
          use_eq = (uu___271_23958.use_eq);
          is_iface = (uu___271_23958.is_iface);
          admit = (uu___271_23958.admit);
          lax = (uu___271_23958.lax);
          lax_universes = (uu___271_23958.lax_universes);
          phase1 = (uu___271_23958.phase1);
          failhard = (uu___271_23958.failhard);
          nosynth = (uu___271_23958.nosynth);
          uvar_subtyping = (uu___271_23958.uvar_subtyping);
          tc_term = (uu___271_23958.tc_term);
          type_of = (uu___271_23958.type_of);
          universe_of = (uu___271_23958.universe_of);
          check_type_of = (uu___271_23958.check_type_of);
          use_bv_sorts = (uu___271_23958.use_bv_sorts);
          qtbl_name_and_index = (uu___271_23958.qtbl_name_and_index);
          normalized_eff_names = (uu___271_23958.normalized_eff_names);
          fv_delta_depths = (uu___271_23958.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___271_23958.synth_hook);
          splice = (uu___271_23958.splice);
          postprocess = (uu___271_23958.postprocess);
          is_native_tactic = (uu___271_23958.is_native_tactic);
          identifier_info = (uu___271_23958.identifier_info);
          tc_hooks = (uu___271_23958.tc_hooks);
          dsenv = (uu___271_23958.dsenv);
          nbe = (uu___271_23958.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___272_24006 = e  in
      {
        solver = (uu___272_24006.solver);
        range = (uu___272_24006.range);
        curmodule = (uu___272_24006.curmodule);
        gamma = (uu___272_24006.gamma);
        gamma_sig = (uu___272_24006.gamma_sig);
        gamma_cache = (uu___272_24006.gamma_cache);
        modules = (uu___272_24006.modules);
        expected_typ = (uu___272_24006.expected_typ);
        sigtab = (uu___272_24006.sigtab);
        attrtab = (uu___272_24006.attrtab);
        is_pattern = (uu___272_24006.is_pattern);
        instantiate_imp = (uu___272_24006.instantiate_imp);
        effects = (uu___272_24006.effects);
        generalize = (uu___272_24006.generalize);
        letrecs = (uu___272_24006.letrecs);
        top_level = (uu___272_24006.top_level);
        check_uvars = (uu___272_24006.check_uvars);
        use_eq = (uu___272_24006.use_eq);
        is_iface = (uu___272_24006.is_iface);
        admit = (uu___272_24006.admit);
        lax = (uu___272_24006.lax);
        lax_universes = (uu___272_24006.lax_universes);
        phase1 = (uu___272_24006.phase1);
        failhard = (uu___272_24006.failhard);
        nosynth = (uu___272_24006.nosynth);
        uvar_subtyping = (uu___272_24006.uvar_subtyping);
        tc_term = (uu___272_24006.tc_term);
        type_of = (uu___272_24006.type_of);
        universe_of = (uu___272_24006.universe_of);
        check_type_of = (uu___272_24006.check_type_of);
        use_bv_sorts = (uu___272_24006.use_bv_sorts);
        qtbl_name_and_index = (uu___272_24006.qtbl_name_and_index);
        normalized_eff_names = (uu___272_24006.normalized_eff_names);
        fv_delta_depths = (uu___272_24006.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___272_24006.synth_hook);
        splice = (uu___272_24006.splice);
        postprocess = (uu___272_24006.postprocess);
        is_native_tactic = (uu___272_24006.is_native_tactic);
        identifier_info = (uu___272_24006.identifier_info);
        tc_hooks = (uu___272_24006.tc_hooks);
        dsenv = (uu___272_24006.dsenv);
        nbe = (uu___272_24006.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____24022 = FStar_Syntax_Free.names t  in
      let uu____24025 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____24022 uu____24025
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____24048 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____24048
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____24058 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____24058
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____24079 =
      match uu____24079 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____24099 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____24099)
       in
    let uu____24107 =
      let uu____24111 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____24111 FStar_List.rev  in
    FStar_All.pipe_right uu____24107 (FStar_String.concat " ")
  
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
                  (let uu____24181 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____24181 with
                   | FStar_Pervasives_Native.Some uu____24185 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____24188 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____24198;
        univ_ineqs = uu____24199; implicits = uu____24200;_} -> true
    | uu____24212 -> false
  
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
          let uu___273_24243 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___273_24243.deferred);
            univ_ineqs = (uu___273_24243.univ_ineqs);
            implicits = (uu___273_24243.implicits)
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
          let uu____24282 = FStar_Options.defensive ()  in
          if uu____24282
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24288 =
              let uu____24290 =
                let uu____24292 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24292  in
              Prims.op_Negation uu____24290  in
            (if uu____24288
             then
               let uu____24299 =
                 let uu____24305 =
                   let uu____24307 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24309 =
                     let uu____24311 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24311
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24307 uu____24309
                    in
                 (FStar_Errors.Warning_Defensive, uu____24305)  in
               FStar_Errors.log_issue rng uu____24299
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
          let uu____24351 =
            let uu____24353 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24353  in
          if uu____24351
          then ()
          else
            (let uu____24358 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24358 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24384 =
            let uu____24386 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24386  in
          if uu____24384
          then ()
          else
            (let uu____24391 = bound_vars e  in
             def_check_closed_in rng msg uu____24391 t)
  
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
          let uu___274_24430 = g  in
          let uu____24431 =
            let uu____24432 =
              let uu____24433 =
                let uu____24440 =
                  let uu____24441 =
                    let uu____24458 =
                      let uu____24469 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24469]  in
                    (f, uu____24458)  in
                  FStar_Syntax_Syntax.Tm_app uu____24441  in
                FStar_Syntax_Syntax.mk uu____24440  in
              uu____24433 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_2  -> FStar_TypeChecker_Common.NonTrivial _0_2)
              uu____24432
             in
          {
            guard_f = uu____24431;
            deferred = (uu___274_24430.deferred);
            univ_ineqs = (uu___274_24430.univ_ineqs);
            implicits = (uu___274_24430.implicits)
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
          let uu___275_24526 = g  in
          let uu____24527 =
            let uu____24528 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24528  in
          {
            guard_f = uu____24527;
            deferred = (uu___275_24526.deferred);
            univ_ineqs = (uu___275_24526.univ_ineqs);
            implicits = (uu___275_24526.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___276_24545 = g  in
          let uu____24546 =
            let uu____24547 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24547  in
          {
            guard_f = uu____24546;
            deferred = (uu___276_24545.deferred);
            univ_ineqs = (uu___276_24545.univ_ineqs);
            implicits = (uu___276_24545.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___277_24549 = g  in
          let uu____24550 =
            let uu____24551 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24551  in
          {
            guard_f = uu____24550;
            deferred = (uu___277_24549.deferred);
            univ_ineqs = (uu___277_24549.univ_ineqs);
            implicits = (uu___277_24549.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24558 ->
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
          let uu____24575 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24575
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24582 =
      let uu____24583 = FStar_Syntax_Util.unmeta t  in
      uu____24583.FStar_Syntax_Syntax.n  in
    match uu____24582 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24587 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24630 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24630;
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
                       let uu____24725 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24725
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___278_24732 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___278_24732.deferred);
              univ_ineqs = (uu___278_24732.univ_ineqs);
              implicits = (uu___278_24732.implicits)
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
               let uu____24766 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24766
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
            let uu___279_24793 = g  in
            let uu____24794 =
              let uu____24795 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24795  in
            {
              guard_f = uu____24794;
              deferred = (uu___279_24793.deferred);
              univ_ineqs = (uu___279_24793.univ_ineqs);
              implicits = (uu___279_24793.implicits)
            }
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list,guard_t)
              FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            let uu____24836 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____24836 with
            | FStar_Pervasives_Native.Some
                (uu____24861::(tm,uu____24863)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], trivial_guard)
            | uu____24927 ->
                let binders = all_binders env  in
                let gamma = env.gamma  in
                let ctx_uvar =
                  let uu____24945 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____24945;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
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
                      imp_range = r;
                      imp_meta = FStar_Pervasives_Native.None
                    }  in
                  let g =
                    let uu___280_24981 = trivial_guard  in
                    {
                      guard_f = (uu___280_24981.guard_f);
                      deferred = (uu___280_24981.deferred);
                      univ_ineqs = (uu___280_24981.univ_ineqs);
                      implicits = [imp]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____24999  -> ());
    push = (fun uu____25001  -> ());
    pop = (fun uu____25004  -> ());
    snapshot =
      (fun uu____25007  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____25026  -> fun uu____25027  -> ());
    encode_modul = (fun uu____25042  -> fun uu____25043  -> ());
    encode_sig = (fun uu____25046  -> fun uu____25047  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____25053 =
             let uu____25060 = FStar_Options.peek ()  in (e, g, uu____25060)
              in
           [uu____25053]);
    solve = (fun uu____25076  -> fun uu____25077  -> fun uu____25078  -> ());
    finish = (fun uu____25085  -> ());
    refresh = (fun uu____25087  -> ())
  } 