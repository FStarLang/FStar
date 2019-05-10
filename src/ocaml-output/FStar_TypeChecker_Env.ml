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
  fun projectee  -> match projectee with | Beta  -> true | uu____109 -> false 
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee  -> match projectee with | Iota  -> true | uu____120 -> false 
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee  -> match projectee with | Zeta  -> true | uu____131 -> false 
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exclude _0 -> true | uu____143 -> false
  
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee  -> match projectee with | Exclude _0 -> _0 
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee  -> match projectee with | Weak  -> true | uu____161 -> false 
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee  -> match projectee with | HNF  -> true | uu____172 -> false 
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____183 -> false
  
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding  -> true | uu____194 -> false
  
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____205 -> false
  
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | DoNotUnfoldPureLets  -> true | uu____216 -> false
  
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldUntil _0 -> true | uu____228 -> false
  
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee  -> match projectee with | UnfoldUntil _0 -> _0 
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldOnly _0 -> true | uu____249 -> false
  
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldOnly _0 -> _0 
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldFully _0 -> true | uu____276 -> false
  
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldFully _0 -> _0 
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldAttr _0 -> true | uu____303 -> false
  
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee  -> match projectee with | UnfoldAttr _0 -> _0 
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____327 -> false
  
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | PureSubtermsWithinComputations  -> true
    | uu____338 -> false
  
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Simplify  -> true | uu____349 -> false
  
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | EraseUniverses  -> true | uu____360 -> false
  
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | AllowUnboundUniverses  -> true
    | uu____371 -> false
  
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reify  -> true | uu____382 -> false
  
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CompressUvars  -> true | uu____393 -> false
  
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoFullNorm  -> true | uu____404 -> false
  
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | CheckNoUvars  -> true | uu____415 -> false
  
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unmeta  -> true | uu____426 -> false
  
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unascribe  -> true | uu____437 -> false
  
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee  -> match projectee with | NBE  -> true | uu____448 -> false 
let (uu___is_ForExtraction : step -> Prims.bool) =
  fun projectee  ->
    match projectee with | ForExtraction  -> true | uu____459 -> false
  
type steps = step Prims.list
let rec (print_step : step -> Prims.string) =
  fun uu___0_469  ->
    match uu___0_469 with
    | Beta  -> "Beta"
    | Iota  -> "Iota"
    | Zeta  -> "Zeta"
    | Exclude s ->
        let uu____475 =
          let uu____477 = print_step s  in Prims.op_Hat uu____477 ")"  in
        Prims.op_Hat "(Exclude " uu____475
    | Weak  -> "Weak"
    | HNF  -> "HNF"
    | Primops  -> "Primops"
    | Eager_unfolding  -> "Eager_unfolding"
    | Inlining  -> "Inlining"
    | DoNotUnfoldPureLets  -> "DoNotUnfoldPureLets"
    | UnfoldUntil dd ->
        let uu____488 =
          let uu____490 = FStar_Syntax_Print.delta_depth_to_string dd  in
          Prims.op_Hat uu____490 ")"  in
        Prims.op_Hat "(UnfoldUntil " uu____488
    | UnfoldOnly lids ->
        let uu____497 =
          let uu____499 =
            let uu____501 = FStar_List.map FStar_Ident.string_of_lid lids  in
            FStar_All.pipe_right uu____501 (FStar_String.concat ", ")  in
          Prims.op_Hat uu____499 ")"  in
        Prims.op_Hat "(UnfoldOnly " uu____497
    | UnfoldFully lids ->
        let uu____516 =
          let uu____518 =
            let uu____520 = FStar_List.map FStar_Ident.string_of_lid lids  in
            FStar_All.pipe_right uu____520 (FStar_String.concat ", ")  in
          Prims.op_Hat uu____518 ")"  in
        Prims.op_Hat "(UnfoldFully " uu____516
    | UnfoldAttr lids ->
        let uu____535 =
          let uu____537 =
            let uu____539 = FStar_List.map FStar_Ident.string_of_lid lids  in
            FStar_All.pipe_right uu____539 (FStar_String.concat ", ")  in
          Prims.op_Hat uu____537 ")"  in
        Prims.op_Hat "(UnfoldAttr " uu____535
    | UnfoldTac  -> "UnfoldTac"
    | PureSubtermsWithinComputations  -> "PureSubtermsWithinComputations"
    | Simplify  -> "Simplify"
    | EraseUniverses  -> "EraseUniverses"
    | AllowUnboundUniverses  -> "AllowUnboundUniverses"
    | Reify  -> "Reify"
    | CompressUvars  -> "CompressUvars"
    | NoFullNorm  -> "NoFullNorm"
    | CheckNoUvars  -> "CheckNoUvars"
    | Unmeta  -> "Unmeta"
    | Unascribe  -> "Unascribe"
    | NBE  -> "NBE"
    | ForExtraction  -> "ForExtraction"
  
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
      | uu____620 -> false
  
type sig_binding =
  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____646 -> false
  
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | InliningDelta  -> true | uu____657 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____668 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____680 -> false
  
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
           (fun uu___1_11897  ->
              match uu___1_11897 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____11900 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____11900  in
                  let uu____11901 =
                    let uu____11902 = FStar_Syntax_Subst.compress y  in
                    uu____11902.FStar_Syntax_Syntax.n  in
                  (match uu____11901 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____11906 =
                         let uu___363_11907 = y1  in
                         let uu____11908 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___363_11907.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___363_11907.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____11908
                         }  in
                       FStar_Syntax_Syntax.Binding_var uu____11906
                   | uu____11911 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___369_11925 = env  in
      let uu____11926 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___369_11925.solver);
        range = (uu___369_11925.range);
        curmodule = (uu___369_11925.curmodule);
        gamma = uu____11926;
        gamma_sig = (uu___369_11925.gamma_sig);
        gamma_cache = (uu___369_11925.gamma_cache);
        modules = (uu___369_11925.modules);
        expected_typ = (uu___369_11925.expected_typ);
        sigtab = (uu___369_11925.sigtab);
        attrtab = (uu___369_11925.attrtab);
        is_pattern = (uu___369_11925.is_pattern);
        instantiate_imp = (uu___369_11925.instantiate_imp);
        effects = (uu___369_11925.effects);
        generalize = (uu___369_11925.generalize);
        letrecs = (uu___369_11925.letrecs);
        top_level = (uu___369_11925.top_level);
        check_uvars = (uu___369_11925.check_uvars);
        use_eq = (uu___369_11925.use_eq);
        is_iface = (uu___369_11925.is_iface);
        admit = (uu___369_11925.admit);
        lax = (uu___369_11925.lax);
        lax_universes = (uu___369_11925.lax_universes);
        phase1 = (uu___369_11925.phase1);
        failhard = (uu___369_11925.failhard);
        nosynth = (uu___369_11925.nosynth);
        uvar_subtyping = (uu___369_11925.uvar_subtyping);
        tc_term = (uu___369_11925.tc_term);
        type_of = (uu___369_11925.type_of);
        universe_of = (uu___369_11925.universe_of);
        check_type_of = (uu___369_11925.check_type_of);
        use_bv_sorts = (uu___369_11925.use_bv_sorts);
        qtbl_name_and_index = (uu___369_11925.qtbl_name_and_index);
        normalized_eff_names = (uu___369_11925.normalized_eff_names);
        fv_delta_depths = (uu___369_11925.fv_delta_depths);
        proof_ns = (uu___369_11925.proof_ns);
        synth_hook = (uu___369_11925.synth_hook);
        splice = (uu___369_11925.splice);
        postprocess = (uu___369_11925.postprocess);
        is_native_tactic = (uu___369_11925.is_native_tactic);
        identifier_info = (uu___369_11925.identifier_info);
        tc_hooks = (uu___369_11925.tc_hooks);
        dsenv = (uu___369_11925.dsenv);
        nbe = (uu___369_11925.nbe)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____11934  -> fun uu____11935  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___376_11957 = env  in
      {
        solver = (uu___376_11957.solver);
        range = (uu___376_11957.range);
        curmodule = (uu___376_11957.curmodule);
        gamma = (uu___376_11957.gamma);
        gamma_sig = (uu___376_11957.gamma_sig);
        gamma_cache = (uu___376_11957.gamma_cache);
        modules = (uu___376_11957.modules);
        expected_typ = (uu___376_11957.expected_typ);
        sigtab = (uu___376_11957.sigtab);
        attrtab = (uu___376_11957.attrtab);
        is_pattern = (uu___376_11957.is_pattern);
        instantiate_imp = (uu___376_11957.instantiate_imp);
        effects = (uu___376_11957.effects);
        generalize = (uu___376_11957.generalize);
        letrecs = (uu___376_11957.letrecs);
        top_level = (uu___376_11957.top_level);
        check_uvars = (uu___376_11957.check_uvars);
        use_eq = (uu___376_11957.use_eq);
        is_iface = (uu___376_11957.is_iface);
        admit = (uu___376_11957.admit);
        lax = (uu___376_11957.lax);
        lax_universes = (uu___376_11957.lax_universes);
        phase1 = (uu___376_11957.phase1);
        failhard = (uu___376_11957.failhard);
        nosynth = (uu___376_11957.nosynth);
        uvar_subtyping = (uu___376_11957.uvar_subtyping);
        tc_term = (uu___376_11957.tc_term);
        type_of = (uu___376_11957.type_of);
        universe_of = (uu___376_11957.universe_of);
        check_type_of = (uu___376_11957.check_type_of);
        use_bv_sorts = (uu___376_11957.use_bv_sorts);
        qtbl_name_and_index = (uu___376_11957.qtbl_name_and_index);
        normalized_eff_names = (uu___376_11957.normalized_eff_names);
        fv_delta_depths = (uu___376_11957.fv_delta_depths);
        proof_ns = (uu___376_11957.proof_ns);
        synth_hook = (uu___376_11957.synth_hook);
        splice = (uu___376_11957.splice);
        postprocess = (uu___376_11957.postprocess);
        is_native_tactic = (uu___376_11957.is_native_tactic);
        identifier_info = (uu___376_11957.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___376_11957.dsenv);
        nbe = (uu___376_11957.nbe)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___380_11969 = e  in
      let uu____11970 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g  in
      {
        solver = (uu___380_11969.solver);
        range = (uu___380_11969.range);
        curmodule = (uu___380_11969.curmodule);
        gamma = (uu___380_11969.gamma);
        gamma_sig = (uu___380_11969.gamma_sig);
        gamma_cache = (uu___380_11969.gamma_cache);
        modules = (uu___380_11969.modules);
        expected_typ = (uu___380_11969.expected_typ);
        sigtab = (uu___380_11969.sigtab);
        attrtab = (uu___380_11969.attrtab);
        is_pattern = (uu___380_11969.is_pattern);
        instantiate_imp = (uu___380_11969.instantiate_imp);
        effects = (uu___380_11969.effects);
        generalize = (uu___380_11969.generalize);
        letrecs = (uu___380_11969.letrecs);
        top_level = (uu___380_11969.top_level);
        check_uvars = (uu___380_11969.check_uvars);
        use_eq = (uu___380_11969.use_eq);
        is_iface = (uu___380_11969.is_iface);
        admit = (uu___380_11969.admit);
        lax = (uu___380_11969.lax);
        lax_universes = (uu___380_11969.lax_universes);
        phase1 = (uu___380_11969.phase1);
        failhard = (uu___380_11969.failhard);
        nosynth = (uu___380_11969.nosynth);
        uvar_subtyping = (uu___380_11969.uvar_subtyping);
        tc_term = (uu___380_11969.tc_term);
        type_of = (uu___380_11969.type_of);
        universe_of = (uu___380_11969.universe_of);
        check_type_of = (uu___380_11969.check_type_of);
        use_bv_sorts = (uu___380_11969.use_bv_sorts);
        qtbl_name_and_index = (uu___380_11969.qtbl_name_and_index);
        normalized_eff_names = (uu___380_11969.normalized_eff_names);
        fv_delta_depths = (uu___380_11969.fv_delta_depths);
        proof_ns = (uu___380_11969.proof_ns);
        synth_hook = (uu___380_11969.synth_hook);
        splice = (uu___380_11969.splice);
        postprocess = (uu___380_11969.postprocess);
        is_native_tactic = (uu___380_11969.is_native_tactic);
        identifier_info = (uu___380_11969.identifier_info);
        tc_hooks = (uu___380_11969.tc_hooks);
        dsenv = uu____11970;
        nbe = (uu___380_11969.nbe)
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
      | (NoDelta ,uu____11999) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____12002,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen )
          -> true
      | (Unfold uu____12004,FStar_Syntax_Syntax.Visible_default ) -> true
      | (InliningDelta ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____12007 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____12021 . unit -> 'Auu____12021 FStar_Util.smap =
  fun uu____12028  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____12034 . unit -> 'Auu____12034 FStar_Util.smap =
  fun uu____12041  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                  let uu____12179 = new_gamma_cache ()  in
                  let uu____12182 = new_sigtab ()  in
                  let uu____12185 = new_sigtab ()  in
                  let uu____12192 =
                    let uu____12207 =
                      FStar_Util.smap_create (Prims.parse_int "10")  in
                    (uu____12207, FStar_Pervasives_Native.None)  in
                  let uu____12228 =
                    FStar_Util.smap_create (Prims.parse_int "20")  in
                  let uu____12232 =
                    FStar_Util.smap_create (Prims.parse_int "50")  in
                  let uu____12236 = FStar_Options.using_facts_from ()  in
                  let uu____12237 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty
                     in
                  let uu____12240 = FStar_Syntax_DsEnv.empty_env deps  in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____12179;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____12182;
                    attrtab = uu____12185;
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
                    qtbl_name_and_index = uu____12192;
                    normalized_eff_names = uu____12228;
                    fv_delta_depths = uu____12232;
                    proof_ns = uu____12236;
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
                    is_native_tactic = (fun uu____12302  -> false);
                    identifier_info = uu____12237;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____12240;
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
  fun uu____12381  ->
    let uu____12382 = FStar_ST.op_Bang query_indices  in
    match uu____12382 with
    | [] -> failwith "Empty query indices!"
    | uu____12437 ->
        let uu____12447 =
          let uu____12457 =
            let uu____12465 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____12465  in
          let uu____12519 = FStar_ST.op_Bang query_indices  in uu____12457 ::
            uu____12519
           in
        FStar_ST.op_Colon_Equals query_indices uu____12447
  
let (pop_query_indices : unit -> unit) =
  fun uu____12615  ->
    let uu____12616 = FStar_ST.op_Bang query_indices  in
    match uu____12616 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices : unit -> (Prims.int * unit)) =
  fun uu____12743  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index : (FStar_Ident.lident * Prims.int) -> unit) =
  fun uu____12780  ->
    match uu____12780 with
    | (l,n1) ->
        let uu____12790 = FStar_ST.op_Bang query_indices  in
        (match uu____12790 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____12912 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit -> (FStar_Ident.lident * Prims.int) Prims.list) =
  fun uu____12935  ->
    let uu____12936 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____12936
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____13004 =
       let uu____13007 = FStar_ST.op_Bang stack  in env :: uu____13007  in
     FStar_ST.op_Colon_Equals stack uu____13004);
    (let uu___448_13056 = env  in
     let uu____13057 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____13060 = FStar_Util.smap_copy (sigtab env)  in
     let uu____13063 = FStar_Util.smap_copy (attrtab env)  in
     let uu____13070 =
       let uu____13085 =
         let uu____13089 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____13089  in
       let uu____13121 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____13085, uu____13121)  in
     let uu____13170 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____13173 = FStar_Util.smap_copy env.fv_delta_depths  in
     let uu____13176 =
       let uu____13179 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____13179  in
     {
       solver = (uu___448_13056.solver);
       range = (uu___448_13056.range);
       curmodule = (uu___448_13056.curmodule);
       gamma = (uu___448_13056.gamma);
       gamma_sig = (uu___448_13056.gamma_sig);
       gamma_cache = uu____13057;
       modules = (uu___448_13056.modules);
       expected_typ = (uu___448_13056.expected_typ);
       sigtab = uu____13060;
       attrtab = uu____13063;
       is_pattern = (uu___448_13056.is_pattern);
       instantiate_imp = (uu___448_13056.instantiate_imp);
       effects = (uu___448_13056.effects);
       generalize = (uu___448_13056.generalize);
       letrecs = (uu___448_13056.letrecs);
       top_level = (uu___448_13056.top_level);
       check_uvars = (uu___448_13056.check_uvars);
       use_eq = (uu___448_13056.use_eq);
       is_iface = (uu___448_13056.is_iface);
       admit = (uu___448_13056.admit);
       lax = (uu___448_13056.lax);
       lax_universes = (uu___448_13056.lax_universes);
       phase1 = (uu___448_13056.phase1);
       failhard = (uu___448_13056.failhard);
       nosynth = (uu___448_13056.nosynth);
       uvar_subtyping = (uu___448_13056.uvar_subtyping);
       tc_term = (uu___448_13056.tc_term);
       type_of = (uu___448_13056.type_of);
       universe_of = (uu___448_13056.universe_of);
       check_type_of = (uu___448_13056.check_type_of);
       use_bv_sorts = (uu___448_13056.use_bv_sorts);
       qtbl_name_and_index = uu____13070;
       normalized_eff_names = uu____13170;
       fv_delta_depths = uu____13173;
       proof_ns = (uu___448_13056.proof_ns);
       synth_hook = (uu___448_13056.synth_hook);
       splice = (uu___448_13056.splice);
       postprocess = (uu___448_13056.postprocess);
       is_native_tactic = (uu___448_13056.is_native_tactic);
       identifier_info = uu____13176;
       tc_hooks = (uu___448_13056.tc_hooks);
       dsenv = (uu___448_13056.dsenv);
       nbe = (uu___448_13056.nbe)
     })
  
let (pop_stack : unit -> env) =
  fun uu____13204  ->
    let uu____13205 = FStar_ST.op_Bang stack  in
    match uu____13205 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____13259 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int * env)) =
  fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t = (Prims.int * Prims.int * solver_depth_t * Prims.int)
let (snapshot : env -> Prims.string -> (tcenv_depth_t * env)) =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____13349  ->
           let uu____13350 = snapshot_stack env  in
           match uu____13350 with
           | (stack_depth,env1) ->
               let uu____13384 = snapshot_query_indices ()  in
               (match uu____13384 with
                | (query_indices_depth,()) ->
                    let uu____13417 = (env1.solver).snapshot msg  in
                    (match uu____13417 with
                     | (solver_depth,()) ->
                         let uu____13474 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____13474 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___473_13541 = env1  in
                                 {
                                   solver = (uu___473_13541.solver);
                                   range = (uu___473_13541.range);
                                   curmodule = (uu___473_13541.curmodule);
                                   gamma = (uu___473_13541.gamma);
                                   gamma_sig = (uu___473_13541.gamma_sig);
                                   gamma_cache = (uu___473_13541.gamma_cache);
                                   modules = (uu___473_13541.modules);
                                   expected_typ =
                                     (uu___473_13541.expected_typ);
                                   sigtab = (uu___473_13541.sigtab);
                                   attrtab = (uu___473_13541.attrtab);
                                   is_pattern = (uu___473_13541.is_pattern);
                                   instantiate_imp =
                                     (uu___473_13541.instantiate_imp);
                                   effects = (uu___473_13541.effects);
                                   generalize = (uu___473_13541.generalize);
                                   letrecs = (uu___473_13541.letrecs);
                                   top_level = (uu___473_13541.top_level);
                                   check_uvars = (uu___473_13541.check_uvars);
                                   use_eq = (uu___473_13541.use_eq);
                                   is_iface = (uu___473_13541.is_iface);
                                   admit = (uu___473_13541.admit);
                                   lax = (uu___473_13541.lax);
                                   lax_universes =
                                     (uu___473_13541.lax_universes);
                                   phase1 = (uu___473_13541.phase1);
                                   failhard = (uu___473_13541.failhard);
                                   nosynth = (uu___473_13541.nosynth);
                                   uvar_subtyping =
                                     (uu___473_13541.uvar_subtyping);
                                   tc_term = (uu___473_13541.tc_term);
                                   type_of = (uu___473_13541.type_of);
                                   universe_of = (uu___473_13541.universe_of);
                                   check_type_of =
                                     (uu___473_13541.check_type_of);
                                   use_bv_sorts =
                                     (uu___473_13541.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___473_13541.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___473_13541.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___473_13541.fv_delta_depths);
                                   proof_ns = (uu___473_13541.proof_ns);
                                   synth_hook = (uu___473_13541.synth_hook);
                                   splice = (uu___473_13541.splice);
                                   postprocess = (uu___473_13541.postprocess);
                                   is_native_tactic =
                                     (uu___473_13541.is_native_tactic);
                                   identifier_info =
                                     (uu___473_13541.identifier_info);
                                   tc_hooks = (uu___473_13541.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___473_13541.nbe)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____13575  ->
             let uu____13576 =
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
             match uu____13576 with
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
                             ((let uu____13756 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____13756
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____13772 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____13772
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____13804,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____13846 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____13876  ->
                  match uu____13876 with
                  | (m,uu____13884) -> FStar_Ident.lid_equals l m))
           in
        (match uu____13846 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___518_13899 = env  in
               {
                 solver = (uu___518_13899.solver);
                 range = (uu___518_13899.range);
                 curmodule = (uu___518_13899.curmodule);
                 gamma = (uu___518_13899.gamma);
                 gamma_sig = (uu___518_13899.gamma_sig);
                 gamma_cache = (uu___518_13899.gamma_cache);
                 modules = (uu___518_13899.modules);
                 expected_typ = (uu___518_13899.expected_typ);
                 sigtab = (uu___518_13899.sigtab);
                 attrtab = (uu___518_13899.attrtab);
                 is_pattern = (uu___518_13899.is_pattern);
                 instantiate_imp = (uu___518_13899.instantiate_imp);
                 effects = (uu___518_13899.effects);
                 generalize = (uu___518_13899.generalize);
                 letrecs = (uu___518_13899.letrecs);
                 top_level = (uu___518_13899.top_level);
                 check_uvars = (uu___518_13899.check_uvars);
                 use_eq = (uu___518_13899.use_eq);
                 is_iface = (uu___518_13899.is_iface);
                 admit = (uu___518_13899.admit);
                 lax = (uu___518_13899.lax);
                 lax_universes = (uu___518_13899.lax_universes);
                 phase1 = (uu___518_13899.phase1);
                 failhard = (uu___518_13899.failhard);
                 nosynth = (uu___518_13899.nosynth);
                 uvar_subtyping = (uu___518_13899.uvar_subtyping);
                 tc_term = (uu___518_13899.tc_term);
                 type_of = (uu___518_13899.type_of);
                 universe_of = (uu___518_13899.universe_of);
                 check_type_of = (uu___518_13899.check_type_of);
                 use_bv_sorts = (uu___518_13899.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___518_13899.normalized_eff_names);
                 fv_delta_depths = (uu___518_13899.fv_delta_depths);
                 proof_ns = (uu___518_13899.proof_ns);
                 synth_hook = (uu___518_13899.synth_hook);
                 splice = (uu___518_13899.splice);
                 postprocess = (uu___518_13899.postprocess);
                 is_native_tactic = (uu___518_13899.is_native_tactic);
                 identifier_info = (uu___518_13899.identifier_info);
                 tc_hooks = (uu___518_13899.tc_hooks);
                 dsenv = (uu___518_13899.dsenv);
                 nbe = (uu___518_13899.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____13916,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___527_13932 = env  in
               {
                 solver = (uu___527_13932.solver);
                 range = (uu___527_13932.range);
                 curmodule = (uu___527_13932.curmodule);
                 gamma = (uu___527_13932.gamma);
                 gamma_sig = (uu___527_13932.gamma_sig);
                 gamma_cache = (uu___527_13932.gamma_cache);
                 modules = (uu___527_13932.modules);
                 expected_typ = (uu___527_13932.expected_typ);
                 sigtab = (uu___527_13932.sigtab);
                 attrtab = (uu___527_13932.attrtab);
                 is_pattern = (uu___527_13932.is_pattern);
                 instantiate_imp = (uu___527_13932.instantiate_imp);
                 effects = (uu___527_13932.effects);
                 generalize = (uu___527_13932.generalize);
                 letrecs = (uu___527_13932.letrecs);
                 top_level = (uu___527_13932.top_level);
                 check_uvars = (uu___527_13932.check_uvars);
                 use_eq = (uu___527_13932.use_eq);
                 is_iface = (uu___527_13932.is_iface);
                 admit = (uu___527_13932.admit);
                 lax = (uu___527_13932.lax);
                 lax_universes = (uu___527_13932.lax_universes);
                 phase1 = (uu___527_13932.phase1);
                 failhard = (uu___527_13932.failhard);
                 nosynth = (uu___527_13932.nosynth);
                 uvar_subtyping = (uu___527_13932.uvar_subtyping);
                 tc_term = (uu___527_13932.tc_term);
                 type_of = (uu___527_13932.type_of);
                 universe_of = (uu___527_13932.universe_of);
                 check_type_of = (uu___527_13932.check_type_of);
                 use_bv_sorts = (uu___527_13932.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___527_13932.normalized_eff_names);
                 fv_delta_depths = (uu___527_13932.fv_delta_depths);
                 proof_ns = (uu___527_13932.proof_ns);
                 synth_hook = (uu___527_13932.synth_hook);
                 splice = (uu___527_13932.splice);
                 postprocess = (uu___527_13932.postprocess);
                 is_native_tactic = (uu___527_13932.is_native_tactic);
                 identifier_info = (uu___527_13932.identifier_info);
                 tc_hooks = (uu___527_13932.tc_hooks);
                 dsenv = (uu___527_13932.dsenv);
                 nbe = (uu___527_13932.nbe)
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
        (let uu___534_13975 = e  in
         {
           solver = (uu___534_13975.solver);
           range = r;
           curmodule = (uu___534_13975.curmodule);
           gamma = (uu___534_13975.gamma);
           gamma_sig = (uu___534_13975.gamma_sig);
           gamma_cache = (uu___534_13975.gamma_cache);
           modules = (uu___534_13975.modules);
           expected_typ = (uu___534_13975.expected_typ);
           sigtab = (uu___534_13975.sigtab);
           attrtab = (uu___534_13975.attrtab);
           is_pattern = (uu___534_13975.is_pattern);
           instantiate_imp = (uu___534_13975.instantiate_imp);
           effects = (uu___534_13975.effects);
           generalize = (uu___534_13975.generalize);
           letrecs = (uu___534_13975.letrecs);
           top_level = (uu___534_13975.top_level);
           check_uvars = (uu___534_13975.check_uvars);
           use_eq = (uu___534_13975.use_eq);
           is_iface = (uu___534_13975.is_iface);
           admit = (uu___534_13975.admit);
           lax = (uu___534_13975.lax);
           lax_universes = (uu___534_13975.lax_universes);
           phase1 = (uu___534_13975.phase1);
           failhard = (uu___534_13975.failhard);
           nosynth = (uu___534_13975.nosynth);
           uvar_subtyping = (uu___534_13975.uvar_subtyping);
           tc_term = (uu___534_13975.tc_term);
           type_of = (uu___534_13975.type_of);
           universe_of = (uu___534_13975.universe_of);
           check_type_of = (uu___534_13975.check_type_of);
           use_bv_sorts = (uu___534_13975.use_bv_sorts);
           qtbl_name_and_index = (uu___534_13975.qtbl_name_and_index);
           normalized_eff_names = (uu___534_13975.normalized_eff_names);
           fv_delta_depths = (uu___534_13975.fv_delta_depths);
           proof_ns = (uu___534_13975.proof_ns);
           synth_hook = (uu___534_13975.synth_hook);
           splice = (uu___534_13975.splice);
           postprocess = (uu___534_13975.postprocess);
           is_native_tactic = (uu___534_13975.is_native_tactic);
           identifier_info = (uu___534_13975.identifier_info);
           tc_hooks = (uu___534_13975.tc_hooks);
           dsenv = (uu___534_13975.dsenv);
           nbe = (uu___534_13975.nbe)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____13995 =
        let uu____13996 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____13996 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____13995
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____14051 =
          let uu____14052 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____14052 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14051
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____14107 =
          let uu____14108 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____14108 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____14107
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____14163 =
        let uu____14164 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____14164 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____14163
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___551_14228 = env  in
      {
        solver = (uu___551_14228.solver);
        range = (uu___551_14228.range);
        curmodule = lid;
        gamma = (uu___551_14228.gamma);
        gamma_sig = (uu___551_14228.gamma_sig);
        gamma_cache = (uu___551_14228.gamma_cache);
        modules = (uu___551_14228.modules);
        expected_typ = (uu___551_14228.expected_typ);
        sigtab = (uu___551_14228.sigtab);
        attrtab = (uu___551_14228.attrtab);
        is_pattern = (uu___551_14228.is_pattern);
        instantiate_imp = (uu___551_14228.instantiate_imp);
        effects = (uu___551_14228.effects);
        generalize = (uu___551_14228.generalize);
        letrecs = (uu___551_14228.letrecs);
        top_level = (uu___551_14228.top_level);
        check_uvars = (uu___551_14228.check_uvars);
        use_eq = (uu___551_14228.use_eq);
        is_iface = (uu___551_14228.is_iface);
        admit = (uu___551_14228.admit);
        lax = (uu___551_14228.lax);
        lax_universes = (uu___551_14228.lax_universes);
        phase1 = (uu___551_14228.phase1);
        failhard = (uu___551_14228.failhard);
        nosynth = (uu___551_14228.nosynth);
        uvar_subtyping = (uu___551_14228.uvar_subtyping);
        tc_term = (uu___551_14228.tc_term);
        type_of = (uu___551_14228.type_of);
        universe_of = (uu___551_14228.universe_of);
        check_type_of = (uu___551_14228.check_type_of);
        use_bv_sorts = (uu___551_14228.use_bv_sorts);
        qtbl_name_and_index = (uu___551_14228.qtbl_name_and_index);
        normalized_eff_names = (uu___551_14228.normalized_eff_names);
        fv_delta_depths = (uu___551_14228.fv_delta_depths);
        proof_ns = (uu___551_14228.proof_ns);
        synth_hook = (uu___551_14228.synth_hook);
        splice = (uu___551_14228.splice);
        postprocess = (uu___551_14228.postprocess);
        is_native_tactic = (uu___551_14228.is_native_tactic);
        identifier_info = (uu___551_14228.identifier_info);
        tc_hooks = (uu___551_14228.tc_hooks);
        dsenv = (uu___551_14228.dsenv);
        nbe = (uu___551_14228.nbe)
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
      let uu____14259 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____14259
  
let (name_not_found :
  FStar_Ident.lid -> (FStar_Errors.raw_error * Prims.string)) =
  fun l  ->
    let uu____14272 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____14272)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv -> (FStar_Errors.raw_error * Prims.string)) =
  fun v1  ->
    let uu____14287 =
      let uu____14289 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____14289  in
    (FStar_Errors.Fatal_VariableNotFound, uu____14287)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____14298  ->
    let uu____14299 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____14299
  
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
      | ((formals,t),uu____14399) ->
          let vs = mk_univ_subst formals us  in
          let uu____14423 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____14423)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun uu___2_14440  ->
    match uu___2_14440 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____14466  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term))
  =
  fun r  ->
    fun t  ->
      let uu____14486 = inst_tscheme t  in
      match uu____14486 with
      | (us,t1) ->
          let uu____14497 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____14497)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____14518  ->
          match uu____14518 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____14540 =
                         let uu____14542 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____14546 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____14550 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____14552 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____14542 uu____14546 uu____14550 uu____14552
                          in
                       failwith uu____14540)
                    else ();
                    (let uu____14557 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____14557))
               | uu____14566 ->
                   let uu____14567 =
                     let uu____14569 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____14569
                      in
                   failwith uu____14567)
  
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____14581 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____14592 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____14603 -> false
  
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
             | ([],uu____14651) -> Maybe
             | (uu____14658,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____14678 -> No  in
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
          let uu____14772 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____14772 with
          | FStar_Pervasives_Native.None  ->
              let uu____14795 =
                FStar_Util.find_map env.gamma
                  (fun uu___3_14839  ->
                     match uu___3_14839 with
                     | FStar_Syntax_Syntax.Binding_lid (l,t) ->
                         let uu____14878 = FStar_Ident.lid_equals lid l  in
                         if uu____14878
                         then
                           let uu____14901 =
                             let uu____14920 =
                               let uu____14935 = inst_tscheme t  in
                               FStar_Util.Inl uu____14935  in
                             let uu____14950 = FStar_Ident.range_of_lid l  in
                             (uu____14920, uu____14950)  in
                           FStar_Pervasives_Native.Some uu____14901
                         else FStar_Pervasives_Native.None
                     | uu____15003 -> FStar_Pervasives_Native.None)
                 in
              FStar_Util.catch_opt uu____14795
                (fun uu____15041  ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___4_15050  ->
                        match uu___4_15050 with
                        | (uu____15053,{
                                         FStar_Syntax_Syntax.sigel =
                                           FStar_Syntax_Syntax.Sig_bundle
                                           (ses,uu____15055);
                                         FStar_Syntax_Syntax.sigrng =
                                           uu____15056;
                                         FStar_Syntax_Syntax.sigquals =
                                           uu____15057;
                                         FStar_Syntax_Syntax.sigmeta =
                                           uu____15058;
                                         FStar_Syntax_Syntax.sigattrs =
                                           uu____15059;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se  ->
                                 let uu____15079 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid))
                                    in
                                 if uu____15079
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
                                  uu____15131 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____15138 -> cache t  in
                            let uu____15139 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids
                               in
                            (match uu____15139 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____15145 =
                                   let uu____15146 =
                                     FStar_Ident.range_of_lid l  in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____15146)
                                    in
                                 maybe_cache uu____15145)))
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____15217 = find_in_sigtab env lid  in
         match uu____15217 with
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
      let uu____15298 = lookup_qname env lid  in
      match uu____15298 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____15319,rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se,us),rng) ->
          FStar_Pervasives_Native.Some se
  
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env  ->
    fun attr  ->
      let uu____15433 = FStar_Util.smap_try_find (attrtab env) attr  in
      match uu____15433 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None  -> []
  
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let add_one1 env1 se1 attr =
        let uu____15478 =
          let uu____15481 = lookup_attr env1 attr  in se1 :: uu____15481  in
        FStar_Util.smap_add (attrtab env1) attr uu____15478  in
      FStar_List.iter
        (fun attr  ->
           let uu____15491 =
             let uu____15492 = FStar_Syntax_Subst.compress attr  in
             uu____15492.FStar_Syntax_Syntax.n  in
           match uu____15491 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____15496 =
                 let uu____15498 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 uu____15498.FStar_Ident.str  in
               add_one1 env se uu____15496
           | uu____15499 -> ()) se.FStar_Syntax_Syntax.sigattrs
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15522) ->
          add_sigelts env ses
      | uu____15531 ->
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
            | uu____15546 -> ()))

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
        (fun uu___5_15578  ->
           match uu___5_15578 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____15596 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____15658,lb::[]),uu____15660) ->
            let uu____15669 =
              let uu____15678 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____15687 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____15678, uu____15687)  in
            FStar_Pervasives_Native.Some uu____15669
        | FStar_Syntax_Syntax.Sig_let ((uu____15700,lbs),uu____15702) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____15734 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____15747 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____15747
                     then
                       let uu____15760 =
                         let uu____15769 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____15778 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____15769, uu____15778)  in
                       FStar_Pervasives_Native.Some uu____15760
                     else FStar_Pervasives_Native.None)
        | uu____15801 -> FStar_Pervasives_Native.None
  
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
          let uu____15861 =
            let uu____15870 =
              let uu____15875 =
                let uu____15876 =
                  let uu____15879 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____15879
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____15876)  in
              inst_tscheme1 uu____15875  in
            (uu____15870, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15861
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____15901,uu____15902) ->
          let uu____15907 =
            let uu____15916 =
              let uu____15921 =
                let uu____15922 =
                  let uu____15925 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____15925  in
                (us, uu____15922)  in
              inst_tscheme1 uu____15921  in
            (uu____15916, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____15907
      | uu____15944 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____16033 =
          match uu____16033 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____16129,uvs,t,uu____16132,uu____16133,uu____16134);
                      FStar_Syntax_Syntax.sigrng = uu____16135;
                      FStar_Syntax_Syntax.sigquals = uu____16136;
                      FStar_Syntax_Syntax.sigmeta = uu____16137;
                      FStar_Syntax_Syntax.sigattrs = uu____16138;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16161 =
                     let uu____16170 = inst_tscheme1 (uvs, t)  in
                     (uu____16170, rng)  in
                   FStar_Pervasives_Native.Some uu____16161
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____16194;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____16196;
                      FStar_Syntax_Syntax.sigattrs = uu____16197;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____16214 =
                     let uu____16216 = in_cur_mod env l  in uu____16216 = Yes
                      in
                   if uu____16214
                   then
                     let uu____16228 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____16228
                      then
                        let uu____16244 =
                          let uu____16253 = inst_tscheme1 (uvs, t)  in
                          (uu____16253, rng)  in
                        FStar_Pervasives_Native.Some uu____16244
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____16286 =
                        let uu____16295 = inst_tscheme1 (uvs, t)  in
                        (uu____16295, rng)  in
                      FStar_Pervasives_Native.Some uu____16286)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16320,uu____16321);
                      FStar_Syntax_Syntax.sigrng = uu____16322;
                      FStar_Syntax_Syntax.sigquals = uu____16323;
                      FStar_Syntax_Syntax.sigmeta = uu____16324;
                      FStar_Syntax_Syntax.sigattrs = uu____16325;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____16366 =
                          let uu____16375 = inst_tscheme1 (uvs, k)  in
                          (uu____16375, rng)  in
                        FStar_Pervasives_Native.Some uu____16366
                    | uu____16396 ->
                        let uu____16397 =
                          let uu____16406 =
                            let uu____16411 =
                              let uu____16412 =
                                let uu____16415 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16415
                                 in
                              (uvs, uu____16412)  in
                            inst_tscheme1 uu____16411  in
                          (uu____16406, rng)  in
                        FStar_Pervasives_Native.Some uu____16397)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____16438,uu____16439);
                      FStar_Syntax_Syntax.sigrng = uu____16440;
                      FStar_Syntax_Syntax.sigquals = uu____16441;
                      FStar_Syntax_Syntax.sigmeta = uu____16442;
                      FStar_Syntax_Syntax.sigattrs = uu____16443;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____16485 =
                          let uu____16494 = inst_tscheme_with (uvs, k) us  in
                          (uu____16494, rng)  in
                        FStar_Pervasives_Native.Some uu____16485
                    | uu____16515 ->
                        let uu____16516 =
                          let uu____16525 =
                            let uu____16530 =
                              let uu____16531 =
                                let uu____16534 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____16534
                                 in
                              (uvs, uu____16531)  in
                            inst_tscheme_with uu____16530 us  in
                          (uu____16525, rng)  in
                        FStar_Pervasives_Native.Some uu____16516)
               | FStar_Util.Inr se ->
                   let uu____16570 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____16591;
                          FStar_Syntax_Syntax.sigrng = uu____16592;
                          FStar_Syntax_Syntax.sigquals = uu____16593;
                          FStar_Syntax_Syntax.sigmeta = uu____16594;
                          FStar_Syntax_Syntax.sigattrs = uu____16595;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____16610 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____16570
                     (FStar_Util.map_option
                        (fun uu____16658  ->
                           match uu____16658 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____16689 =
          let uu____16700 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____16700 mapper  in
        match uu____16689 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____16774 =
              let uu____16785 =
                let uu____16792 =
                  let uu___878_16795 = t  in
                  let uu____16796 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___878_16795.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____16796;
                    FStar_Syntax_Syntax.vars =
                      (uu___878_16795.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____16792)  in
              (uu____16785, r)  in
            FStar_Pervasives_Native.Some uu____16774
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____16845 = lookup_qname env l  in
      match uu____16845 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____16866 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv -> (FStar_Syntax_Syntax.typ * FStar_Range.range))
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____16920 = try_lookup_bv env bv  in
      match uu____16920 with
      | FStar_Pervasives_Native.None  ->
          let uu____16935 = variable_not_found bv  in
          FStar_Errors.raise_error uu____16935 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____16951 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____16952 =
            let uu____16953 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____16953  in
          (uu____16951, uu____16952)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____16975 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____16975 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____17041 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____17041  in
          let uu____17042 =
            let uu____17051 =
              let uu____17056 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____17056)  in
            (uu____17051, r1)  in
          FStar_Pervasives_Native.Some uu____17042
  
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
        let uu____17091 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____17091 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____17124,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____17149 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____17149  in
            let uu____17150 =
              let uu____17155 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____17155, r1)  in
            FStar_Pervasives_Native.Some uu____17150
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) *
        FStar_Range.range))
  =
  fun env  ->
    fun l  ->
      let uu____17179 = try_lookup_lid env l  in
      match uu____17179 with
      | FStar_Pervasives_Native.None  ->
          let uu____17206 = name_not_found l  in
          let uu____17212 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____17206 uu____17212
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___6_17255  ->
              match uu___6_17255 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____17259 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier
        Prims.list) FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____17280 = lookup_qname env lid  in
      match uu____17280 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17289,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17292;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____17294;
              FStar_Syntax_Syntax.sigattrs = uu____17295;_},FStar_Pervasives_Native.None
            ),uu____17296)
          ->
          let uu____17345 =
            let uu____17352 =
              let uu____17353 =
                let uu____17356 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____17356 t  in
              (uvs, uu____17353)  in
            (uu____17352, q)  in
          FStar_Pervasives_Native.Some uu____17345
      | uu____17369 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17391 = lookup_qname env lid  in
      match uu____17391 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____17396,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____17399;
              FStar_Syntax_Syntax.sigquals = uu____17400;
              FStar_Syntax_Syntax.sigmeta = uu____17401;
              FStar_Syntax_Syntax.sigattrs = uu____17402;_},FStar_Pervasives_Native.None
            ),uu____17403)
          ->
          let uu____17452 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17452 (uvs, t)
      | uu____17457 ->
          let uu____17458 = name_not_found lid  in
          let uu____17464 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17458 uu____17464
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun lid  ->
      let uu____17484 = lookup_qname env lid  in
      match uu____17484 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17489,uvs,t,uu____17492,uu____17493,uu____17494);
              FStar_Syntax_Syntax.sigrng = uu____17495;
              FStar_Syntax_Syntax.sigquals = uu____17496;
              FStar_Syntax_Syntax.sigmeta = uu____17497;
              FStar_Syntax_Syntax.sigattrs = uu____17498;_},FStar_Pervasives_Native.None
            ),uu____17499)
          ->
          let uu____17554 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____17554 (uvs, t)
      | uu____17559 ->
          let uu____17560 = name_not_found lid  in
          let uu____17566 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____17560 uu____17566
  
let (datacons_of_typ :
  env -> FStar_Ident.lident -> (Prims.bool * FStar_Ident.lident Prims.list))
  =
  fun env  ->
    fun lid  ->
      let uu____17589 = lookup_qname env lid  in
      match uu____17589 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17597,uu____17598,uu____17599,uu____17600,uu____17601,dcs);
              FStar_Syntax_Syntax.sigrng = uu____17603;
              FStar_Syntax_Syntax.sigquals = uu____17604;
              FStar_Syntax_Syntax.sigmeta = uu____17605;
              FStar_Syntax_Syntax.sigattrs = uu____17606;_},uu____17607),uu____17608)
          -> (true, dcs)
      | uu____17671 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____17687 = lookup_qname env lid  in
      match uu____17687 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____17688,uu____17689,uu____17690,l,uu____17692,uu____17693);
              FStar_Syntax_Syntax.sigrng = uu____17694;
              FStar_Syntax_Syntax.sigquals = uu____17695;
              FStar_Syntax_Syntax.sigmeta = uu____17696;
              FStar_Syntax_Syntax.sigattrs = uu____17697;_},uu____17698),uu____17699)
          -> l
      | uu____17756 ->
          let uu____17757 =
            let uu____17759 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____17759  in
          failwith uu____17757
  
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
              (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____17829)
              ->
              (match se.FStar_Syntax_Syntax.sigel with
               | FStar_Syntax_Syntax.Sig_let ((is_rec,lbs),uu____17886) when
                   (visible se.FStar_Syntax_Syntax.sigquals) &&
                     ((Prims.op_Negation is_rec) || rec_ok)
                   ->
                   FStar_Util.find_map lbs
                     (fun lb  ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        let uu____17910 =
                          FStar_Syntax_Syntax.fv_eq_lid fv lid  in
                        if uu____17910
                        then
                          FStar_Pervasives_Native.Some
                            ((lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbdef))
                        else FStar_Pervasives_Native.None)
               | uu____17945 -> FStar_Pervasives_Native.None)
          | uu____17954 -> FStar_Pervasives_Native.None
  
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
        let uu____18016 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____18016
  
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
        let uu____18049 = lookup_qname env lid  in
        FStar_All.pipe_left
          (lookup_definition_qninfo_aux false delta_levels lid) uu____18049
  
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
             (FStar_Util.Inl uu____18101,uu____18102) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se,uu____18151),uu____18152) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____18201 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____18219 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____18229 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____18246 ->
                  let uu____18253 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals
                     in
                  FStar_Pervasives_Native.Some uu____18253
              | FStar_Syntax_Syntax.Sig_let ((uu____18254,lbs),uu____18256)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb  ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       let uu____18272 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid  in
                       if uu____18272
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____18279 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____18287 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____18288 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____18295 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____18296 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____18297 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____18298 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____18311 ->
                  FStar_Pervasives_Native.None))
  
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env  ->
    fun fv  ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____18329 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths)
            in
         FStar_All.pipe_right uu____18329
           (fun d_opt  ->
              let uu____18342 = FStar_All.pipe_right d_opt FStar_Util.is_some
                 in
              if uu____18342
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____18352 =
                   let uu____18355 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   delta_depth_of_qninfo fv uu____18355  in
                 match uu____18352 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____18356 =
                       let uu____18358 = FStar_Syntax_Print.fv_to_string fv
                          in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____18358
                        in
                     failwith uu____18356
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____18363 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____18363
                       then
                         let uu____18366 = FStar_Syntax_Print.fv_to_string fv
                            in
                         let uu____18368 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta
                            in
                         let uu____18370 =
                           FStar_Syntax_Print.delta_depth_to_string d  in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____18366 uu____18368 uu____18370
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
        (FStar_Util.Inr (se,uu____18395),uu____18396) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____18445 -> FStar_Pervasives_Native.None
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____18467),uu____18468) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____18517 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____18539 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____18539
  
let (fv_with_lid_has_attr :
  env -> FStar_Ident.lid -> FStar_Ident.lid -> Prims.bool) =
  fun env  ->
    fun fv_lid1  ->
      fun attr_lid  ->
        let uu____18562 = lookup_attrs_of_lid env fv_lid1  in
        match uu____18562 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some [] -> false
        | FStar_Pervasives_Native.Some attrs ->
            FStar_All.pipe_right attrs
              (FStar_Util.for_some
                 (fun tm  ->
                    let uu____18586 =
                      let uu____18587 = FStar_Syntax_Util.un_uinst tm  in
                      uu____18587.FStar_Syntax_Syntax.n  in
                    match uu____18586 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_Syntax_Syntax.fv_eq_lid fv attr_lid
                    | uu____18592 -> false))
  
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
      let uu____18626 = lookup_qname env ftv  in
      match uu____18626 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____18630) ->
          let uu____18675 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____18675 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____18696,t),r) ->
               let uu____18711 =
                 let uu____18712 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____18712 t  in
               FStar_Pervasives_Native.Some uu____18711)
      | uu____18713 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____18725 = try_lookup_effect_lid env ftv  in
      match uu____18725 with
      | FStar_Pervasives_Native.None  ->
          let uu____18728 = name_not_found ftv  in
          let uu____18734 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____18728 uu____18734
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
        let uu____18758 = lookup_qname env lid0  in
        match uu____18758 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____18769);
                FStar_Syntax_Syntax.sigrng = uu____18770;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____18772;
                FStar_Syntax_Syntax.sigattrs = uu____18773;_},FStar_Pervasives_Native.None
              ),uu____18774)
            ->
            let lid1 =
              let uu____18828 =
                let uu____18829 = FStar_Ident.range_of_lid lid  in
                let uu____18830 =
                  let uu____18831 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____18831  in
                FStar_Range.set_use_range uu____18829 uu____18830  in
              FStar_Ident.set_lid_range lid uu____18828  in
            let uu____18832 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___7_18838  ->
                      match uu___7_18838 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____18841 -> false))
               in
            if uu____18832
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____18860 =
                      let uu____18862 =
                        let uu____18864 = get_range env  in
                        FStar_Range.string_of_range uu____18864  in
                      let uu____18865 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____18867 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____18862 uu____18865 uu____18867
                       in
                    failwith uu____18860)
                  in
               match (binders, univs1) with
               | ([],uu____18888) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____18914,uu____18915::uu____18916::uu____18917) ->
                   let uu____18938 =
                     let uu____18940 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____18942 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____18940 uu____18942
                      in
                   failwith uu____18938
               | uu____18953 ->
                   let uu____18968 =
                     let uu____18973 =
                       let uu____18974 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____18974)  in
                     inst_tscheme_with uu____18973 insts  in
                   (match uu____18968 with
                    | (uu____18987,t) ->
                        let t1 =
                          let uu____18990 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____18990 t  in
                        let uu____18991 =
                          let uu____18992 = FStar_Syntax_Subst.compress t1
                             in
                          uu____18992.FStar_Syntax_Syntax.n  in
                        (match uu____18991 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____19027 -> failwith "Impossible")))
        | uu____19035 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____19059 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____19059 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____19072,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____19079 = find1 l2  in
            (match uu____19079 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____19086 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____19086 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____19090 = find1 l  in
            (match uu____19090 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____19095 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____19095
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____19110 = lookup_qname env l1  in
      match uu____19110 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____19113;
              FStar_Syntax_Syntax.sigrng = uu____19114;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____19116;
              FStar_Syntax_Syntax.sigattrs = uu____19117;_},uu____19118),uu____19119)
          -> q
      | uu____19170 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____19194 =
          let uu____19195 =
            let uu____19197 = FStar_Util.string_of_int i  in
            let uu____19199 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____19197 uu____19199
             in
          failwith uu____19195  in
        let uu____19202 = lookup_datacon env lid  in
        match uu____19202 with
        | (uu____19207,t) ->
            let uu____19209 =
              let uu____19210 = FStar_Syntax_Subst.compress t  in
              uu____19210.FStar_Syntax_Syntax.n  in
            (match uu____19209 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____19214) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____19258 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____19258
                      FStar_Pervasives_Native.fst)
             | uu____19269 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19283 = lookup_qname env l  in
      match uu____19283 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____19285,uu____19286,uu____19287);
              FStar_Syntax_Syntax.sigrng = uu____19288;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19290;
              FStar_Syntax_Syntax.sigattrs = uu____19291;_},uu____19292),uu____19293)
          ->
          FStar_Util.for_some
            (fun uu___8_19346  ->
               match uu___8_19346 with
               | FStar_Syntax_Syntax.Projector uu____19348 -> true
               | uu____19354 -> false) quals
      | uu____19356 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19370 = lookup_qname env lid  in
      match uu____19370 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____19372,uu____19373,uu____19374,uu____19375,uu____19376,uu____19377);
              FStar_Syntax_Syntax.sigrng = uu____19378;
              FStar_Syntax_Syntax.sigquals = uu____19379;
              FStar_Syntax_Syntax.sigmeta = uu____19380;
              FStar_Syntax_Syntax.sigattrs = uu____19381;_},uu____19382),uu____19383)
          -> true
      | uu____19441 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19455 = lookup_qname env lid  in
      match uu____19455 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19457,uu____19458,uu____19459,uu____19460,uu____19461,uu____19462);
              FStar_Syntax_Syntax.sigrng = uu____19463;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____19465;
              FStar_Syntax_Syntax.sigattrs = uu____19466;_},uu____19467),uu____19468)
          ->
          FStar_Util.for_some
            (fun uu___9_19529  ->
               match uu___9_19529 with
               | FStar_Syntax_Syntax.RecordType uu____19531 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____19541 -> true
               | uu____19551 -> false) quals
      | uu____19553 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____19563,uu____19564);
            FStar_Syntax_Syntax.sigrng = uu____19565;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____19567;
            FStar_Syntax_Syntax.sigattrs = uu____19568;_},uu____19569),uu____19570)
        ->
        FStar_Util.for_some
          (fun uu___10_19627  ->
             match uu___10_19627 with
             | FStar_Syntax_Syntax.Action uu____19629 -> true
             | uu____19631 -> false) quals
    | uu____19633 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____19647 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____19647
  
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
      let uu____19664 =
        let uu____19665 = FStar_Syntax_Util.un_uinst head1  in
        uu____19665.FStar_Syntax_Syntax.n  in
      match uu____19664 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____19671 ->
               true
           | uu____19674 -> false)
      | uu____19676 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____19690 = lookup_qname env l  in
      match uu____19690 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____19693),uu____19694) ->
          FStar_Util.for_some
            (fun uu___11_19742  ->
               match uu___11_19742 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____19745 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____19747 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____19823 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____19841) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____19859 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____19867 ->
                 FStar_Pervasives_Native.Some true
             | uu____19886 -> FStar_Pervasives_Native.Some false)
         in
      let uu____19889 =
        let uu____19893 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____19893 mapper  in
      match uu____19889 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env  ->
    fun lid  ->
      let uu____19953 = lookup_qname env lid  in
      match uu____19953 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____19957,uu____19958,tps,uu____19960,uu____19961,uu____19962);
              FStar_Syntax_Syntax.sigrng = uu____19963;
              FStar_Syntax_Syntax.sigquals = uu____19964;
              FStar_Syntax_Syntax.sigmeta = uu____19965;
              FStar_Syntax_Syntax.sigattrs = uu____19966;_},uu____19967),uu____19968)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____20034 -> FStar_Pervasives_Native.None
  
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
           (fun uu____20080  ->
              match uu____20080 with
              | (d,uu____20089) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____20105 = effect_decl_opt env l  in
      match uu____20105 with
      | FStar_Pervasives_Native.None  ->
          let uu____20120 = name_not_found l  in
          let uu____20126 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____20120 uu____20126
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____20149  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____20168  ->
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
        let uu____20200 = FStar_Ident.lid_equals l1 l2  in
        if uu____20200
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____20211 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____20211
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____20222 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____20275  ->
                        match uu____20275 with
                        | (m1,m2,uu____20289,uu____20290,uu____20291) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____20222 with
              | FStar_Pervasives_Native.None  ->
                  let uu____20308 =
                    let uu____20314 =
                      let uu____20316 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____20318 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____20316
                        uu____20318
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____20314)
                     in
                  FStar_Errors.raise_error uu____20308 env.range
              | FStar_Pervasives_Native.Some
                  (uu____20328,uu____20329,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____20363 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____20363
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
  'Auu____20383 .
    (FStar_Syntax_Syntax.eff_decl * 'Auu____20383) Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax)
  =
  fun decls  ->
    fun m  ->
      let uu____20412 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____20438  ->
                match uu____20438 with
                | (d,uu____20445) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____20412 with
      | FStar_Pervasives_Native.None  ->
          let uu____20456 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____20456
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____20471 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____20471 with
           | (uu____20486,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____20504)::(wp,uu____20506)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____20562 -> failwith "Impossible"))
  
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
          let uu____20620 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____20620
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____20625 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____20625
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
                  let uu____20636 = get_range env  in
                  let uu____20637 =
                    let uu____20644 =
                      let uu____20645 =
                        let uu____20662 =
                          let uu____20673 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____20673]  in
                        (null_wp, uu____20662)  in
                      FStar_Syntax_Syntax.Tm_app uu____20645  in
                    FStar_Syntax_Syntax.mk uu____20644  in
                  uu____20637 FStar_Pervasives_Native.None uu____20636  in
                let uu____20710 =
                  let uu____20711 =
                    let uu____20722 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____20722]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____20711;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____20710))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___1532_20760 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___1532_20760.order);
              joins = (uu___1532_20760.joins)
            }  in
          let uu___1535_20769 = env  in
          {
            solver = (uu___1535_20769.solver);
            range = (uu___1535_20769.range);
            curmodule = (uu___1535_20769.curmodule);
            gamma = (uu___1535_20769.gamma);
            gamma_sig = (uu___1535_20769.gamma_sig);
            gamma_cache = (uu___1535_20769.gamma_cache);
            modules = (uu___1535_20769.modules);
            expected_typ = (uu___1535_20769.expected_typ);
            sigtab = (uu___1535_20769.sigtab);
            attrtab = (uu___1535_20769.attrtab);
            is_pattern = (uu___1535_20769.is_pattern);
            instantiate_imp = (uu___1535_20769.instantiate_imp);
            effects;
            generalize = (uu___1535_20769.generalize);
            letrecs = (uu___1535_20769.letrecs);
            top_level = (uu___1535_20769.top_level);
            check_uvars = (uu___1535_20769.check_uvars);
            use_eq = (uu___1535_20769.use_eq);
            is_iface = (uu___1535_20769.is_iface);
            admit = (uu___1535_20769.admit);
            lax = (uu___1535_20769.lax);
            lax_universes = (uu___1535_20769.lax_universes);
            phase1 = (uu___1535_20769.phase1);
            failhard = (uu___1535_20769.failhard);
            nosynth = (uu___1535_20769.nosynth);
            uvar_subtyping = (uu___1535_20769.uvar_subtyping);
            tc_term = (uu___1535_20769.tc_term);
            type_of = (uu___1535_20769.type_of);
            universe_of = (uu___1535_20769.universe_of);
            check_type_of = (uu___1535_20769.check_type_of);
            use_bv_sorts = (uu___1535_20769.use_bv_sorts);
            qtbl_name_and_index = (uu___1535_20769.qtbl_name_and_index);
            normalized_eff_names = (uu___1535_20769.normalized_eff_names);
            fv_delta_depths = (uu___1535_20769.fv_delta_depths);
            proof_ns = (uu___1535_20769.proof_ns);
            synth_hook = (uu___1535_20769.synth_hook);
            splice = (uu___1535_20769.splice);
            postprocess = (uu___1535_20769.postprocess);
            is_native_tactic = (uu___1535_20769.is_native_tactic);
            identifier_info = (uu___1535_20769.identifier_info);
            tc_hooks = (uu___1535_20769.tc_hooks);
            dsenv = (uu___1535_20769.dsenv);
            nbe = (uu___1535_20769.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____20799 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____20799  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____20957 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____20958 = l1 u t wp e  in
                                l2 u t uu____20957 uu____20958))
                | uu____20959 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____21031 = inst_tscheme_with lift_t [u]  in
            match uu____21031 with
            | (uu____21038,lift_t1) ->
                let uu____21040 =
                  let uu____21047 =
                    let uu____21048 =
                      let uu____21065 =
                        let uu____21076 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21085 =
                          let uu____21096 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____21096]  in
                        uu____21076 :: uu____21085  in
                      (lift_t1, uu____21065)  in
                    FStar_Syntax_Syntax.Tm_app uu____21048  in
                  FStar_Syntax_Syntax.mk uu____21047  in
                uu____21040 FStar_Pervasives_Native.None
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
            let uu____21206 = inst_tscheme_with lift_t [u]  in
            match uu____21206 with
            | (uu____21213,lift_t1) ->
                let uu____21215 =
                  let uu____21222 =
                    let uu____21223 =
                      let uu____21240 =
                        let uu____21251 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____21260 =
                          let uu____21271 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____21280 =
                            let uu____21291 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____21291]  in
                          uu____21271 :: uu____21280  in
                        uu____21251 :: uu____21260  in
                      (lift_t1, uu____21240)  in
                    FStar_Syntax_Syntax.Tm_app uu____21223  in
                  FStar_Syntax_Syntax.mk uu____21222  in
                uu____21215 FStar_Pervasives_Native.None
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
              let uu____21393 =
                let uu____21394 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____21394
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____21393  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____21403 =
              let uu____21405 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____21405  in
            let uu____21406 =
              let uu____21408 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____21436 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____21436)
                 in
              FStar_Util.dflt "none" uu____21408  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____21403
              uu____21406
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____21465  ->
                    match uu____21465 with
                    | (e,uu____21473) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____21496 =
            match uu____21496 with
            | (i,j) ->
                let uu____21507 = FStar_Ident.lid_equals i j  in
                if uu____21507
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _21514  -> FStar_Pervasives_Native.Some _21514)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____21543 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____21553 = FStar_Ident.lid_equals i k  in
                        if uu____21553
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____21567 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____21567
                                  then []
                                  else
                                    (let uu____21574 =
                                       let uu____21583 =
                                         find_edge order1 (i, k)  in
                                       let uu____21586 =
                                         find_edge order1 (k, j)  in
                                       (uu____21583, uu____21586)  in
                                     match uu____21574 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____21601 =
                                           compose_edges e1 e2  in
                                         [uu____21601]
                                     | uu____21602 -> [])))))
                 in
              FStar_List.append order1 uu____21543  in
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
                   let uu____21632 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____21635 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____21635
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____21632
                   then
                     let uu____21642 =
                       let uu____21648 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____21648)
                        in
                     let uu____21652 = get_range env  in
                     FStar_Errors.raise_error uu____21642 uu____21652
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____21730 = FStar_Ident.lid_equals i j
                                   in
                                if uu____21730
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____21782 =
                                              let uu____21791 =
                                                find_edge order2 (i, k)  in
                                              let uu____21794 =
                                                find_edge order2 (j, k)  in
                                              (uu____21791, uu____21794)  in
                                            match uu____21782 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____21836,uu____21837)
                                                     ->
                                                     let uu____21844 =
                                                       let uu____21851 =
                                                         let uu____21853 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21853
                                                          in
                                                       let uu____21856 =
                                                         let uu____21858 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____21858
                                                          in
                                                       (uu____21851,
                                                         uu____21856)
                                                        in
                                                     (match uu____21844 with
                                                      | (true ,true ) ->
                                                          let uu____21875 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____21875
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
                                            | uu____21918 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___1662_21991 = env.effects  in
              { decls = (uu___1662_21991.decls); order = order2; joins }  in
            let uu___1665_21992 = env  in
            {
              solver = (uu___1665_21992.solver);
              range = (uu___1665_21992.range);
              curmodule = (uu___1665_21992.curmodule);
              gamma = (uu___1665_21992.gamma);
              gamma_sig = (uu___1665_21992.gamma_sig);
              gamma_cache = (uu___1665_21992.gamma_cache);
              modules = (uu___1665_21992.modules);
              expected_typ = (uu___1665_21992.expected_typ);
              sigtab = (uu___1665_21992.sigtab);
              attrtab = (uu___1665_21992.attrtab);
              is_pattern = (uu___1665_21992.is_pattern);
              instantiate_imp = (uu___1665_21992.instantiate_imp);
              effects;
              generalize = (uu___1665_21992.generalize);
              letrecs = (uu___1665_21992.letrecs);
              top_level = (uu___1665_21992.top_level);
              check_uvars = (uu___1665_21992.check_uvars);
              use_eq = (uu___1665_21992.use_eq);
              is_iface = (uu___1665_21992.is_iface);
              admit = (uu___1665_21992.admit);
              lax = (uu___1665_21992.lax);
              lax_universes = (uu___1665_21992.lax_universes);
              phase1 = (uu___1665_21992.phase1);
              failhard = (uu___1665_21992.failhard);
              nosynth = (uu___1665_21992.nosynth);
              uvar_subtyping = (uu___1665_21992.uvar_subtyping);
              tc_term = (uu___1665_21992.tc_term);
              type_of = (uu___1665_21992.type_of);
              universe_of = (uu___1665_21992.universe_of);
              check_type_of = (uu___1665_21992.check_type_of);
              use_bv_sorts = (uu___1665_21992.use_bv_sorts);
              qtbl_name_and_index = (uu___1665_21992.qtbl_name_and_index);
              normalized_eff_names = (uu___1665_21992.normalized_eff_names);
              fv_delta_depths = (uu___1665_21992.fv_delta_depths);
              proof_ns = (uu___1665_21992.proof_ns);
              synth_hook = (uu___1665_21992.synth_hook);
              splice = (uu___1665_21992.splice);
              postprocess = (uu___1665_21992.postprocess);
              is_native_tactic = (uu___1665_21992.is_native_tactic);
              identifier_info = (uu___1665_21992.identifier_info);
              tc_hooks = (uu___1665_21992.tc_hooks);
              dsenv = (uu___1665_21992.dsenv);
              nbe = (uu___1665_21992.nbe)
            }))
      | uu____21993 -> env
  
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
        | uu____22022 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____22035 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____22035 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____22052 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____22052 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____22077 =
                     let uu____22083 =
                       let uu____22085 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____22093 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____22104 =
                         let uu____22106 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____22106  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____22085 uu____22093 uu____22104
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____22083)
                      in
                   FStar_Errors.raise_error uu____22077
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____22114 =
                     let uu____22125 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____22125 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____22162  ->
                        fun uu____22163  ->
                          match (uu____22162, uu____22163) with
                          | ((x,uu____22193),(t,uu____22195)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____22114
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____22226 =
                     let uu___1703_22227 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___1703_22227.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___1703_22227.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___1703_22227.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___1703_22227.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____22226
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
let effect_repr_aux :
  'Auu____22239 .
    'Auu____22239 ->
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
          let uu____22269 = effect_decl_opt env effect_name  in
          match uu____22269 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown  ->
                   FStar_Pervasives_Native.None
               | uu____22308 ->
                   let c1 = unfold_effect_abbrev env c  in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____22331 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name  in
                         let message =
                           let uu____22370 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name
                              in
                           Prims.op_Hat uu____22370
                             (Prims.op_Hat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].")
                            in
                         let uu____22375 = get_range env  in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____22375
                      in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr))
                      in
                   let uu____22390 =
                     let uu____22393 = get_range env  in
                     let uu____22394 =
                       let uu____22401 =
                         let uu____22402 =
                           let uu____22419 =
                             let uu____22430 =
                               FStar_Syntax_Syntax.as_arg res_typ  in
                             [uu____22430; wp]  in
                           (repr, uu____22419)  in
                         FStar_Syntax_Syntax.Tm_app uu____22402  in
                       FStar_Syntax_Syntax.mk uu____22401  in
                     uu____22394 FStar_Pervasives_Native.None uu____22393  in
                   FStar_Pervasives_Native.Some uu____22390)
  
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
      | uu____22574 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____22589 =
        let uu____22590 = FStar_Syntax_Subst.compress t  in
        uu____22590.FStar_Syntax_Syntax.n  in
      match uu____22589 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____22594,c) ->
          is_reifiable_comp env c
      | uu____22616 -> false
  
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let l = FStar_Syntax_Util.comp_effect_name c  in
        (let uu____22636 =
           let uu____22638 = is_reifiable_effect env l  in
           Prims.op_Negation uu____22638  in
         if uu____22636
         then
           let uu____22641 =
             let uu____22647 =
               let uu____22649 = FStar_Ident.string_of_lid l  in
               FStar_Util.format1 "Effect %s cannot be reified" uu____22649
                in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____22647)  in
           let uu____22653 = get_range env  in
           FStar_Errors.raise_error uu____22641 uu____22653
         else ());
        (let uu____22656 = effect_repr_aux true env c u_c  in
         match uu____22656 with
         | FStar_Pervasives_Native.None  ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s)  in
      let env1 =
        let uu___1768_22692 = env  in
        {
          solver = (uu___1768_22692.solver);
          range = (uu___1768_22692.range);
          curmodule = (uu___1768_22692.curmodule);
          gamma = (uu___1768_22692.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___1768_22692.gamma_cache);
          modules = (uu___1768_22692.modules);
          expected_typ = (uu___1768_22692.expected_typ);
          sigtab = (uu___1768_22692.sigtab);
          attrtab = (uu___1768_22692.attrtab);
          is_pattern = (uu___1768_22692.is_pattern);
          instantiate_imp = (uu___1768_22692.instantiate_imp);
          effects = (uu___1768_22692.effects);
          generalize = (uu___1768_22692.generalize);
          letrecs = (uu___1768_22692.letrecs);
          top_level = (uu___1768_22692.top_level);
          check_uvars = (uu___1768_22692.check_uvars);
          use_eq = (uu___1768_22692.use_eq);
          is_iface = (uu___1768_22692.is_iface);
          admit = (uu___1768_22692.admit);
          lax = (uu___1768_22692.lax);
          lax_universes = (uu___1768_22692.lax_universes);
          phase1 = (uu___1768_22692.phase1);
          failhard = (uu___1768_22692.failhard);
          nosynth = (uu___1768_22692.nosynth);
          uvar_subtyping = (uu___1768_22692.uvar_subtyping);
          tc_term = (uu___1768_22692.tc_term);
          type_of = (uu___1768_22692.type_of);
          universe_of = (uu___1768_22692.universe_of);
          check_type_of = (uu___1768_22692.check_type_of);
          use_bv_sorts = (uu___1768_22692.use_bv_sorts);
          qtbl_name_and_index = (uu___1768_22692.qtbl_name_and_index);
          normalized_eff_names = (uu___1768_22692.normalized_eff_names);
          fv_delta_depths = (uu___1768_22692.fv_delta_depths);
          proof_ns = (uu___1768_22692.proof_ns);
          synth_hook = (uu___1768_22692.synth_hook);
          splice = (uu___1768_22692.splice);
          postprocess = (uu___1768_22692.postprocess);
          is_native_tactic = (uu___1768_22692.is_native_tactic);
          identifier_info = (uu___1768_22692.identifier_info);
          tc_hooks = (uu___1768_22692.tc_hooks);
          dsenv = (uu___1768_22692.dsenv);
          nbe = (uu___1768_22692.nbe)
        }  in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
  
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env  ->
    fun b  ->
      let uu___1775_22706 = env  in
      {
        solver = (uu___1775_22706.solver);
        range = (uu___1775_22706.range);
        curmodule = (uu___1775_22706.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___1775_22706.gamma_sig);
        gamma_cache = (uu___1775_22706.gamma_cache);
        modules = (uu___1775_22706.modules);
        expected_typ = (uu___1775_22706.expected_typ);
        sigtab = (uu___1775_22706.sigtab);
        attrtab = (uu___1775_22706.attrtab);
        is_pattern = (uu___1775_22706.is_pattern);
        instantiate_imp = (uu___1775_22706.instantiate_imp);
        effects = (uu___1775_22706.effects);
        generalize = (uu___1775_22706.generalize);
        letrecs = (uu___1775_22706.letrecs);
        top_level = (uu___1775_22706.top_level);
        check_uvars = (uu___1775_22706.check_uvars);
        use_eq = (uu___1775_22706.use_eq);
        is_iface = (uu___1775_22706.is_iface);
        admit = (uu___1775_22706.admit);
        lax = (uu___1775_22706.lax);
        lax_universes = (uu___1775_22706.lax_universes);
        phase1 = (uu___1775_22706.phase1);
        failhard = (uu___1775_22706.failhard);
        nosynth = (uu___1775_22706.nosynth);
        uvar_subtyping = (uu___1775_22706.uvar_subtyping);
        tc_term = (uu___1775_22706.tc_term);
        type_of = (uu___1775_22706.type_of);
        universe_of = (uu___1775_22706.universe_of);
        check_type_of = (uu___1775_22706.check_type_of);
        use_bv_sorts = (uu___1775_22706.use_bv_sorts);
        qtbl_name_and_index = (uu___1775_22706.qtbl_name_and_index);
        normalized_eff_names = (uu___1775_22706.normalized_eff_names);
        fv_delta_depths = (uu___1775_22706.fv_delta_depths);
        proof_ns = (uu___1775_22706.proof_ns);
        synth_hook = (uu___1775_22706.synth_hook);
        splice = (uu___1775_22706.splice);
        postprocess = (uu___1775_22706.postprocess);
        is_native_tactic = (uu___1775_22706.is_native_tactic);
        identifier_info = (uu___1775_22706.identifier_info);
        tc_hooks = (uu___1775_22706.tc_hooks);
        dsenv = (uu___1775_22706.dsenv);
        nbe = (uu___1775_22706.nbe)
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
            (let uu___1788_22764 = env  in
             {
               solver = (uu___1788_22764.solver);
               range = (uu___1788_22764.range);
               curmodule = (uu___1788_22764.curmodule);
               gamma = rest;
               gamma_sig = (uu___1788_22764.gamma_sig);
               gamma_cache = (uu___1788_22764.gamma_cache);
               modules = (uu___1788_22764.modules);
               expected_typ = (uu___1788_22764.expected_typ);
               sigtab = (uu___1788_22764.sigtab);
               attrtab = (uu___1788_22764.attrtab);
               is_pattern = (uu___1788_22764.is_pattern);
               instantiate_imp = (uu___1788_22764.instantiate_imp);
               effects = (uu___1788_22764.effects);
               generalize = (uu___1788_22764.generalize);
               letrecs = (uu___1788_22764.letrecs);
               top_level = (uu___1788_22764.top_level);
               check_uvars = (uu___1788_22764.check_uvars);
               use_eq = (uu___1788_22764.use_eq);
               is_iface = (uu___1788_22764.is_iface);
               admit = (uu___1788_22764.admit);
               lax = (uu___1788_22764.lax);
               lax_universes = (uu___1788_22764.lax_universes);
               phase1 = (uu___1788_22764.phase1);
               failhard = (uu___1788_22764.failhard);
               nosynth = (uu___1788_22764.nosynth);
               uvar_subtyping = (uu___1788_22764.uvar_subtyping);
               tc_term = (uu___1788_22764.tc_term);
               type_of = (uu___1788_22764.type_of);
               universe_of = (uu___1788_22764.universe_of);
               check_type_of = (uu___1788_22764.check_type_of);
               use_bv_sorts = (uu___1788_22764.use_bv_sorts);
               qtbl_name_and_index = (uu___1788_22764.qtbl_name_and_index);
               normalized_eff_names = (uu___1788_22764.normalized_eff_names);
               fv_delta_depths = (uu___1788_22764.fv_delta_depths);
               proof_ns = (uu___1788_22764.proof_ns);
               synth_hook = (uu___1788_22764.synth_hook);
               splice = (uu___1788_22764.splice);
               postprocess = (uu___1788_22764.postprocess);
               is_native_tactic = (uu___1788_22764.is_native_tactic);
               identifier_info = (uu___1788_22764.identifier_info);
               tc_hooks = (uu___1788_22764.tc_hooks);
               dsenv = (uu___1788_22764.dsenv);
               nbe = (uu___1788_22764.nbe)
             }))
    | uu____22765 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____22794  ->
             match uu____22794 with | (x,uu____22802) -> push_bv env1 x) env
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
            let uu___1802_22837 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___1802_22837.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___1802_22837.FStar_Syntax_Syntax.index);
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
      (let uu___1813_22879 = env  in
       {
         solver = (uu___1813_22879.solver);
         range = (uu___1813_22879.range);
         curmodule = (uu___1813_22879.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1813_22879.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___1813_22879.sigtab);
         attrtab = (uu___1813_22879.attrtab);
         is_pattern = (uu___1813_22879.is_pattern);
         instantiate_imp = (uu___1813_22879.instantiate_imp);
         effects = (uu___1813_22879.effects);
         generalize = (uu___1813_22879.generalize);
         letrecs = (uu___1813_22879.letrecs);
         top_level = (uu___1813_22879.top_level);
         check_uvars = (uu___1813_22879.check_uvars);
         use_eq = (uu___1813_22879.use_eq);
         is_iface = (uu___1813_22879.is_iface);
         admit = (uu___1813_22879.admit);
         lax = (uu___1813_22879.lax);
         lax_universes = (uu___1813_22879.lax_universes);
         phase1 = (uu___1813_22879.phase1);
         failhard = (uu___1813_22879.failhard);
         nosynth = (uu___1813_22879.nosynth);
         uvar_subtyping = (uu___1813_22879.uvar_subtyping);
         tc_term = (uu___1813_22879.tc_term);
         type_of = (uu___1813_22879.type_of);
         universe_of = (uu___1813_22879.universe_of);
         check_type_of = (uu___1813_22879.check_type_of);
         use_bv_sorts = (uu___1813_22879.use_bv_sorts);
         qtbl_name_and_index = (uu___1813_22879.qtbl_name_and_index);
         normalized_eff_names = (uu___1813_22879.normalized_eff_names);
         fv_delta_depths = (uu___1813_22879.fv_delta_depths);
         proof_ns = (uu___1813_22879.proof_ns);
         synth_hook = (uu___1813_22879.synth_hook);
         splice = (uu___1813_22879.splice);
         postprocess = (uu___1813_22879.postprocess);
         is_native_tactic = (uu___1813_22879.is_native_tactic);
         identifier_info = (uu___1813_22879.identifier_info);
         tc_hooks = (uu___1813_22879.tc_hooks);
         dsenv = (uu___1813_22879.dsenv);
         nbe = (uu___1813_22879.nbe)
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
        let uu____22923 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____22923 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____22951 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____22951)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___1828_22967 = env  in
      {
        solver = (uu___1828_22967.solver);
        range = (uu___1828_22967.range);
        curmodule = (uu___1828_22967.curmodule);
        gamma = (uu___1828_22967.gamma);
        gamma_sig = (uu___1828_22967.gamma_sig);
        gamma_cache = (uu___1828_22967.gamma_cache);
        modules = (uu___1828_22967.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___1828_22967.sigtab);
        attrtab = (uu___1828_22967.attrtab);
        is_pattern = (uu___1828_22967.is_pattern);
        instantiate_imp = (uu___1828_22967.instantiate_imp);
        effects = (uu___1828_22967.effects);
        generalize = (uu___1828_22967.generalize);
        letrecs = (uu___1828_22967.letrecs);
        top_level = (uu___1828_22967.top_level);
        check_uvars = (uu___1828_22967.check_uvars);
        use_eq = false;
        is_iface = (uu___1828_22967.is_iface);
        admit = (uu___1828_22967.admit);
        lax = (uu___1828_22967.lax);
        lax_universes = (uu___1828_22967.lax_universes);
        phase1 = (uu___1828_22967.phase1);
        failhard = (uu___1828_22967.failhard);
        nosynth = (uu___1828_22967.nosynth);
        uvar_subtyping = (uu___1828_22967.uvar_subtyping);
        tc_term = (uu___1828_22967.tc_term);
        type_of = (uu___1828_22967.type_of);
        universe_of = (uu___1828_22967.universe_of);
        check_type_of = (uu___1828_22967.check_type_of);
        use_bv_sorts = (uu___1828_22967.use_bv_sorts);
        qtbl_name_and_index = (uu___1828_22967.qtbl_name_and_index);
        normalized_eff_names = (uu___1828_22967.normalized_eff_names);
        fv_delta_depths = (uu___1828_22967.fv_delta_depths);
        proof_ns = (uu___1828_22967.proof_ns);
        synth_hook = (uu___1828_22967.synth_hook);
        splice = (uu___1828_22967.splice);
        postprocess = (uu___1828_22967.postprocess);
        is_native_tactic = (uu___1828_22967.is_native_tactic);
        identifier_info = (uu___1828_22967.identifier_info);
        tc_hooks = (uu___1828_22967.tc_hooks);
        dsenv = (uu___1828_22967.dsenv);
        nbe = (uu___1828_22967.nbe)
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
    let uu____22998 = expected_typ env_  in
    ((let uu___1835_23004 = env_  in
      {
        solver = (uu___1835_23004.solver);
        range = (uu___1835_23004.range);
        curmodule = (uu___1835_23004.curmodule);
        gamma = (uu___1835_23004.gamma);
        gamma_sig = (uu___1835_23004.gamma_sig);
        gamma_cache = (uu___1835_23004.gamma_cache);
        modules = (uu___1835_23004.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___1835_23004.sigtab);
        attrtab = (uu___1835_23004.attrtab);
        is_pattern = (uu___1835_23004.is_pattern);
        instantiate_imp = (uu___1835_23004.instantiate_imp);
        effects = (uu___1835_23004.effects);
        generalize = (uu___1835_23004.generalize);
        letrecs = (uu___1835_23004.letrecs);
        top_level = (uu___1835_23004.top_level);
        check_uvars = (uu___1835_23004.check_uvars);
        use_eq = false;
        is_iface = (uu___1835_23004.is_iface);
        admit = (uu___1835_23004.admit);
        lax = (uu___1835_23004.lax);
        lax_universes = (uu___1835_23004.lax_universes);
        phase1 = (uu___1835_23004.phase1);
        failhard = (uu___1835_23004.failhard);
        nosynth = (uu___1835_23004.nosynth);
        uvar_subtyping = (uu___1835_23004.uvar_subtyping);
        tc_term = (uu___1835_23004.tc_term);
        type_of = (uu___1835_23004.type_of);
        universe_of = (uu___1835_23004.universe_of);
        check_type_of = (uu___1835_23004.check_type_of);
        use_bv_sorts = (uu___1835_23004.use_bv_sorts);
        qtbl_name_and_index = (uu___1835_23004.qtbl_name_and_index);
        normalized_eff_names = (uu___1835_23004.normalized_eff_names);
        fv_delta_depths = (uu___1835_23004.fv_delta_depths);
        proof_ns = (uu___1835_23004.proof_ns);
        synth_hook = (uu___1835_23004.synth_hook);
        splice = (uu___1835_23004.splice);
        postprocess = (uu___1835_23004.postprocess);
        is_native_tactic = (uu___1835_23004.is_native_tactic);
        identifier_info = (uu___1835_23004.identifier_info);
        tc_hooks = (uu___1835_23004.tc_hooks);
        dsenv = (uu___1835_23004.dsenv);
        nbe = (uu___1835_23004.nbe)
      }), uu____22998)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____23016 =
      let uu____23019 = FStar_Ident.id_of_text ""  in [uu____23019]  in
    FStar_Ident.lid_of_ids uu____23016  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____23026 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____23026
        then
          let uu____23031 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd)
             in
          FStar_All.pipe_right uu____23031 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___1843_23059 = env  in
       {
         solver = (uu___1843_23059.solver);
         range = (uu___1843_23059.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___1843_23059.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___1843_23059.expected_typ);
         sigtab = (uu___1843_23059.sigtab);
         attrtab = (uu___1843_23059.attrtab);
         is_pattern = (uu___1843_23059.is_pattern);
         instantiate_imp = (uu___1843_23059.instantiate_imp);
         effects = (uu___1843_23059.effects);
         generalize = (uu___1843_23059.generalize);
         letrecs = (uu___1843_23059.letrecs);
         top_level = (uu___1843_23059.top_level);
         check_uvars = (uu___1843_23059.check_uvars);
         use_eq = (uu___1843_23059.use_eq);
         is_iface = (uu___1843_23059.is_iface);
         admit = (uu___1843_23059.admit);
         lax = (uu___1843_23059.lax);
         lax_universes = (uu___1843_23059.lax_universes);
         phase1 = (uu___1843_23059.phase1);
         failhard = (uu___1843_23059.failhard);
         nosynth = (uu___1843_23059.nosynth);
         uvar_subtyping = (uu___1843_23059.uvar_subtyping);
         tc_term = (uu___1843_23059.tc_term);
         type_of = (uu___1843_23059.type_of);
         universe_of = (uu___1843_23059.universe_of);
         check_type_of = (uu___1843_23059.check_type_of);
         use_bv_sorts = (uu___1843_23059.use_bv_sorts);
         qtbl_name_and_index = (uu___1843_23059.qtbl_name_and_index);
         normalized_eff_names = (uu___1843_23059.normalized_eff_names);
         fv_delta_depths = (uu___1843_23059.fv_delta_depths);
         proof_ns = (uu___1843_23059.proof_ns);
         synth_hook = (uu___1843_23059.synth_hook);
         splice = (uu___1843_23059.splice);
         postprocess = (uu___1843_23059.postprocess);
         is_native_tactic = (uu___1843_23059.is_native_tactic);
         identifier_info = (uu___1843_23059.identifier_info);
         tc_hooks = (uu___1843_23059.tc_hooks);
         dsenv = (uu___1843_23059.dsenv);
         nbe = (uu___1843_23059.nbe)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23111)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23115,(uu____23116,t)))::tl1
          ->
          let uu____23137 =
            let uu____23140 = FStar_Syntax_Free.uvars t  in
            ext out uu____23140  in
          aux uu____23137 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23143;
            FStar_Syntax_Syntax.index = uu____23144;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23152 =
            let uu____23155 = FStar_Syntax_Free.uvars t  in
            ext out uu____23155  in
          aux uu____23152 tl1
       in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____23213)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23217,(uu____23218,t)))::tl1
          ->
          let uu____23239 =
            let uu____23242 = FStar_Syntax_Free.univs t  in
            ext out uu____23242  in
          aux uu____23239 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23245;
            FStar_Syntax_Syntax.index = uu____23246;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23254 =
            let uu____23257 = FStar_Syntax_Free.univs t  in
            ext out uu____23257  in
          aux uu____23254 tl1
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
          let uu____23319 = FStar_Util.set_add uname out  in
          aux uu____23319 tl1
      | (FStar_Syntax_Syntax.Binding_lid (uu____23322,(uu____23323,t)))::tl1
          ->
          let uu____23344 =
            let uu____23347 = FStar_Syntax_Free.univnames t  in
            ext out uu____23347  in
          aux uu____23344 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____23350;
            FStar_Syntax_Syntax.index = uu____23351;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____23359 =
            let uu____23362 = FStar_Syntax_Free.univnames t  in
            ext out uu____23362  in
          aux uu____23359 tl1
       in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___12_23383  ->
            match uu___12_23383 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____23387 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____23400 -> []))
  
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs  ->
    let uu____23411 =
      let uu____23420 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____23420
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____23411 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma  ->
    let uu____23468 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___13_23481  ->
              match uu___13_23481 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____23484 = FStar_Syntax_Print.bv_to_string x  in
                  Prims.op_Hat "Binding_var " uu____23484
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.op_Hat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l,uu____23490) ->
                  let uu____23507 = FStar_Ident.string_of_lid l  in
                  Prims.op_Hat "Binding_lid " uu____23507))
       in
    FStar_All.pipe_right uu____23468 (FStar_String.concat "::\n")
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___14_23521  ->
    match uu___14_23521 with
    | NoDelta  -> "NoDelta"
    | InliningDelta  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____23527 = FStar_Syntax_Print.delta_depth_to_string d  in
        Prims.op_Hat "Unfold " uu____23527
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____23550  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec str_i_prefix xs ys =
        match (xs, ys) with
        | ([],uu____23605) -> true
        | (x::xs1,y::ys1) ->
            ((FStar_String.lowercase x) = (FStar_String.lowercase y)) &&
              (str_i_prefix xs1 ys1)
        | (uu____23638,uu____23639) -> false  in
      let uu____23653 =
        FStar_List.tryFind
          (fun uu____23675  ->
             match uu____23675 with | (p,uu____23686) -> str_i_prefix p path)
          env.proof_ns
         in
      match uu____23653 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____23705,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____23735 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____23735
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___1986_23757 = e  in
        {
          solver = (uu___1986_23757.solver);
          range = (uu___1986_23757.range);
          curmodule = (uu___1986_23757.curmodule);
          gamma = (uu___1986_23757.gamma);
          gamma_sig = (uu___1986_23757.gamma_sig);
          gamma_cache = (uu___1986_23757.gamma_cache);
          modules = (uu___1986_23757.modules);
          expected_typ = (uu___1986_23757.expected_typ);
          sigtab = (uu___1986_23757.sigtab);
          attrtab = (uu___1986_23757.attrtab);
          is_pattern = (uu___1986_23757.is_pattern);
          instantiate_imp = (uu___1986_23757.instantiate_imp);
          effects = (uu___1986_23757.effects);
          generalize = (uu___1986_23757.generalize);
          letrecs = (uu___1986_23757.letrecs);
          top_level = (uu___1986_23757.top_level);
          check_uvars = (uu___1986_23757.check_uvars);
          use_eq = (uu___1986_23757.use_eq);
          is_iface = (uu___1986_23757.is_iface);
          admit = (uu___1986_23757.admit);
          lax = (uu___1986_23757.lax);
          lax_universes = (uu___1986_23757.lax_universes);
          phase1 = (uu___1986_23757.phase1);
          failhard = (uu___1986_23757.failhard);
          nosynth = (uu___1986_23757.nosynth);
          uvar_subtyping = (uu___1986_23757.uvar_subtyping);
          tc_term = (uu___1986_23757.tc_term);
          type_of = (uu___1986_23757.type_of);
          universe_of = (uu___1986_23757.universe_of);
          check_type_of = (uu___1986_23757.check_type_of);
          use_bv_sorts = (uu___1986_23757.use_bv_sorts);
          qtbl_name_and_index = (uu___1986_23757.qtbl_name_and_index);
          normalized_eff_names = (uu___1986_23757.normalized_eff_names);
          fv_delta_depths = (uu___1986_23757.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___1986_23757.synth_hook);
          splice = (uu___1986_23757.splice);
          postprocess = (uu___1986_23757.postprocess);
          is_native_tactic = (uu___1986_23757.is_native_tactic);
          identifier_info = (uu___1986_23757.identifier_info);
          tc_hooks = (uu___1986_23757.tc_hooks);
          dsenv = (uu___1986_23757.dsenv);
          nbe = (uu___1986_23757.nbe)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___1995_23805 = e  in
      {
        solver = (uu___1995_23805.solver);
        range = (uu___1995_23805.range);
        curmodule = (uu___1995_23805.curmodule);
        gamma = (uu___1995_23805.gamma);
        gamma_sig = (uu___1995_23805.gamma_sig);
        gamma_cache = (uu___1995_23805.gamma_cache);
        modules = (uu___1995_23805.modules);
        expected_typ = (uu___1995_23805.expected_typ);
        sigtab = (uu___1995_23805.sigtab);
        attrtab = (uu___1995_23805.attrtab);
        is_pattern = (uu___1995_23805.is_pattern);
        instantiate_imp = (uu___1995_23805.instantiate_imp);
        effects = (uu___1995_23805.effects);
        generalize = (uu___1995_23805.generalize);
        letrecs = (uu___1995_23805.letrecs);
        top_level = (uu___1995_23805.top_level);
        check_uvars = (uu___1995_23805.check_uvars);
        use_eq = (uu___1995_23805.use_eq);
        is_iface = (uu___1995_23805.is_iface);
        admit = (uu___1995_23805.admit);
        lax = (uu___1995_23805.lax);
        lax_universes = (uu___1995_23805.lax_universes);
        phase1 = (uu___1995_23805.phase1);
        failhard = (uu___1995_23805.failhard);
        nosynth = (uu___1995_23805.nosynth);
        uvar_subtyping = (uu___1995_23805.uvar_subtyping);
        tc_term = (uu___1995_23805.tc_term);
        type_of = (uu___1995_23805.type_of);
        universe_of = (uu___1995_23805.universe_of);
        check_type_of = (uu___1995_23805.check_type_of);
        use_bv_sorts = (uu___1995_23805.use_bv_sorts);
        qtbl_name_and_index = (uu___1995_23805.qtbl_name_and_index);
        normalized_eff_names = (uu___1995_23805.normalized_eff_names);
        fv_delta_depths = (uu___1995_23805.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___1995_23805.synth_hook);
        splice = (uu___1995_23805.splice);
        postprocess = (uu___1995_23805.postprocess);
        is_native_tactic = (uu___1995_23805.is_native_tactic);
        identifier_info = (uu___1995_23805.identifier_info);
        tc_hooks = (uu___1995_23805.tc_hooks);
        dsenv = (uu___1995_23805.dsenv);
        nbe = (uu___1995_23805.nbe)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____23821 = FStar_Syntax_Free.names t  in
      let uu____23824 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____23821 uu____23824
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____23847 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____23847
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____23857 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____23857
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____23878 =
      match uu____23878 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____23898 = FStar_Ident.text_of_path p  in
             Prims.op_Hat (if b then "+" else "-") uu____23898)
       in
    let uu____23906 =
      let uu____23910 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____23910 FStar_List.rev  in
    FStar_All.pipe_right uu____23906 (FStar_String.concat " ")
  
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
                  (let uu____23980 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____23980 with
                   | FStar_Pervasives_Native.Some uu____23984 -> true
                   | FStar_Pervasives_Native.None  -> false)))
    | uu____23987 -> false
  
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial ; deferred = uu____23997;
        univ_ineqs = uu____23998; implicits = uu____23999;_} -> true
    | uu____24011 -> false
  
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
          let uu___2039_24042 = g  in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___2039_24042.deferred);
            univ_ineqs = (uu___2039_24042.univ_ineqs);
            implicits = (uu___2039_24042.implicits)
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
          let uu____24081 = FStar_Options.defensive ()  in
          if uu____24081
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____24087 =
              let uu____24089 =
                let uu____24091 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____24091  in
              Prims.op_Negation uu____24089  in
            (if uu____24087
             then
               let uu____24098 =
                 let uu____24104 =
                   let uu____24106 = FStar_Syntax_Print.term_to_string t  in
                   let uu____24108 =
                     let uu____24110 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____24110
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____24106 uu____24108
                    in
                 (FStar_Errors.Warning_Defensive, uu____24104)  in
               FStar_Errors.log_issue rng uu____24098
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
          let uu____24150 =
            let uu____24152 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24152  in
          if uu____24150
          then ()
          else
            (let uu____24157 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv  in
             def_check_vars_in_set rng msg uu____24157 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____24183 =
            let uu____24185 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____24185  in
          if uu____24183
          then ()
          else
            (let uu____24190 = bound_vars e  in
             def_check_closed_in rng msg uu____24190 t)
  
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
          let uu___2076_24229 = g  in
          let uu____24230 =
            let uu____24231 =
              let uu____24232 =
                let uu____24239 =
                  let uu____24240 =
                    let uu____24257 =
                      let uu____24268 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____24268]  in
                    (f, uu____24257)  in
                  FStar_Syntax_Syntax.Tm_app uu____24240  in
                FStar_Syntax_Syntax.mk uu____24239  in
              uu____24232 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _24305  -> FStar_TypeChecker_Common.NonTrivial _24305)
              uu____24231
             in
          {
            guard_f = uu____24230;
            deferred = (uu___2076_24229.deferred);
            univ_ineqs = (uu___2076_24229.univ_ineqs);
            implicits = (uu___2076_24229.implicits)
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
          let uu___2083_24323 = g  in
          let uu____24324 =
            let uu____24325 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24325  in
          {
            guard_f = uu____24324;
            deferred = (uu___2083_24323.deferred);
            univ_ineqs = (uu___2083_24323.univ_ineqs);
            implicits = (uu___2083_24323.implicits)
          }
  
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial  ->
          let uu___2088_24342 = g  in
          let uu____24343 =
            let uu____24344 = map1 FStar_Syntax_Util.t_true  in
            FStar_TypeChecker_Common.NonTrivial uu____24344  in
          {
            guard_f = uu____24343;
            deferred = (uu___2088_24342.deferred);
            univ_ineqs = (uu___2088_24342.univ_ineqs);
            implicits = (uu___2088_24342.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___2092_24346 = g  in
          let uu____24347 =
            let uu____24348 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____24348  in
          {
            guard_f = uu____24347;
            deferred = (uu___2092_24346.deferred);
            univ_ineqs = (uu___2092_24346.univ_ineqs);
            implicits = (uu___2092_24346.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____24355 ->
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
          let uu____24372 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____24372
  
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t  ->
    let uu____24379 =
      let uu____24380 = FStar_Syntax_Util.unmeta t  in
      uu____24380.FStar_Syntax_Syntax.n  in
    match uu____24379 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____24384 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____24427 = f g1.guard_f g2.guard_f  in
        {
          guard_f = uu____24427;
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
                       let uu____24522 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____24522
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___2147_24529 = g  in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___2147_24529.deferred);
              univ_ineqs = (uu___2147_24529.univ_ineqs);
              implicits = (uu___2147_24529.implicits)
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
               let uu____24563 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____24563
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
            let uu___2162_24590 = g  in
            let uu____24591 =
              let uu____24592 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____24592  in
            {
              guard_f = uu____24591;
              deferred = (uu___2162_24590.deferred);
              univ_ineqs = (uu___2162_24590.univ_ineqs);
              implicits = (uu___2162_24590.implicits)
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
              let uu____24650 =
                FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
                 in
              match uu____24650 with
              | FStar_Pervasives_Native.Some
                  (uu____24675::(tm,uu____24677)::[]) ->
                  let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_range
                            (tm.FStar_Syntax_Syntax.pos)))
                      FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                     in
                  (t, [], trivial_guard)
              | uu____24741 ->
                  let binders = all_binders env  in
                  let gamma = env.gamma  in
                  let ctx_uvar =
                    let uu____24759 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____24759;
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
                      let uu___2184_24791 = trivial_guard  in
                      {
                        guard_f = (uu___2184_24791.guard_f);
                        deferred = (uu___2184_24791.deferred);
                        univ_ineqs = (uu___2184_24791.univ_ineqs);
                        implicits = [imp]
                      }  in
                    (t, [(ctx_uvar, r)], g)))
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____24809  -> ());
    push = (fun uu____24811  -> ());
    pop = (fun uu____24814  -> ());
    snapshot =
      (fun uu____24817  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____24836  -> fun uu____24837  -> ());
    encode_sig = (fun uu____24852  -> fun uu____24853  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____24859 =
             let uu____24866 = FStar_Options.peek ()  in (e, g, uu____24866)
              in
           [uu____24859]);
    solve = (fun uu____24882  -> fun uu____24883  -> fun uu____24884  -> ());
    finish = (fun uu____24891  -> ());
    refresh = (fun uu____24893  -> ())
  } 