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
let (uu___is_Beta : step -> Prims.bool) =
  fun projectee -> match projectee with | Beta -> true | uu____37 -> false
let (uu___is_Iota : step -> Prims.bool) =
  fun projectee -> match projectee with | Iota -> true | uu____43 -> false
let (uu___is_Zeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Zeta -> true | uu____49 -> false
let (uu___is_Exclude : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Exclude _0 -> true | uu____56 -> false
let (__proj__Exclude__item___0 : step -> step) =
  fun projectee -> match projectee with | Exclude _0 -> _0
let (uu___is_Weak : step -> Prims.bool) =
  fun projectee -> match projectee with | Weak -> true | uu____69 -> false
let (uu___is_HNF : step -> Prims.bool) =
  fun projectee -> match projectee with | HNF -> true | uu____75 -> false
let (uu___is_Primops : step -> Prims.bool) =
  fun projectee -> match projectee with | Primops -> true | uu____81 -> false
let (uu___is_Eager_unfolding : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding -> true | uu____87 -> false
let (uu___is_Inlining : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Inlining -> true | uu____93 -> false
let (uu___is_DoNotUnfoldPureLets : step -> Prims.bool) =
  fun projectee ->
    match projectee with | DoNotUnfoldPureLets -> true | uu____99 -> false
let (uu___is_UnfoldUntil : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldUntil _0 -> true | uu____106 -> false
let (__proj__UnfoldUntil__item___0 : step -> FStar_Syntax_Syntax.delta_depth)
  = fun projectee -> match projectee with | UnfoldUntil _0 -> _0
let (uu___is_UnfoldOnly : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldOnly _0 -> true | uu____122 -> false
let (__proj__UnfoldOnly__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldOnly _0 -> _0
let (uu___is_UnfoldFully : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldFully _0 -> true | uu____144 -> false
let (__proj__UnfoldFully__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldFully _0 -> _0
let (uu___is_UnfoldAttr : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldAttr _0 -> true | uu____166 -> false
let (__proj__UnfoldAttr__item___0 : step -> FStar_Ident.lid Prims.list) =
  fun projectee -> match projectee with | UnfoldAttr _0 -> _0
let (uu___is_UnfoldTac : step -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldTac -> true | uu____185 -> false
let (uu___is_PureSubtermsWithinComputations : step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | PureSubtermsWithinComputations -> true
    | uu____191 -> false
let (uu___is_Simplify : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Simplify -> true | uu____197 -> false
let (uu___is_EraseUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | EraseUniverses -> true | uu____203 -> false
let (uu___is_AllowUnboundUniverses : step -> Prims.bool) =
  fun projectee ->
    match projectee with | AllowUnboundUniverses -> true | uu____209 -> false
let (uu___is_Reify : step -> Prims.bool) =
  fun projectee -> match projectee with | Reify -> true | uu____215 -> false
let (uu___is_CompressUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CompressUvars -> true | uu____221 -> false
let (uu___is_NoFullNorm : step -> Prims.bool) =
  fun projectee ->
    match projectee with | NoFullNorm -> true | uu____227 -> false
let (uu___is_CheckNoUvars : step -> Prims.bool) =
  fun projectee ->
    match projectee with | CheckNoUvars -> true | uu____233 -> false
let (uu___is_Unmeta : step -> Prims.bool) =
  fun projectee -> match projectee with | Unmeta -> true | uu____239 -> false
let (uu___is_Unascribe : step -> Prims.bool) =
  fun projectee ->
    match projectee with | Unascribe -> true | uu____245 -> false
let (uu___is_NBE : step -> Prims.bool) =
  fun projectee -> match projectee with | NBE -> true | uu____251 -> false
type steps = step Prims.list
let rec (eq_step : step -> step -> Prims.bool) =
  fun s1 ->
    fun s2 ->
      match (s1, s2) with
      | (Beta, Beta) -> true
      | (Iota, Iota) -> true
      | (Zeta, Zeta) -> true
      | (Weak, Weak) -> true
      | (HNF, HNF) -> true
      | (Primops, Primops) -> true
      | (Eager_unfolding, Eager_unfolding) -> true
      | (Inlining, Inlining) -> true
      | (DoNotUnfoldPureLets, DoNotUnfoldPureLets) -> true
      | (UnfoldTac, UnfoldTac) -> true
      | (PureSubtermsWithinComputations, PureSubtermsWithinComputations) ->
          true
      | (Simplify, Simplify) -> true
      | (EraseUniverses, EraseUniverses) -> true
      | (AllowUnboundUniverses, AllowUnboundUniverses) -> true
      | (Reify, Reify) -> true
      | (CompressUvars, CompressUvars) -> true
      | (NoFullNorm, NoFullNorm) -> true
      | (CheckNoUvars, CheckNoUvars) -> true
      | (Unmeta, Unmeta) -> true
      | (Unascribe, Unascribe) -> true
      | (NBE, NBE) -> true
      | (Exclude s11, Exclude s21) -> eq_step s11 s21
      | (UnfoldUntil s11, UnfoldUntil s21) -> s11 = s21
      | (UnfoldOnly lids1, UnfoldOnly lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldFully lids1, UnfoldFully lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | (UnfoldAttr lids1, UnfoldAttr lids2) ->
          ((FStar_List.length lids1) = (FStar_List.length lids2)) &&
            (FStar_List.forall2 FStar_Ident.lid_equals lids1 lids2)
      | uu____286 -> false
type sig_binding =
  (FStar_Ident.lident Prims.list, FStar_Syntax_Syntax.sigelt)
    FStar_Pervasives_Native.tuple2
type delta_level =
  | NoDelta 
  | InliningDelta 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | NoDelta -> true | uu____307 -> false
let (uu___is_InliningDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | InliningDelta -> true | uu____313 -> false
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding_only -> true | uu____319 -> false
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Unfold _0 -> true | uu____326 -> false
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee -> match projectee with | Unfold _0 -> _0
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
  fun projectee ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl, FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident, FStar_Ident.lident, FStar_Ident.lident, mlift,
      mlift) FStar_Pervasives_Native.tuple5 Prims.list
    }
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl, FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident, FStar_Ident.lident, FStar_Ident.lident, mlift,
      mlift) FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
type name_prefix = Prims.string Prims.list
type proof_namespace =
  (name_prefix, Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,
     (FStar_Syntax_Syntax.sigelt,
       FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,
    FStar_Range.range) FStar_Pervasives_Native.tuple2
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
    (FStar_Syntax_Syntax.lbname, FStar_Syntax_Syntax.typ,
      FStar_Syntax_Syntax.univ_names) FStar_Pervasives_Native.tuple3
      Prims.list
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
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp, guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ, guard_t)
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
    (Prims.int FStar_Util.smap,
      (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Util.smap ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
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
      ((Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2
    ;
  rollback:
    Prims.string ->
      (Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit
    ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (env, goal, FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
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
    (FStar_Syntax_Syntax.universe Prims.list,
      FStar_TypeChecker_Common.univ_ineq Prims.list)
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
    (env, FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
    }
and tcenv_hooks =
  {
  tc_push_in_gamma_hook:
    env ->
      (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either -> unit
    }
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__solver
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__range
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__curmodule
let (__proj__Mkenv__item__gamma :
  env -> FStar_Syntax_Syntax.binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__gamma
let (__proj__Mkenv__item__gamma_sig : env -> sig_binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__gamma_sig
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__gamma_cache
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__modules
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__expected_typ
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__sigtab
let (__proj__Mkenv__item__attrtab :
  env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__attrtab
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__is_pattern
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__instantiate_imp
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__effects
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__generalize
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname, FStar_Syntax_Syntax.typ,
      FStar_Syntax_Syntax.univ_names) FStar_Pervasives_Native.tuple3
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__letrecs
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__top_level
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__check_uvars
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__use_eq
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__is_iface
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__admit
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__lax
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__lax_universes
let (__proj__Mkenv__item__phase1 : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__phase1
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__failhard
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__nosynth
let (__proj__Mkenv__item__uvar_subtyping : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__uvar_subtyping
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp, guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__tc_term
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ, guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__type_of
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__universe_of
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__check_type_of
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__use_bv_sorts
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap,
      (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__qtbl_name_and_index
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__normalized_eff_names
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__proof_ns
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__synth_hook
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__splice
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__is_native_tactic
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__identifier_info
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__tc_hooks
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__dsenv
let (__proj__Mkenv__item__nbe :
  env ->
    step Prims.list ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_sig = __fname__gamma_sig; gamma_cache = __fname__gamma_cache;
        modules = __fname__modules; expected_typ = __fname__expected_typ;
        sigtab = __fname__sigtab; attrtab = __fname__attrtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        phase1 = __fname__phase1; failhard = __fname__failhard;
        nosynth = __fname__nosynth; uvar_subtyping = __fname__uvar_subtyping;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__nbe
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
let (__proj__Mksolver_t__item__snapshot :
  solver_t ->
    Prims.string ->
      ((Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__snapshot
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit)
  =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__rollback
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env ->
      goal ->
        (env, goal, FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list)
  =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,
      FStar_TypeChecker_Common.univ_ineq Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
let (__proj__Mkguard_t__item__implicits : guard_t -> implicit Prims.list) =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
let (__proj__Mkimplicit__item__imp_reason : implicit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_reason
let (__proj__Mkimplicit__item__imp_uvar :
  implicit -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_uvar
let (__proj__Mkimplicit__item__imp_tm : implicit -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_tm
let (__proj__Mkimplicit__item__imp_range : implicit -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_range
let (__proj__Mkimplicit__item__imp_meta :
  implicit ->
    (env, FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { imp_reason = __fname__imp_reason; imp_uvar = __fname__imp_uvar;
        imp_tm = __fname__imp_tm; imp_range = __fname__imp_range;
        imp_meta = __fname__imp_meta;_} -> __fname__imp_meta
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks ->
    env ->
      (FStar_Syntax_Syntax.binding, sig_binding) FStar_Util.either -> unit)
  =
  fun projectee ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
type solver_depth_t =
  (Prims.int, Prims.int, Prims.int) FStar_Pervasives_Native.tuple3
type implicits = implicit Prims.list
let (rename_gamma :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.gamma -> FStar_Syntax_Syntax.gamma)
  =
  fun subst1 ->
    fun gamma ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___225_9659 ->
              match uu___225_9659 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9662 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____9662 in
                  let uu____9663 =
                    let uu____9664 = FStar_Syntax_Subst.compress y in
                    uu____9664.FStar_Syntax_Syntax.n in
                  (match uu____9663 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9668 =
                         let uu___239_9669 = y1 in
                         let uu____9670 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___239_9669.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___239_9669.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9670
                         } in
                       FStar_Syntax_Syntax.Binding_var uu____9668
                   | uu____9673 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1 ->
    fun env ->
      let uu___240_9685 = env in
      let uu____9686 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___240_9685.solver);
        range = (uu___240_9685.range);
        curmodule = (uu___240_9685.curmodule);
        gamma = uu____9686;
        gamma_sig = (uu___240_9685.gamma_sig);
        gamma_cache = (uu___240_9685.gamma_cache);
        modules = (uu___240_9685.modules);
        expected_typ = (uu___240_9685.expected_typ);
        sigtab = (uu___240_9685.sigtab);
        attrtab = (uu___240_9685.attrtab);
        is_pattern = (uu___240_9685.is_pattern);
        instantiate_imp = (uu___240_9685.instantiate_imp);
        effects = (uu___240_9685.effects);
        generalize = (uu___240_9685.generalize);
        letrecs = (uu___240_9685.letrecs);
        top_level = (uu___240_9685.top_level);
        check_uvars = (uu___240_9685.check_uvars);
        use_eq = (uu___240_9685.use_eq);
        is_iface = (uu___240_9685.is_iface);
        admit = (uu___240_9685.admit);
        lax = (uu___240_9685.lax);
        lax_universes = (uu___240_9685.lax_universes);
        phase1 = (uu___240_9685.phase1);
        failhard = (uu___240_9685.failhard);
        nosynth = (uu___240_9685.nosynth);
        uvar_subtyping = (uu___240_9685.uvar_subtyping);
        tc_term = (uu___240_9685.tc_term);
        type_of = (uu___240_9685.type_of);
        universe_of = (uu___240_9685.universe_of);
        check_type_of = (uu___240_9685.check_type_of);
        use_bv_sorts = (uu___240_9685.use_bv_sorts);
        qtbl_name_and_index = (uu___240_9685.qtbl_name_and_index);
        normalized_eff_names = (uu___240_9685.normalized_eff_names);
        proof_ns = (uu___240_9685.proof_ns);
        synth_hook = (uu___240_9685.synth_hook);
        splice = (uu___240_9685.splice);
        is_native_tactic = (uu___240_9685.is_native_tactic);
        identifier_info = (uu___240_9685.identifier_info);
        tc_hooks = (uu___240_9685.tc_hooks);
        dsenv = (uu___240_9685.dsenv);
        nbe = (uu___240_9685.nbe)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9693 -> fun uu____9694 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env -> env.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env ->
    fun hooks ->
      let uu___241_9714 = env in
      {
        solver = (uu___241_9714.solver);
        range = (uu___241_9714.range);
        curmodule = (uu___241_9714.curmodule);
        gamma = (uu___241_9714.gamma);
        gamma_sig = (uu___241_9714.gamma_sig);
        gamma_cache = (uu___241_9714.gamma_cache);
        modules = (uu___241_9714.modules);
        expected_typ = (uu___241_9714.expected_typ);
        sigtab = (uu___241_9714.sigtab);
        attrtab = (uu___241_9714.attrtab);
        is_pattern = (uu___241_9714.is_pattern);
        instantiate_imp = (uu___241_9714.instantiate_imp);
        effects = (uu___241_9714.effects);
        generalize = (uu___241_9714.generalize);
        letrecs = (uu___241_9714.letrecs);
        top_level = (uu___241_9714.top_level);
        check_uvars = (uu___241_9714.check_uvars);
        use_eq = (uu___241_9714.use_eq);
        is_iface = (uu___241_9714.is_iface);
        admit = (uu___241_9714.admit);
        lax = (uu___241_9714.lax);
        lax_universes = (uu___241_9714.lax_universes);
        phase1 = (uu___241_9714.phase1);
        failhard = (uu___241_9714.failhard);
        nosynth = (uu___241_9714.nosynth);
        uvar_subtyping = (uu___241_9714.uvar_subtyping);
        tc_term = (uu___241_9714.tc_term);
        type_of = (uu___241_9714.type_of);
        universe_of = (uu___241_9714.universe_of);
        check_type_of = (uu___241_9714.check_type_of);
        use_bv_sorts = (uu___241_9714.use_bv_sorts);
        qtbl_name_and_index = (uu___241_9714.qtbl_name_and_index);
        normalized_eff_names = (uu___241_9714.normalized_eff_names);
        proof_ns = (uu___241_9714.proof_ns);
        synth_hook = (uu___241_9714.synth_hook);
        splice = (uu___241_9714.splice);
        is_native_tactic = (uu___241_9714.is_native_tactic);
        identifier_info = (uu___241_9714.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___241_9714.dsenv);
        nbe = (uu___241_9714.nbe)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___242_9725 = e in
      let uu____9726 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
      {
        solver = (uu___242_9725.solver);
        range = (uu___242_9725.range);
        curmodule = (uu___242_9725.curmodule);
        gamma = (uu___242_9725.gamma);
        gamma_sig = (uu___242_9725.gamma_sig);
        gamma_cache = (uu___242_9725.gamma_cache);
        modules = (uu___242_9725.modules);
        expected_typ = (uu___242_9725.expected_typ);
        sigtab = (uu___242_9725.sigtab);
        attrtab = (uu___242_9725.attrtab);
        is_pattern = (uu___242_9725.is_pattern);
        instantiate_imp = (uu___242_9725.instantiate_imp);
        effects = (uu___242_9725.effects);
        generalize = (uu___242_9725.generalize);
        letrecs = (uu___242_9725.letrecs);
        top_level = (uu___242_9725.top_level);
        check_uvars = (uu___242_9725.check_uvars);
        use_eq = (uu___242_9725.use_eq);
        is_iface = (uu___242_9725.is_iface);
        admit = (uu___242_9725.admit);
        lax = (uu___242_9725.lax);
        lax_universes = (uu___242_9725.lax_universes);
        phase1 = (uu___242_9725.phase1);
        failhard = (uu___242_9725.failhard);
        nosynth = (uu___242_9725.nosynth);
        uvar_subtyping = (uu___242_9725.uvar_subtyping);
        tc_term = (uu___242_9725.tc_term);
        type_of = (uu___242_9725.type_of);
        universe_of = (uu___242_9725.universe_of);
        check_type_of = (uu___242_9725.check_type_of);
        use_bv_sorts = (uu___242_9725.use_bv_sorts);
        qtbl_name_and_index = (uu___242_9725.qtbl_name_and_index);
        normalized_eff_names = (uu___242_9725.normalized_eff_names);
        proof_ns = (uu___242_9725.proof_ns);
        synth_hook = (uu___242_9725.synth_hook);
        splice = (uu___242_9725.splice);
        is_native_tactic = (uu___242_9725.is_native_tactic);
        identifier_info = (uu___242_9725.identifier_info);
        tc_hooks = (uu___242_9725.tc_hooks);
        dsenv = uu____9726;
        nbe = (uu___242_9725.nbe)
      }
let (dep_graph : env -> FStar_Parser_Dep.deps) =
  fun e -> FStar_Syntax_DsEnv.dep_graph e.dsenv
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let (should_verify : env -> Prims.bool) =
  fun env ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d ->
    fun q ->
      match (d, q) with
      | (NoDelta, uu____9749) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____9750,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____9751, FStar_Syntax_Syntax.Visible_default) -> true
      | (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu____9752 -> false
let (default_table_size : Prims.int) = (Prims.parse_int "200")
let new_sigtab : 'Auu____9761 . unit -> 'Auu____9761 FStar_Util.smap =
  fun uu____9768 -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'Auu____9773 . unit -> 'Auu____9773 FStar_Util.smap =
  fun uu____9780 -> FStar_Util.smap_create (Prims.parse_int "100")
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp, guard_t)
           FStar_Pervasives_Native.tuple3)
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ, guard_t)
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
  fun deps ->
    fun tc_term ->
      fun type_of ->
        fun universe_of ->
          fun check_type_of ->
            fun solver ->
              fun module_lid ->
                fun nbe1 ->
                  let uu____9914 = new_gamma_cache () in
                  let uu____9917 = new_sigtab () in
                  let uu____9920 = new_sigtab () in
                  let uu____9927 =
                    let uu____9940 =
                      FStar_Util.smap_create (Prims.parse_int "10") in
                    (uu____9940, FStar_Pervasives_Native.None) in
                  let uu____9955 =
                    FStar_Util.smap_create (Prims.parse_int "20") in
                  let uu____9958 = FStar_Options.using_facts_from () in
                  let uu____9959 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty in
                  let uu____9962 = FStar_Syntax_DsEnv.empty_env deps in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____9914;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____9917;
                    attrtab = uu____9920;
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
                    qtbl_name_and_index = uu____9927;
                    normalized_eff_names = uu____9955;
                    proof_ns = uu____9958;
                    synth_hook =
                      (fun e ->
                         fun g ->
                           fun tau -> failwith "no synthesizer available");
                    splice =
                      (fun e -> fun tau -> failwith "no splicer available");
                    is_native_tactic = (fun uu____9998 -> false);
                    identifier_info = uu____9959;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____9962;
                    nbe = nbe1
                  }
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env -> env.dsenv
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env -> env.sigtab
let (attrtab : env -> FStar_Syntax_Syntax.sigelt Prims.list FStar_Util.smap)
  = fun env -> env.attrtab
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env -> env.gamma_cache
let (query_indices :
  (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]]
let (push_query_indices : unit -> unit) =
  fun uu____10098 ->
    let uu____10099 = FStar_ST.op_Bang query_indices in
    match uu____10099 with
    | [] -> failwith "Empty query indices!"
    | uu____10149 ->
        let uu____10158 =
          let uu____10167 =
            let uu____10174 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____10174 in
          let uu____10224 = FStar_ST.op_Bang query_indices in uu____10167 ::
            uu____10224 in
        FStar_ST.op_Colon_Equals query_indices uu____10158
let (pop_query_indices : unit -> unit) =
  fun uu____10313 ->
    let uu____10314 = FStar_ST.op_Bang query_indices in
    match uu____10314 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let (snapshot_query_indices :
  unit -> (Prims.int, unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10429 ->
    FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index :
  (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10459 ->
    match uu____10459 with
    | (l, n1) ->
        let uu____10466 = FStar_ST.op_Bang query_indices in
        (match uu____10466 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10577 -> failwith "Empty query indices")
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10596 ->
    let uu____10597 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____10597
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env ->
    (let uu____10670 =
       let uu____10673 = FStar_ST.op_Bang stack in env :: uu____10673 in
     FStar_ST.op_Colon_Equals stack uu____10670);
    (let uu___243_10722 = env in
     let uu____10723 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____10726 = FStar_Util.smap_copy (sigtab env) in
     let uu____10729 = FStar_Util.smap_copy (attrtab env) in
     let uu____10736 =
       let uu____10749 =
         let uu____10752 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu____10752 in
       let uu____10777 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu____10749, uu____10777) in
     let uu____10818 = FStar_Util.smap_copy env.normalized_eff_names in
     let uu____10821 =
       let uu____10824 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____10824 in
     {
       solver = (uu___243_10722.solver);
       range = (uu___243_10722.range);
       curmodule = (uu___243_10722.curmodule);
       gamma = (uu___243_10722.gamma);
       gamma_sig = (uu___243_10722.gamma_sig);
       gamma_cache = uu____10723;
       modules = (uu___243_10722.modules);
       expected_typ = (uu___243_10722.expected_typ);
       sigtab = uu____10726;
       attrtab = uu____10729;
       is_pattern = (uu___243_10722.is_pattern);
       instantiate_imp = (uu___243_10722.instantiate_imp);
       effects = (uu___243_10722.effects);
       generalize = (uu___243_10722.generalize);
       letrecs = (uu___243_10722.letrecs);
       top_level = (uu___243_10722.top_level);
       check_uvars = (uu___243_10722.check_uvars);
       use_eq = (uu___243_10722.use_eq);
       is_iface = (uu___243_10722.is_iface);
       admit = (uu___243_10722.admit);
       lax = (uu___243_10722.lax);
       lax_universes = (uu___243_10722.lax_universes);
       phase1 = (uu___243_10722.phase1);
       failhard = (uu___243_10722.failhard);
       nosynth = (uu___243_10722.nosynth);
       uvar_subtyping = (uu___243_10722.uvar_subtyping);
       tc_term = (uu___243_10722.tc_term);
       type_of = (uu___243_10722.type_of);
       universe_of = (uu___243_10722.universe_of);
       check_type_of = (uu___243_10722.check_type_of);
       use_bv_sorts = (uu___243_10722.use_bv_sorts);
       qtbl_name_and_index = uu____10736;
       normalized_eff_names = uu____10818;
       proof_ns = (uu___243_10722.proof_ns);
       synth_hook = (uu___243_10722.synth_hook);
       splice = (uu___243_10722.splice);
       is_native_tactic = (uu___243_10722.is_native_tactic);
       identifier_info = uu____10821;
       tc_hooks = (uu___243_10722.tc_hooks);
       dsenv = (uu___243_10722.dsenv);
       nbe = (uu___243_10722.nbe)
     })
let (pop_stack : unit -> env) =
  fun uu____10870 ->
    let uu____10871 = FStar_ST.op_Bang stack in
    match uu____10871 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____10925 -> failwith "Impossible: Too many pops"
let (snapshot_stack : env -> (Prims.int, env) FStar_Pervasives_Native.tuple2)
  = fun env -> FStar_Common.snapshot push_stack stack env
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth -> FStar_Common.rollback pop_stack stack depth
type tcenv_depth_t =
  (Prims.int, Prims.int, solver_depth_t, Prims.int)
    FStar_Pervasives_Native.tuple4
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t, env) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun msg ->
      FStar_Util.atomically
        (fun uu____10997 ->
           let uu____10998 = snapshot_stack env in
           match uu____10998 with
           | (stack_depth, env1) ->
               let uu____11023 = snapshot_query_indices () in
               (match uu____11023 with
                | (query_indices_depth, ()) ->
                    let uu____11047 = (env1.solver).snapshot msg in
                    (match uu____11047 with
                     | (solver_depth, ()) ->
                         let uu____11089 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv in
                         (match uu____11089 with
                          | (dsenv_depth, dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___244_11135 = env1 in
                                 {
                                   solver = (uu___244_11135.solver);
                                   range = (uu___244_11135.range);
                                   curmodule = (uu___244_11135.curmodule);
                                   gamma = (uu___244_11135.gamma);
                                   gamma_sig = (uu___244_11135.gamma_sig);
                                   gamma_cache = (uu___244_11135.gamma_cache);
                                   modules = (uu___244_11135.modules);
                                   expected_typ =
                                     (uu___244_11135.expected_typ);
                                   sigtab = (uu___244_11135.sigtab);
                                   attrtab = (uu___244_11135.attrtab);
                                   is_pattern = (uu___244_11135.is_pattern);
                                   instantiate_imp =
                                     (uu___244_11135.instantiate_imp);
                                   effects = (uu___244_11135.effects);
                                   generalize = (uu___244_11135.generalize);
                                   letrecs = (uu___244_11135.letrecs);
                                   top_level = (uu___244_11135.top_level);
                                   check_uvars = (uu___244_11135.check_uvars);
                                   use_eq = (uu___244_11135.use_eq);
                                   is_iface = (uu___244_11135.is_iface);
                                   admit = (uu___244_11135.admit);
                                   lax = (uu___244_11135.lax);
                                   lax_universes =
                                     (uu___244_11135.lax_universes);
                                   phase1 = (uu___244_11135.phase1);
                                   failhard = (uu___244_11135.failhard);
                                   nosynth = (uu___244_11135.nosynth);
                                   uvar_subtyping =
                                     (uu___244_11135.uvar_subtyping);
                                   tc_term = (uu___244_11135.tc_term);
                                   type_of = (uu___244_11135.type_of);
                                   universe_of = (uu___244_11135.universe_of);
                                   check_type_of =
                                     (uu___244_11135.check_type_of);
                                   use_bv_sorts =
                                     (uu___244_11135.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___244_11135.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___244_11135.normalized_eff_names);
                                   proof_ns = (uu___244_11135.proof_ns);
                                   synth_hook = (uu___244_11135.synth_hook);
                                   splice = (uu___244_11135.splice);
                                   is_native_tactic =
                                     (uu___244_11135.is_native_tactic);
                                   identifier_info =
                                     (uu___244_11135.identifier_info);
                                   tc_hooks = (uu___244_11135.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___244_11135.nbe)
                                 }))))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
          (fun uu____11166 ->
             let uu____11167 =
               match depth with
               | FStar_Pervasives_Native.Some (s1, s2, s3, s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None) in
             match uu____11167 with
             | (stack_depth, query_indices_depth, solver_depth, dsenv_depth)
                 ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth in
                             ((let uu____11293 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1 in
                               FStar_Common.runtime_assert uu____11293
                                 "Inconsistent stack state");
                              tcenv))))))
let (push : env -> Prims.string -> env) =
  fun env ->
    fun msg ->
      let uu____11304 = snapshot env msg in
      FStar_Pervasives_Native.snd uu____11304
let (pop : env -> Prims.string -> env) =
  fun env -> fun msg -> rollback env.solver msg FStar_Pervasives_Native.None
let (incr_query_index : env -> env) =
  fun env ->
    let qix = peek_query_indices () in
    match env.qtbl_name_and_index with
    | (uu____11331, FStar_Pervasives_Native.None) -> env
    | (tbl, FStar_Pervasives_Native.Some (l, n1)) ->
        let uu____11363 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11389 ->
                  match uu____11389 with
                  | (m, uu____11395) -> FStar_Ident.lid_equals l m)) in
        (match uu____11363 with
         | FStar_Pervasives_Native.None ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___245_11403 = env in
               {
                 solver = (uu___245_11403.solver);
                 range = (uu___245_11403.range);
                 curmodule = (uu___245_11403.curmodule);
                 gamma = (uu___245_11403.gamma);
                 gamma_sig = (uu___245_11403.gamma_sig);
                 gamma_cache = (uu___245_11403.gamma_cache);
                 modules = (uu___245_11403.modules);
                 expected_typ = (uu___245_11403.expected_typ);
                 sigtab = (uu___245_11403.sigtab);
                 attrtab = (uu___245_11403.attrtab);
                 is_pattern = (uu___245_11403.is_pattern);
                 instantiate_imp = (uu___245_11403.instantiate_imp);
                 effects = (uu___245_11403.effects);
                 generalize = (uu___245_11403.generalize);
                 letrecs = (uu___245_11403.letrecs);
                 top_level = (uu___245_11403.top_level);
                 check_uvars = (uu___245_11403.check_uvars);
                 use_eq = (uu___245_11403.use_eq);
                 is_iface = (uu___245_11403.is_iface);
                 admit = (uu___245_11403.admit);
                 lax = (uu___245_11403.lax);
                 lax_universes = (uu___245_11403.lax_universes);
                 phase1 = (uu___245_11403.phase1);
                 failhard = (uu___245_11403.failhard);
                 nosynth = (uu___245_11403.nosynth);
                 uvar_subtyping = (uu___245_11403.uvar_subtyping);
                 tc_term = (uu___245_11403.tc_term);
                 type_of = (uu___245_11403.type_of);
                 universe_of = (uu___245_11403.universe_of);
                 check_type_of = (uu___245_11403.check_type_of);
                 use_bv_sorts = (uu___245_11403.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___245_11403.normalized_eff_names);
                 proof_ns = (uu___245_11403.proof_ns);
                 synth_hook = (uu___245_11403.synth_hook);
                 splice = (uu___245_11403.splice);
                 is_native_tactic = (uu___245_11403.is_native_tactic);
                 identifier_info = (uu___245_11403.identifier_info);
                 tc_hooks = (uu___245_11403.tc_hooks);
                 dsenv = (uu___245_11403.dsenv);
                 nbe = (uu___245_11403.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11416, m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___246_11425 = env in
               {
                 solver = (uu___246_11425.solver);
                 range = (uu___246_11425.range);
                 curmodule = (uu___246_11425.curmodule);
                 gamma = (uu___246_11425.gamma);
                 gamma_sig = (uu___246_11425.gamma_sig);
                 gamma_cache = (uu___246_11425.gamma_cache);
                 modules = (uu___246_11425.modules);
                 expected_typ = (uu___246_11425.expected_typ);
                 sigtab = (uu___246_11425.sigtab);
                 attrtab = (uu___246_11425.attrtab);
                 is_pattern = (uu___246_11425.is_pattern);
                 instantiate_imp = (uu___246_11425.instantiate_imp);
                 effects = (uu___246_11425.effects);
                 generalize = (uu___246_11425.generalize);
                 letrecs = (uu___246_11425.letrecs);
                 top_level = (uu___246_11425.top_level);
                 check_uvars = (uu___246_11425.check_uvars);
                 use_eq = (uu___246_11425.use_eq);
                 is_iface = (uu___246_11425.is_iface);
                 admit = (uu___246_11425.admit);
                 lax = (uu___246_11425.lax);
                 lax_universes = (uu___246_11425.lax_universes);
                 phase1 = (uu___246_11425.phase1);
                 failhard = (uu___246_11425.failhard);
                 nosynth = (uu___246_11425.nosynth);
                 uvar_subtyping = (uu___246_11425.uvar_subtyping);
                 tc_term = (uu___246_11425.tc_term);
                 type_of = (uu___246_11425.type_of);
                 universe_of = (uu___246_11425.universe_of);
                 check_type_of = (uu___246_11425.check_type_of);
                 use_bv_sorts = (uu___246_11425.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___246_11425.normalized_eff_names);
                 proof_ns = (uu___246_11425.proof_ns);
                 synth_hook = (uu___246_11425.synth_hook);
                 splice = (uu___246_11425.splice);
                 is_native_tactic = (uu___246_11425.is_native_tactic);
                 identifier_info = (uu___246_11425.identifier_info);
                 tc_hooks = (uu___246_11425.tc_hooks);
                 dsenv = (uu___246_11425.dsenv);
                 nbe = (uu___246_11425.nbe)
               })))
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env ->
    fun l -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let (set_range : env -> FStar_Range.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___247_11459 = e in
         {
           solver = (uu___247_11459.solver);
           range = r;
           curmodule = (uu___247_11459.curmodule);
           gamma = (uu___247_11459.gamma);
           gamma_sig = (uu___247_11459.gamma_sig);
           gamma_cache = (uu___247_11459.gamma_cache);
           modules = (uu___247_11459.modules);
           expected_typ = (uu___247_11459.expected_typ);
           sigtab = (uu___247_11459.sigtab);
           attrtab = (uu___247_11459.attrtab);
           is_pattern = (uu___247_11459.is_pattern);
           instantiate_imp = (uu___247_11459.instantiate_imp);
           effects = (uu___247_11459.effects);
           generalize = (uu___247_11459.generalize);
           letrecs = (uu___247_11459.letrecs);
           top_level = (uu___247_11459.top_level);
           check_uvars = (uu___247_11459.check_uvars);
           use_eq = (uu___247_11459.use_eq);
           is_iface = (uu___247_11459.is_iface);
           admit = (uu___247_11459.admit);
           lax = (uu___247_11459.lax);
           lax_universes = (uu___247_11459.lax_universes);
           phase1 = (uu___247_11459.phase1);
           failhard = (uu___247_11459.failhard);
           nosynth = (uu___247_11459.nosynth);
           uvar_subtyping = (uu___247_11459.uvar_subtyping);
           tc_term = (uu___247_11459.tc_term);
           type_of = (uu___247_11459.type_of);
           universe_of = (uu___247_11459.universe_of);
           check_type_of = (uu___247_11459.check_type_of);
           use_bv_sorts = (uu___247_11459.use_bv_sorts);
           qtbl_name_and_index = (uu___247_11459.qtbl_name_and_index);
           normalized_eff_names = (uu___247_11459.normalized_eff_names);
           proof_ns = (uu___247_11459.proof_ns);
           synth_hook = (uu___247_11459.synth_hook);
           splice = (uu___247_11459.splice);
           is_native_tactic = (uu___247_11459.is_native_tactic);
           identifier_info = (uu___247_11459.identifier_info);
           tc_hooks = (uu___247_11459.tc_hooks);
           dsenv = (uu___247_11459.dsenv);
           nbe = (uu___247_11459.nbe)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env ->
    fun enabled ->
      let uu____11475 =
        let uu____11476 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____11476 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11475
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env ->
    fun bv ->
      fun ty ->
        let uu____11530 =
          let uu____11531 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11531 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11530
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env ->
    fun fv ->
      fun ty ->
        let uu____11585 =
          let uu____11586 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11586 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11585
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env ->
    fun ty_map ->
      let uu____11640 =
        let uu____11641 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____11641 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11640
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env -> env.modules
let (current_module : env -> FStar_Ident.lident) = fun env -> env.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun lid ->
      let uu___248_11702 = env in
      {
        solver = (uu___248_11702.solver);
        range = (uu___248_11702.range);
        curmodule = lid;
        gamma = (uu___248_11702.gamma);
        gamma_sig = (uu___248_11702.gamma_sig);
        gamma_cache = (uu___248_11702.gamma_cache);
        modules = (uu___248_11702.modules);
        expected_typ = (uu___248_11702.expected_typ);
        sigtab = (uu___248_11702.sigtab);
        attrtab = (uu___248_11702.attrtab);
        is_pattern = (uu___248_11702.is_pattern);
        instantiate_imp = (uu___248_11702.instantiate_imp);
        effects = (uu___248_11702.effects);
        generalize = (uu___248_11702.generalize);
        letrecs = (uu___248_11702.letrecs);
        top_level = (uu___248_11702.top_level);
        check_uvars = (uu___248_11702.check_uvars);
        use_eq = (uu___248_11702.use_eq);
        is_iface = (uu___248_11702.is_iface);
        admit = (uu___248_11702.admit);
        lax = (uu___248_11702.lax);
        lax_universes = (uu___248_11702.lax_universes);
        phase1 = (uu___248_11702.phase1);
        failhard = (uu___248_11702.failhard);
        nosynth = (uu___248_11702.nosynth);
        uvar_subtyping = (uu___248_11702.uvar_subtyping);
        tc_term = (uu___248_11702.tc_term);
        type_of = (uu___248_11702.type_of);
        universe_of = (uu___248_11702.universe_of);
        check_type_of = (uu___248_11702.check_type_of);
        use_bv_sorts = (uu___248_11702.use_bv_sorts);
        qtbl_name_and_index = (uu___248_11702.qtbl_name_and_index);
        normalized_eff_names = (uu___248_11702.normalized_eff_names);
        proof_ns = (uu___248_11702.proof_ns);
        synth_hook = (uu___248_11702.synth_hook);
        splice = (uu___248_11702.splice);
        is_native_tactic = (uu___248_11702.is_native_tactic);
        identifier_info = (uu___248_11702.identifier_info);
        tc_hooks = (uu___248_11702.tc_hooks);
        dsenv = (uu___248_11702.dsenv);
        nbe = (uu___248_11702.nbe)
      }
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____11729 = FStar_Ident.text_of_lid lid in
      FStar_Util.smap_try_find (sigtab env) uu____11729
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    let uu____11739 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str in
    (FStar_Errors.Fatal_NameNotFound, uu____11739)
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1 ->
    let uu____11749 =
      let uu____11750 = FStar_Syntax_Print.bv_to_string v1 in
      FStar_Util.format1 "Variable \"%s\" not found" uu____11750 in
    (FStar_Errors.Fatal_VariableNotFound, uu____11749)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____11755 ->
    let uu____11756 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____11756
let (mk_univ_subst :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.universes -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun formals ->
    fun us ->
      let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
      FStar_All.pipe_right us
        (FStar_List.mapi
           (fun i -> fun u -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun ts ->
    fun us ->
      match (ts, us) with
      | (([], t), []) -> ([], t)
      | ((formals, t), uu____11850) ->
          let vs = mk_univ_subst formals us in
          let uu____11874 = FStar_Syntax_Subst.subst vs t in
          (us, uu____11874)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___226_11890 ->
    match uu___226_11890 with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____11916 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r ->
    fun t ->
      let uu____11935 = inst_tscheme t in
      match uu____11935 with
      | (us, t1) ->
          let uu____11946 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____11946)
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts ->
    fun env ->
      fun ed ->
        fun uu____11966 ->
          match uu____11966 with
          | (us, t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____11987 =
                         let uu____11988 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____11989 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____11990 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____11991 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____11988 uu____11989 uu____11990 uu____11991 in
                       failwith uu____11987)
                    else ();
                    (let uu____11993 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____11993))
               | uu____12002 ->
                   let uu____12003 =
                     let uu____12004 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12004 in
                   failwith uu____12003)
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu____12010 -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____12016 -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____12022 -> false
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env ->
    fun l ->
      let cur = current_module env in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident] in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident] in
           let rec aux c l1 =
             match (c, l1) with
             | ([], uu____12064) -> Maybe
             | (uu____12071, []) -> No
             | (hd1::tl1, hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12090 -> No in
           aux cur1 lns)
        else No
type qninfo =
  (((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,
     (FStar_Syntax_Syntax.sigelt,
       FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,
    FStar_Range.range) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env ->
    fun lid ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____12181 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____12181 with
          | FStar_Pervasives_Native.None ->
              let uu____12204 =
                FStar_Util.find_map env.gamma
                  (fun uu___227_12248 ->
                     match uu___227_12248 with
                     | FStar_Syntax_Syntax.Binding_lid (l, t) ->
                         let uu____12287 = FStar_Ident.lid_equals lid l in
                         if uu____12287
                         then
                           let uu____12308 =
                             let uu____12327 =
                               let uu____12342 = inst_tscheme t in
                               FStar_Util.Inl uu____12342 in
                             let uu____12357 = FStar_Ident.range_of_lid l in
                             (uu____12327, uu____12357) in
                           FStar_Pervasives_Native.Some uu____12308
                         else FStar_Pervasives_Native.None
                     | uu____12409 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu____12204
                (fun uu____12447 ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___228_12456 ->
                        match uu___228_12456 with
                        | (uu____12459,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               (ses, uu____12461);
                             FStar_Syntax_Syntax.sigrng = uu____12462;
                             FStar_Syntax_Syntax.sigquals = uu____12463;
                             FStar_Syntax_Syntax.sigmeta = uu____12464;
                             FStar_Syntax_Syntax.sigattrs = uu____12465;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu____12485 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu____12485
                                 then
                                   cache
                                     ((FStar_Util.Inr
                                         (se, FStar_Pervasives_Native.None)),
                                       (FStar_Syntax_Util.range_of_sigelt se))
                                 else FStar_Pervasives_Native.None)
                        | (lids, s) ->
                            let maybe_cache t =
                              match s.FStar_Syntax_Syntax.sigel with
                              | FStar_Syntax_Syntax.Sig_declare_typ
                                  uu____12533 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12540 -> cache t in
                            let uu____12541 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
                            (match uu____12541 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12547 =
                                   let uu____12548 =
                                     FStar_Ident.range_of_lid l in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12548) in
                                 maybe_cache uu____12547)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12616 = find_in_sigtab env lid in
         match uu____12616 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (lookup_sigelt :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____12696 = lookup_qname env lid in
      match uu____12696 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____12717, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env ->
    fun attr ->
      let uu____12828 = FStar_Util.smap_try_find (attrtab env) attr in
      match uu____12828 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let add_one1 env1 se1 attr =
        let uu____12870 =
          let uu____12873 = lookup_attr env1 attr in se1 :: uu____12873 in
        FStar_Util.smap_add (attrtab env1) attr uu____12870 in
      FStar_List.iter
        (fun attr ->
           let uu____12883 =
             let uu____12884 = FStar_Syntax_Subst.compress attr in
             uu____12884.FStar_Syntax_Syntax.n in
           match uu____12883 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____12888 =
                 let uu____12889 = FStar_Syntax_Syntax.lid_of_fv fv in
                 uu____12889.FStar_Ident.str in
               add_one1 env se uu____12888
           | uu____12890 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____12912) ->
          add_sigelts env ses
      | uu____12921 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           add_se_to_attrtab env se;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____12936 -> ()))
and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env ->
    fun ses -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ, FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun bv ->
      FStar_Util.find_map env.gamma
        (fun uu___229_12967 ->
           match uu___229_12967 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____12985 -> FStar_Pervasives_Native.None)
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,
          FStar_Range.range) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____13046, lb::[]), uu____13048) ->
            let uu____13055 =
              let uu____13064 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____13073 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____13064, uu____13073) in
            FStar_Pervasives_Native.Some uu____13055
        | FStar_Syntax_Syntax.Sig_let ((uu____13086, lbs), uu____13088) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13118 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13130 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____13130
                     then
                       let uu____13141 =
                         let uu____13150 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____13159 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____13150, uu____13159) in
                       FStar_Pervasives_Native.Some uu____13141
                     else FStar_Pervasives_Native.None)
        | uu____13181 -> FStar_Pervasives_Native.None
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____13240 =
            let uu____13249 =
              let uu____13254 =
                let uu____13255 =
                  let uu____13258 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13258 in
                ((ne.FStar_Syntax_Syntax.univs), uu____13255) in
              inst_tscheme1 uu____13254 in
            (uu____13249, (se.FStar_Syntax_Syntax.sigrng)) in
          FStar_Pervasives_Native.Some uu____13240
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, us, binders, uu____13280, uu____13281) ->
          let uu____13286 =
            let uu____13295 =
              let uu____13300 =
                let uu____13301 =
                  let uu____13304 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                  FStar_Syntax_Util.arrow binders uu____13304 in
                (us, uu____13301) in
              inst_tscheme1 uu____13300 in
            (uu____13295, (se.FStar_Syntax_Syntax.sigrng)) in
          FStar_Pervasives_Native.Some uu____13286
      | uu____13323 -> FStar_Pervasives_Native.None
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,
           FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,
          FStar_Range.range) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun env ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        let mapper uu____13411 =
          match uu____13411 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13507, uvs, t, uu____13510, uu____13511,
                         uu____13512);
                      FStar_Syntax_Syntax.sigrng = uu____13513;
                      FStar_Syntax_Syntax.sigquals = uu____13514;
                      FStar_Syntax_Syntax.sigmeta = uu____13515;
                      FStar_Syntax_Syntax.sigattrs = uu____13516;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____13537 =
                     let uu____13546 = inst_tscheme1 (uvs, t) in
                     (uu____13546, rng) in
                   FStar_Pervasives_Native.Some uu____13537
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____13570;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13572;
                      FStar_Syntax_Syntax.sigattrs = uu____13573;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____13590 =
                     let uu____13591 = in_cur_mod env l in uu____13591 = Yes in
                   if uu____13590
                   then
                     let uu____13602 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface in
                     (if uu____13602
                      then
                        let uu____13615 =
                          let uu____13624 = inst_tscheme1 (uvs, t) in
                          (uu____13624, rng) in
                        FStar_Pervasives_Native.Some uu____13615
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13655 =
                        let uu____13664 = inst_tscheme1 (uvs, t) in
                        (uu____13664, rng) in
                      FStar_Pervasives_Native.Some uu____13655)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____13689, uu____13690);
                      FStar_Syntax_Syntax.sigrng = uu____13691;
                      FStar_Syntax_Syntax.sigquals = uu____13692;
                      FStar_Syntax_Syntax.sigmeta = uu____13693;
                      FStar_Syntax_Syntax.sigattrs = uu____13694;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13735 =
                          let uu____13744 = inst_tscheme1 (uvs, k) in
                          (uu____13744, rng) in
                        FStar_Pervasives_Native.Some uu____13735
                    | uu____13765 ->
                        let uu____13766 =
                          let uu____13775 =
                            let uu____13780 =
                              let uu____13781 =
                                let uu____13784 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____13784 in
                              (uvs, uu____13781) in
                            inst_tscheme1 uu____13780 in
                          (uu____13775, rng) in
                        FStar_Pervasives_Native.Some uu____13766)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____13807, uu____13808);
                      FStar_Syntax_Syntax.sigrng = uu____13809;
                      FStar_Syntax_Syntax.sigquals = uu____13810;
                      FStar_Syntax_Syntax.sigmeta = uu____13811;
                      FStar_Syntax_Syntax.sigattrs = uu____13812;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____13854 =
                          let uu____13863 = inst_tscheme_with (uvs, k) us in
                          (uu____13863, rng) in
                        FStar_Pervasives_Native.Some uu____13854
                    | uu____13884 ->
                        let uu____13885 =
                          let uu____13894 =
                            let uu____13899 =
                              let uu____13900 =
                                let uu____13903 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____13903 in
                              (uvs, uu____13900) in
                            inst_tscheme_with uu____13899 us in
                          (uu____13894, rng) in
                        FStar_Pervasives_Native.Some uu____13885)
               | FStar_Util.Inr se ->
                   let uu____13939 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____13960;
                          FStar_Syntax_Syntax.sigrng = uu____13961;
                          FStar_Syntax_Syntax.sigquals = uu____13962;
                          FStar_Syntax_Syntax.sigmeta = uu____13963;
                          FStar_Syntax_Syntax.sigattrs = uu____13964;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____13979 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) in
                   FStar_All.pipe_right uu____13939
                     (FStar_Util.map_option
                        (fun uu____14027 ->
                           match uu____14027 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____14058 =
          let uu____14069 = lookup_qname env lid in
          FStar_Util.bind_opt uu____14069 mapper in
        match uu____14058 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____14143 =
              let uu____14154 =
                let uu____14161 =
                  let uu___249_14164 = t in
                  let uu____14165 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___249_14164.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14165;
                    FStar_Syntax_Syntax.vars =
                      (uu___249_14164.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____14161) in
              (uu____14154, r) in
            FStar_Pervasives_Native.Some uu____14143
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____14212 = lookup_qname env l in
      match uu____14212 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____14231 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ, FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____14283 = try_lookup_bv env bv in
      match uu____14283 with
      | FStar_Pervasives_Native.None ->
          let uu____14298 = variable_not_found bv in
          FStar_Errors.raise_error uu____14298 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____14313 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____14314 =
            let uu____14315 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____14315 in
          (uu____14313, uu____14314)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____14336 = try_lookup_lid_aux FStar_Pervasives_Native.None env l in
      match uu____14336 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____14402 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____14402 in
          let uu____14403 =
            let uu____14412 =
              let uu____14417 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____14417) in
            (uu____14412, r1) in
          FStar_Pervasives_Native.Some uu____14403
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ, FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun us ->
      fun l ->
        let uu____14451 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l in
        match uu____14451 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14484, t), r) ->
            let use_range1 = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____14509 = FStar_Range.use_range use_range1 in
              FStar_Range.set_use_range r uu____14509 in
            let uu____14510 =
              let uu____14515 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (uu____14515, r1) in
            FStar_Pervasives_Native.Some uu____14510
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun l ->
      let uu____14538 = try_lookup_lid env l in
      match uu____14538 with
      | FStar_Pervasives_Native.None ->
          let uu____14565 = name_not_found l in
          let uu____14570 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____14565 uu____14570
      | FStar_Pervasives_Native.Some v1 -> v1
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___230_14610 ->
              match uu___230_14610 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14612 -> false) env.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme, FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____14631 = lookup_qname env lid in
      match uu____14631 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14640, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____14643;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14645;
              FStar_Syntax_Syntax.sigattrs = uu____14646;_},
            FStar_Pervasives_Native.None),
           uu____14647)
          ->
          let uu____14696 =
            let uu____14703 =
              let uu____14704 =
                let uu____14707 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____14707 t in
              (uvs, uu____14704) in
            (uu____14703, q) in
          FStar_Pervasives_Native.Some uu____14696
      | uu____14720 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____14741 = lookup_qname env lid in
      match uu____14741 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14746, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____14749;
              FStar_Syntax_Syntax.sigquals = uu____14750;
              FStar_Syntax_Syntax.sigmeta = uu____14751;
              FStar_Syntax_Syntax.sigattrs = uu____14752;_},
            FStar_Pervasives_Native.None),
           uu____14753)
          ->
          let uu____14802 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____14802 (uvs, t)
      | uu____14807 ->
          let uu____14808 = name_not_found lid in
          let uu____14813 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____14808 uu____14813
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____14832 = lookup_qname env lid in
      match uu____14832 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14837, uvs, t, uu____14840, uu____14841, uu____14842);
              FStar_Syntax_Syntax.sigrng = uu____14843;
              FStar_Syntax_Syntax.sigquals = uu____14844;
              FStar_Syntax_Syntax.sigmeta = uu____14845;
              FStar_Syntax_Syntax.sigattrs = uu____14846;_},
            FStar_Pervasives_Native.None),
           uu____14847)
          ->
          let uu____14900 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____14900 (uvs, t)
      | uu____14905 ->
          let uu____14906 = name_not_found lid in
          let uu____14911 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____14906 uu____14911
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool, FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____14932 = lookup_qname env lid in
      match uu____14932 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14939, uu____14940, uu____14941, uu____14942,
                 uu____14943, dcs);
              FStar_Syntax_Syntax.sigrng = uu____14945;
              FStar_Syntax_Syntax.sigquals = uu____14946;
              FStar_Syntax_Syntax.sigmeta = uu____14947;
              FStar_Syntax_Syntax.sigattrs = uu____14948;_},
            uu____14949),
           uu____14950)
          -> (true, dcs)
      | uu____15011 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      let uu____15024 = lookup_qname env lid in
      match uu____15024 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15025, uu____15026, uu____15027, l, uu____15029,
                 uu____15030);
              FStar_Syntax_Syntax.sigrng = uu____15031;
              FStar_Syntax_Syntax.sigquals = uu____15032;
              FStar_Syntax_Syntax.sigmeta = uu____15033;
              FStar_Syntax_Syntax.sigattrs = uu____15034;_},
            uu____15035),
           uu____15036)
          -> l
      | uu____15091 ->
          let uu____15092 =
            let uu____15093 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____15093 in
          failwith uu____15092
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun lid ->
      fun qninfo ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        match qninfo with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____15142)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15193, lbs), uu____15195)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____15217 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____15217
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15249 -> FStar_Pervasives_Native.None)
        | uu____15254 -> FStar_Pervasives_Native.None
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun env ->
      fun lid ->
        let uu____15284 = lookup_qname env lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15284
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____15309), uu____15310) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15359 -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____15380), uu____15381) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____15430 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____15451 = lookup_qname env lid in
      FStar_All.pipe_left attrs_of_qninfo uu____15451
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ftv ->
      let uu____15470 = lookup_qname env ftv in
      match uu____15470 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____15474) ->
          let uu____15519 = effect_signature FStar_Pervasives_Native.None se in
          (match uu____15519 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____15540, t), r) ->
               let uu____15555 =
                 let uu____15556 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____15556 t in
               FStar_Pervasives_Native.Some uu____15555)
      | uu____15557 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun ftv ->
      let uu____15568 = try_lookup_effect_lid env ftv in
      match uu____15568 with
      | FStar_Pervasives_Native.None ->
          let uu____15571 = name_not_found ftv in
          let uu____15576 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____15571 uu____15576
      | FStar_Pervasives_Native.Some k -> k
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun univ_insts ->
      fun lid0 ->
        let uu____15599 = lookup_qname env lid0 in
        match uu____15599 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs1, binders, c, uu____15610);
                FStar_Syntax_Syntax.sigrng = uu____15611;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____15613;
                FStar_Syntax_Syntax.sigattrs = uu____15614;_},
              FStar_Pervasives_Native.None),
             uu____15615)
            ->
            let lid1 =
              let uu____15669 =
                let uu____15670 = FStar_Ident.range_of_lid lid in
                let uu____15671 =
                  let uu____15672 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____15672 in
                FStar_Range.set_use_range uu____15670 uu____15671 in
              FStar_Ident.set_lid_range lid uu____15669 in
            let uu____15673 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___231_15677 ->
                      match uu___231_15677 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____15678 -> false)) in
            if uu____15673
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____15692 =
                      let uu____15693 =
                        let uu____15694 = get_range env in
                        FStar_Range.string_of_range uu____15694 in
                      let uu____15695 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____15696 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____15693 uu____15695 uu____15696 in
                    failwith uu____15692) in
               match (binders, univs1) with
               | ([], uu____15713) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____15738, uu____15739::uu____15740::uu____15741) ->
                   let uu____15762 =
                     let uu____15763 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____15764 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____15763 uu____15764 in
                   failwith uu____15762
               | uu____15771 ->
                   let uu____15786 =
                     let uu____15791 =
                       let uu____15792 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____15792) in
                     inst_tscheme_with uu____15791 insts in
                   (match uu____15786 with
                    | (uu____15805, t) ->
                        let t1 =
                          let uu____15808 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____15808 t in
                        let uu____15809 =
                          let uu____15810 = FStar_Syntax_Subst.compress t1 in
                          uu____15810.FStar_Syntax_Syntax.n in
                        (match uu____15809 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____15845 -> failwith "Impossible")))
        | uu____15852 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun l ->
      let rec find1 l1 =
        let uu____15875 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____15875 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____15888, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____15895 = find1 l2 in
            (match uu____15895 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____15902 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str in
        match uu____15902 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____15906 = find1 l in
            (match uu____15906 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m)) in
      let uu____15911 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____15911
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env ->
    fun l ->
      let l1 = norm_eff_name env l in
      let uu____15925 = lookup_qname env l1 in
      match uu____15925 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____15928;
              FStar_Syntax_Syntax.sigrng = uu____15929;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____15931;
              FStar_Syntax_Syntax.sigattrs = uu____15932;_},
            uu____15933),
           uu____15934)
          -> q
      | uu____15985 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      fun i ->
        let fail1 uu____16006 =
          let uu____16007 =
            let uu____16008 = FStar_Util.string_of_int i in
            let uu____16009 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16008 uu____16009 in
          failwith uu____16007 in
        let uu____16010 = lookup_datacon env lid in
        match uu____16010 with
        | (uu____16015, t) ->
            let uu____16017 =
              let uu____16018 = FStar_Syntax_Subst.compress t in
              uu____16018.FStar_Syntax_Syntax.n in
            (match uu____16017 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____16022) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____16063 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____16063
                      FStar_Pervasives_Native.fst)
             | uu____16074 -> fail1 ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____16085 = lookup_qname env l in
      match uu____16085 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16086, uu____16087, uu____16088);
              FStar_Syntax_Syntax.sigrng = uu____16089;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16091;
              FStar_Syntax_Syntax.sigattrs = uu____16092;_},
            uu____16093),
           uu____16094)
          ->
          FStar_Util.for_some
            (fun uu___232_16147 ->
               match uu___232_16147 with
               | FStar_Syntax_Syntax.Projector uu____16148 -> true
               | uu____16153 -> false) quals
      | uu____16154 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____16165 = lookup_qname env lid in
      match uu____16165 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16166, uu____16167, uu____16168, uu____16169,
                 uu____16170, uu____16171);
              FStar_Syntax_Syntax.sigrng = uu____16172;
              FStar_Syntax_Syntax.sigquals = uu____16173;
              FStar_Syntax_Syntax.sigmeta = uu____16174;
              FStar_Syntax_Syntax.sigattrs = uu____16175;_},
            uu____16176),
           uu____16177)
          -> true
      | uu____16232 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____16243 = lookup_qname env lid in
      match uu____16243 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16244, uu____16245, uu____16246, uu____16247,
                 uu____16248, uu____16249);
              FStar_Syntax_Syntax.sigrng = uu____16250;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16252;
              FStar_Syntax_Syntax.sigattrs = uu____16253;_},
            uu____16254),
           uu____16255)
          ->
          FStar_Util.for_some
            (fun uu___233_16316 ->
               match uu___233_16316 with
               | FStar_Syntax_Syntax.RecordType uu____16317 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16326 -> true
               | uu____16335 -> false) quals
      | uu____16336 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16342, uu____16343);
            FStar_Syntax_Syntax.sigrng = uu____16344;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16346;
            FStar_Syntax_Syntax.sigattrs = uu____16347;_},
          uu____16348),
         uu____16349)
        ->
        FStar_Util.for_some
          (fun uu___234_16406 ->
             match uu___234_16406 with
             | FStar_Syntax_Syntax.Action uu____16407 -> true
             | uu____16408 -> false) quals
    | uu____16409 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____16420 = lookup_qname env lid in
      FStar_All.pipe_left qninfo_is_action uu____16420
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
    FStar_Parser_Const.op_Negation] in
  fun env ->
    fun head1 ->
      let uu____16434 =
        let uu____16435 = FStar_Syntax_Util.un_uinst head1 in
        uu____16435.FStar_Syntax_Syntax.n in
      match uu____16434 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____16439 ->
               true
           | uu____16440 -> false)
      | uu____16441 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____16452 = lookup_qname env l in
      match uu____16452 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____16454), uu____16455) ->
          FStar_Util.for_some
            (fun uu___235_16503 ->
               match uu___235_16503 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____16504 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____16505 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____16576 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____16592) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____16609 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____16616 ->
                 FStar_Pervasives_Native.Some true
             | uu____16633 -> FStar_Pervasives_Native.Some false) in
      let uu____16634 =
        let uu____16637 = lookup_qname env lid in
        FStar_Util.bind_opt uu____16637 mapper in
      match uu____16634 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env ->
    fun lid ->
      let uu____16689 = lookup_qname env lid in
      match uu____16689 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16692, uu____16693, tps, uu____16695, uu____16696,
                 uu____16697);
              FStar_Syntax_Syntax.sigrng = uu____16698;
              FStar_Syntax_Syntax.sigquals = uu____16699;
              FStar_Syntax_Syntax.sigmeta = uu____16700;
              FStar_Syntax_Syntax.sigattrs = uu____16701;_},
            uu____16702),
           uu____16703)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____16768 -> FStar_Pervasives_Native.None
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____16812 ->
              match uu____16812 with
              | (d, uu____16820) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env ->
    fun l ->
      let uu____16835 = effect_decl_opt env l in
      match uu____16835 with
      | FStar_Pervasives_Native.None ->
          let uu____16850 = name_not_found l in
          let uu____16855 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____16850 uu____16855
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____16877 -> fun t -> fun wp -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____16896 ->
            fun t -> fun wp -> fun e -> FStar_Util.return_all e))
  }
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident, mlift, mlift) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun l1 ->
      fun l2 ->
        let uu____16927 = FStar_Ident.lid_equals l1 l2 in
        if uu____16927
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____16935 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____16935
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____16943 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____16996 ->
                        match uu____16996 with
                        | (m1, m2, uu____17009, uu____17010, uu____17011) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____16943 with
              | FStar_Pervasives_Native.None ->
                  let uu____17028 =
                    let uu____17033 =
                      let uu____17034 = FStar_Syntax_Print.lid_to_string l1 in
                      let uu____17035 = FStar_Syntax_Print.lid_to_string l2 in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17034
                        uu____17035 in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17033) in
                  FStar_Errors.raise_error uu____17028 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17042, uu____17043, m3, j1, j2) -> (m3, j1, j2)))
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l1 ->
      fun l2 ->
        let uu____17076 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____17076
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux :
  'Auu____17092 .
    (FStar_Syntax_Syntax.eff_decl, 'Auu____17092)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls ->
    fun m ->
      let uu____17121 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17147 ->
                match uu____17147 with
                | (d, uu____17153) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____17121 with
      | FStar_Pervasives_Native.None ->
          let uu____17164 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____17164
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____17177 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____17177 with
           | (uu____17192, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____17210)::(wp, uu____17212)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17268 -> failwith "Impossible"))
let (wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  = fun env -> fun m -> wp_sig_aux (env.effects).decls m
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun eff_name ->
      fun res_u ->
        fun res_t ->
          let uu____17323 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid in
          if uu____17323
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17325 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid in
             if uu____17325
             then
               FStar_Syntax_Syntax.mk_GTotal' res_t
                 (FStar_Pervasives_Native.Some res_u)
             else
               (let eff_name1 = norm_eff_name env eff_name in
                let ed = get_effect_decl env eff_name1 in
                let null_wp =
                  inst_effect_fun_with [res_u] env ed
                    ed.FStar_Syntax_Syntax.null_wp in
                let null_wp_res =
                  let uu____17333 = get_range env in
                  let uu____17334 =
                    let uu____17341 =
                      let uu____17342 =
                        let uu____17359 =
                          let uu____17370 = FStar_Syntax_Syntax.as_arg res_t in
                          [uu____17370] in
                        (null_wp, uu____17359) in
                      FStar_Syntax_Syntax.Tm_app uu____17342 in
                    FStar_Syntax_Syntax.mk uu____17341 in
                  uu____17334 FStar_Pervasives_Native.None uu____17333 in
                let uu____17410 =
                  let uu____17411 =
                    let uu____17422 = FStar_Syntax_Syntax.as_arg null_wp_res in
                    [uu____17422] in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17411;
                    FStar_Syntax_Syntax.flags = []
                  } in
                FStar_Syntax_Syntax.mk_Comp uu____17410))
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___250_17459 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___250_17459.order);
              joins = (uu___250_17459.joins)
            } in
          let uu___251_17468 = env in
          {
            solver = (uu___251_17468.solver);
            range = (uu___251_17468.range);
            curmodule = (uu___251_17468.curmodule);
            gamma = (uu___251_17468.gamma);
            gamma_sig = (uu___251_17468.gamma_sig);
            gamma_cache = (uu___251_17468.gamma_cache);
            modules = (uu___251_17468.modules);
            expected_typ = (uu___251_17468.expected_typ);
            sigtab = (uu___251_17468.sigtab);
            attrtab = (uu___251_17468.attrtab);
            is_pattern = (uu___251_17468.is_pattern);
            instantiate_imp = (uu___251_17468.instantiate_imp);
            effects;
            generalize = (uu___251_17468.generalize);
            letrecs = (uu___251_17468.letrecs);
            top_level = (uu___251_17468.top_level);
            check_uvars = (uu___251_17468.check_uvars);
            use_eq = (uu___251_17468.use_eq);
            is_iface = (uu___251_17468.is_iface);
            admit = (uu___251_17468.admit);
            lax = (uu___251_17468.lax);
            lax_universes = (uu___251_17468.lax_universes);
            phase1 = (uu___251_17468.phase1);
            failhard = (uu___251_17468.failhard);
            nosynth = (uu___251_17468.nosynth);
            uvar_subtyping = (uu___251_17468.uvar_subtyping);
            tc_term = (uu___251_17468.tc_term);
            type_of = (uu___251_17468.type_of);
            universe_of = (uu___251_17468.universe_of);
            check_type_of = (uu___251_17468.check_type_of);
            use_bv_sorts = (uu___251_17468.use_bv_sorts);
            qtbl_name_and_index = (uu___251_17468.qtbl_name_and_index);
            normalized_eff_names = (uu___251_17468.normalized_eff_names);
            proof_ns = (uu___251_17468.proof_ns);
            synth_hook = (uu___251_17468.synth_hook);
            splice = (uu___251_17468.splice);
            is_native_tactic = (uu___251_17468.is_native_tactic);
            identifier_info = (uu___251_17468.identifier_info);
            tc_hooks = (uu___251_17468.tc_hooks);
            dsenv = (uu___251_17468.dsenv);
            nbe = (uu___251_17468.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____17498 = (e1.mlift).mlift_wp u r wp1 in
                (e2.mlift).mlift_wp u r uu____17498 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun wp ->
                              fun e ->
                                let uu____17656 = (e1.mlift).mlift_wp u t wp in
                                let uu____17657 = l1 u t wp e in
                                l2 u t uu____17656 uu____17657))
                | uu____17658 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____17730 = inst_tscheme_with lift_t [u] in
            match uu____17730 with
            | (uu____17737, lift_t1) ->
                let uu____17739 =
                  let uu____17746 =
                    let uu____17747 =
                      let uu____17764 =
                        let uu____17775 = FStar_Syntax_Syntax.as_arg r in
                        let uu____17784 =
                          let uu____17795 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____17795] in
                        uu____17775 :: uu____17784 in
                      (lift_t1, uu____17764) in
                    FStar_Syntax_Syntax.Tm_app uu____17747 in
                  FStar_Syntax_Syntax.mk uu____17746 in
                uu____17739 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____17907 = inst_tscheme_with lift_t [u] in
            match uu____17907 with
            | (uu____17914, lift_t1) ->
                let uu____17916 =
                  let uu____17923 =
                    let uu____17924 =
                      let uu____17941 =
                        let uu____17952 = FStar_Syntax_Syntax.as_arg r in
                        let uu____17961 =
                          let uu____17972 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____17981 =
                            let uu____17992 = FStar_Syntax_Syntax.as_arg e in
                            [uu____17992] in
                          uu____17972 :: uu____17981 in
                        uu____17952 :: uu____17961 in
                      (lift_t1, uu____17941) in
                    FStar_Syntax_Syntax.Tm_app uu____17924 in
                  FStar_Syntax_Syntax.mk uu____17923 in
                uu____17916 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            } in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            } in
          let print_mlift l =
            let bogus_term s =
              let uu____18094 =
                let uu____18095 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____18095
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____18094 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____18099 =
              let uu____18100 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp in
              FStar_Syntax_Print.term_to_string uu____18100 in
            let uu____18101 =
              let uu____18102 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1 ->
                     let uu____18128 = l1 FStar_Syntax_Syntax.U_zero arg wp e in
                     FStar_Syntax_Print.term_to_string uu____18128) in
              FStar_Util.dflt "none" uu____18102 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18099
              uu____18101 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18154 ->
                    match uu____18154 with
                    | (e, uu____18162) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____18185 =
            match uu____18185 with
            | (i, j) ->
                let uu____18196 = FStar_Ident.lid_equals i j in
                if uu____18196
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_16 -> FStar_Pervasives_Native.Some _0_16)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____18228 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i ->
                        let uu____18238 = FStar_Ident.lid_equals i k in
                        if uu____18238
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j ->
                                  let uu____18249 =
                                    FStar_Ident.lid_equals j k in
                                  if uu____18249
                                  then []
                                  else
                                    (let uu____18253 =
                                       let uu____18262 =
                                         find_edge order1 (i, k) in
                                       let uu____18265 =
                                         find_edge order1 (k, j) in
                                       (uu____18262, uu____18265) in
                                     match uu____18253 with
                                     | (FStar_Pervasives_Native.Some e1,
                                        FStar_Pervasives_Native.Some e2) ->
                                         let uu____18280 =
                                           compose_edges e1 e2 in
                                         [uu____18280]
                                     | uu____18281 -> []))))) in
              FStar_List.append order1 uu____18228 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1 ->
                 fun e2 ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1 ->
                   let uu____18311 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18313 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____18313
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____18311
                   then
                     let uu____18318 =
                       let uu____18323 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18323) in
                     let uu____18324 = get_range env in
                     FStar_Errors.raise_error uu____18318 uu____18324
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j ->
                              let join_opt =
                                let uu____18401 = FStar_Ident.lid_equals i j in
                                if uu____18401
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt ->
                                          fun k ->
                                            let uu____18450 =
                                              let uu____18459 =
                                                find_edge order2 (i, k) in
                                              let uu____18462 =
                                                find_edge order2 (j, k) in
                                              (uu____18459, uu____18462) in
                                            match uu____18450 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,
                                               FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub, uu____18504,
                                                      uu____18505)
                                                     ->
                                                     let uu____18512 =
                                                       let uu____18517 =
                                                         let uu____18518 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____18518 in
                                                       let uu____18521 =
                                                         let uu____18522 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____18522 in
                                                       (uu____18517,
                                                         uu____18521) in
                                                     (match uu____18512 with
                                                      | (true, true) ->
                                                          let uu____18533 =
                                                            FStar_Ident.lid_equals
                                                              k ub in
                                                          if uu____18533
                                                          then
                                                            (FStar_Errors.log_issue
                                                               FStar_Range.dummyRange
                                                               (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                 "Looking multiple times at the same upper bound candidate");
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false, false) ->
                                                          bopt
                                                      | (true, false) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false, true) -> bopt))
                                            | uu____18558 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None -> []
                              | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___252_18631 = env.effects in
              { decls = (uu___252_18631.decls); order = order2; joins } in
            let uu___253_18632 = env in
            {
              solver = (uu___253_18632.solver);
              range = (uu___253_18632.range);
              curmodule = (uu___253_18632.curmodule);
              gamma = (uu___253_18632.gamma);
              gamma_sig = (uu___253_18632.gamma_sig);
              gamma_cache = (uu___253_18632.gamma_cache);
              modules = (uu___253_18632.modules);
              expected_typ = (uu___253_18632.expected_typ);
              sigtab = (uu___253_18632.sigtab);
              attrtab = (uu___253_18632.attrtab);
              is_pattern = (uu___253_18632.is_pattern);
              instantiate_imp = (uu___253_18632.instantiate_imp);
              effects;
              generalize = (uu___253_18632.generalize);
              letrecs = (uu___253_18632.letrecs);
              top_level = (uu___253_18632.top_level);
              check_uvars = (uu___253_18632.check_uvars);
              use_eq = (uu___253_18632.use_eq);
              is_iface = (uu___253_18632.is_iface);
              admit = (uu___253_18632.admit);
              lax = (uu___253_18632.lax);
              lax_universes = (uu___253_18632.lax_universes);
              phase1 = (uu___253_18632.phase1);
              failhard = (uu___253_18632.failhard);
              nosynth = (uu___253_18632.nosynth);
              uvar_subtyping = (uu___253_18632.uvar_subtyping);
              tc_term = (uu___253_18632.tc_term);
              type_of = (uu___253_18632.type_of);
              universe_of = (uu___253_18632.universe_of);
              check_type_of = (uu___253_18632.check_type_of);
              use_bv_sorts = (uu___253_18632.use_bv_sorts);
              qtbl_name_and_index = (uu___253_18632.qtbl_name_and_index);
              normalized_eff_names = (uu___253_18632.normalized_eff_names);
              proof_ns = (uu___253_18632.proof_ns);
              synth_hook = (uu___253_18632.synth_hook);
              splice = (uu___253_18632.splice);
              is_native_tactic = (uu___253_18632.is_native_tactic);
              identifier_info = (uu___253_18632.identifier_info);
              tc_hooks = (uu___253_18632.tc_hooks);
              dsenv = (uu___253_18632.dsenv);
              nbe = (uu___253_18632.nbe)
            }))
      | uu____18633 -> env
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env ->
    fun c ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____18661 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env ->
    fun comp ->
      let c = comp_to_comp_typ env comp in
      let uu____18673 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____18673 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____18690 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____18690 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____18712 =
                     let uu____18717 =
                       let uu____18718 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____18725 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1")) in
                       let uu____18734 =
                         let uu____18735 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____18735 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____18718 uu____18725 uu____18734 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____18717) in
                   FStar_Errors.raise_error uu____18712
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____18740 =
                     let uu____18751 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____18751 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____18788 ->
                        fun uu____18789 ->
                          match (uu____18788, uu____18789) with
                          | ((x, uu____18819), (t, uu____18821)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____18740 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____18852 =
                     let uu___254_18853 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___254_18853.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___254_18853.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___254_18853.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___254_18853.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____18852
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux :
  'Auu____18864 .
    'Auu____18864 ->
      env ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.universe ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
              FStar_Pervasives_Native.option
  =
  fun only_reifiable ->
    fun env ->
      fun c ->
        fun u_c ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
          let uu____18894 = effect_decl_opt env effect_name in
          match uu____18894 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown ->
                   FStar_Pervasives_Native.None
               | uu____18933 ->
                   let c1 = unfold_effect_abbrev env c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____18956 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name in
                         let message =
                           let uu____18993 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name in
                           Prims.strcat uu____18993
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].") in
                         let uu____18994 = get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____18994 in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr)) in
                   let uu____19008 =
                     let uu____19011 = get_range env in
                     let uu____19012 =
                       let uu____19019 =
                         let uu____19020 =
                           let uu____19037 =
                             let uu____19048 =
                               FStar_Syntax_Syntax.as_arg res_typ in
                             [uu____19048; wp] in
                           (repr, uu____19037) in
                         FStar_Syntax_Syntax.Tm_app uu____19020 in
                       FStar_Syntax_Syntax.mk uu____19019 in
                     uu____19012 FStar_Pervasives_Native.None uu____19011 in
                   FStar_Pervasives_Native.Some uu____19008)
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env -> fun c -> fun u_c -> effect_repr_aux false env c u_c
let (is_user_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env effect_lid in
      let quals = lookup_effect_quals env effect_lid1 in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun effect_lid ->
      let effect_lid1 = norm_eff_name env effect_lid in
      (is_user_reifiable_effect env effect_lid1) ||
        (FStar_Ident.lid_equals effect_lid1 FStar_Parser_Const.effect_TAC_lid)
let (is_reifiable_rc :
  env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env ->
    fun c -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____19163 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____19174 =
        let uu____19175 = FStar_Syntax_Subst.compress t in
        uu____19175.FStar_Syntax_Syntax.n in
      match uu____19174 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19178, c) ->
          is_reifiable_comp env c
      | uu____19200 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu____19218 =
           let uu____19219 = is_reifiable_effect env l in
           Prims.op_Negation uu____19219 in
         if uu____19218
         then
           let uu____19220 =
             let uu____19225 =
               let uu____19226 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19226 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19225) in
           let uu____19227 = get_range env in
           FStar_Errors.raise_error uu____19220 uu____19227
         else ());
        (let uu____19229 = effect_repr_aux true env c u_c in
         match uu____19229 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env1 =
        let uu___255_19261 = env in
        {
          solver = (uu___255_19261.solver);
          range = (uu___255_19261.range);
          curmodule = (uu___255_19261.curmodule);
          gamma = (uu___255_19261.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___255_19261.gamma_cache);
          modules = (uu___255_19261.modules);
          expected_typ = (uu___255_19261.expected_typ);
          sigtab = (uu___255_19261.sigtab);
          attrtab = (uu___255_19261.attrtab);
          is_pattern = (uu___255_19261.is_pattern);
          instantiate_imp = (uu___255_19261.instantiate_imp);
          effects = (uu___255_19261.effects);
          generalize = (uu___255_19261.generalize);
          letrecs = (uu___255_19261.letrecs);
          top_level = (uu___255_19261.top_level);
          check_uvars = (uu___255_19261.check_uvars);
          use_eq = (uu___255_19261.use_eq);
          is_iface = (uu___255_19261.is_iface);
          admit = (uu___255_19261.admit);
          lax = (uu___255_19261.lax);
          lax_universes = (uu___255_19261.lax_universes);
          phase1 = (uu___255_19261.phase1);
          failhard = (uu___255_19261.failhard);
          nosynth = (uu___255_19261.nosynth);
          uvar_subtyping = (uu___255_19261.uvar_subtyping);
          tc_term = (uu___255_19261.tc_term);
          type_of = (uu___255_19261.type_of);
          universe_of = (uu___255_19261.universe_of);
          check_type_of = (uu___255_19261.check_type_of);
          use_bv_sorts = (uu___255_19261.use_bv_sorts);
          qtbl_name_and_index = (uu___255_19261.qtbl_name_and_index);
          normalized_eff_names = (uu___255_19261.normalized_eff_names);
          proof_ns = (uu___255_19261.proof_ns);
          synth_hook = (uu___255_19261.synth_hook);
          splice = (uu___255_19261.splice);
          is_native_tactic = (uu___255_19261.is_native_tactic);
          identifier_info = (uu___255_19261.identifier_info);
          tc_hooks = (uu___255_19261.tc_hooks);
          dsenv = (uu___255_19261.dsenv);
          nbe = (uu___255_19261.nbe)
        } in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env ->
    fun b ->
      let uu___256_19274 = env in
      {
        solver = (uu___256_19274.solver);
        range = (uu___256_19274.range);
        curmodule = (uu___256_19274.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___256_19274.gamma_sig);
        gamma_cache = (uu___256_19274.gamma_cache);
        modules = (uu___256_19274.modules);
        expected_typ = (uu___256_19274.expected_typ);
        sigtab = (uu___256_19274.sigtab);
        attrtab = (uu___256_19274.attrtab);
        is_pattern = (uu___256_19274.is_pattern);
        instantiate_imp = (uu___256_19274.instantiate_imp);
        effects = (uu___256_19274.effects);
        generalize = (uu___256_19274.generalize);
        letrecs = (uu___256_19274.letrecs);
        top_level = (uu___256_19274.top_level);
        check_uvars = (uu___256_19274.check_uvars);
        use_eq = (uu___256_19274.use_eq);
        is_iface = (uu___256_19274.is_iface);
        admit = (uu___256_19274.admit);
        lax = (uu___256_19274.lax);
        lax_universes = (uu___256_19274.lax_universes);
        phase1 = (uu___256_19274.phase1);
        failhard = (uu___256_19274.failhard);
        nosynth = (uu___256_19274.nosynth);
        uvar_subtyping = (uu___256_19274.uvar_subtyping);
        tc_term = (uu___256_19274.tc_term);
        type_of = (uu___256_19274.type_of);
        universe_of = (uu___256_19274.universe_of);
        check_type_of = (uu___256_19274.check_type_of);
        use_bv_sorts = (uu___256_19274.use_bv_sorts);
        qtbl_name_and_index = (uu___256_19274.qtbl_name_and_index);
        normalized_eff_names = (uu___256_19274.normalized_eff_names);
        proof_ns = (uu___256_19274.proof_ns);
        synth_hook = (uu___256_19274.synth_hook);
        splice = (uu___256_19274.splice);
        is_native_tactic = (uu___256_19274.is_native_tactic);
        identifier_info = (uu___256_19274.identifier_info);
        tc_hooks = (uu___256_19274.tc_hooks);
        dsenv = (uu___256_19274.dsenv);
        nbe = (uu___256_19274.nbe)
      }
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env ->
    fun x -> push_local_binding env (FStar_Syntax_Syntax.Binding_var x)
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env ->
    fun bvs ->
      FStar_List.fold_left (fun env1 -> fun bv -> push_bv env1 bv) env bvs
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv, env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env ->
    match env.gamma with
    | (FStar_Syntax_Syntax.Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___257_19329 = env in
             {
               solver = (uu___257_19329.solver);
               range = (uu___257_19329.range);
               curmodule = (uu___257_19329.curmodule);
               gamma = rest;
               gamma_sig = (uu___257_19329.gamma_sig);
               gamma_cache = (uu___257_19329.gamma_cache);
               modules = (uu___257_19329.modules);
               expected_typ = (uu___257_19329.expected_typ);
               sigtab = (uu___257_19329.sigtab);
               attrtab = (uu___257_19329.attrtab);
               is_pattern = (uu___257_19329.is_pattern);
               instantiate_imp = (uu___257_19329.instantiate_imp);
               effects = (uu___257_19329.effects);
               generalize = (uu___257_19329.generalize);
               letrecs = (uu___257_19329.letrecs);
               top_level = (uu___257_19329.top_level);
               check_uvars = (uu___257_19329.check_uvars);
               use_eq = (uu___257_19329.use_eq);
               is_iface = (uu___257_19329.is_iface);
               admit = (uu___257_19329.admit);
               lax = (uu___257_19329.lax);
               lax_universes = (uu___257_19329.lax_universes);
               phase1 = (uu___257_19329.phase1);
               failhard = (uu___257_19329.failhard);
               nosynth = (uu___257_19329.nosynth);
               uvar_subtyping = (uu___257_19329.uvar_subtyping);
               tc_term = (uu___257_19329.tc_term);
               type_of = (uu___257_19329.type_of);
               universe_of = (uu___257_19329.universe_of);
               check_type_of = (uu___257_19329.check_type_of);
               use_bv_sorts = (uu___257_19329.use_bv_sorts);
               qtbl_name_and_index = (uu___257_19329.qtbl_name_and_index);
               normalized_eff_names = (uu___257_19329.normalized_eff_names);
               proof_ns = (uu___257_19329.proof_ns);
               synth_hook = (uu___257_19329.synth_hook);
               splice = (uu___257_19329.splice);
               is_native_tactic = (uu___257_19329.is_native_tactic);
               identifier_info = (uu___257_19329.identifier_info);
               tc_hooks = (uu___257_19329.tc_hooks);
               dsenv = (uu___257_19329.dsenv);
               nbe = (uu___257_19329.nbe)
             }))
    | uu____19330 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env ->
    fun bs ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____19358 ->
             match uu____19358 with | (x, uu____19366) -> push_bv env1 x) env
        bs
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> FStar_Syntax_Syntax.binding)
  =
  fun x ->
    fun t ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___258_19400 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___258_19400.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___258_19400.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          FStar_Syntax_Syntax.Binding_var x2
      | FStar_Util.Inr fv ->
          FStar_Syntax_Syntax.Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env -> fun lb -> fun ts -> push_local_binding env (binding_of_lb lb ts)
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env ->
    fun m ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___259_19440 = env in
       {
         solver = (uu___259_19440.solver);
         range = (uu___259_19440.range);
         curmodule = (uu___259_19440.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___259_19440.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___259_19440.sigtab);
         attrtab = (uu___259_19440.attrtab);
         is_pattern = (uu___259_19440.is_pattern);
         instantiate_imp = (uu___259_19440.instantiate_imp);
         effects = (uu___259_19440.effects);
         generalize = (uu___259_19440.generalize);
         letrecs = (uu___259_19440.letrecs);
         top_level = (uu___259_19440.top_level);
         check_uvars = (uu___259_19440.check_uvars);
         use_eq = (uu___259_19440.use_eq);
         is_iface = (uu___259_19440.is_iface);
         admit = (uu___259_19440.admit);
         lax = (uu___259_19440.lax);
         lax_universes = (uu___259_19440.lax_universes);
         phase1 = (uu___259_19440.phase1);
         failhard = (uu___259_19440.failhard);
         nosynth = (uu___259_19440.nosynth);
         uvar_subtyping = (uu___259_19440.uvar_subtyping);
         tc_term = (uu___259_19440.tc_term);
         type_of = (uu___259_19440.type_of);
         universe_of = (uu___259_19440.universe_of);
         check_type_of = (uu___259_19440.check_type_of);
         use_bv_sorts = (uu___259_19440.use_bv_sorts);
         qtbl_name_and_index = (uu___259_19440.qtbl_name_and_index);
         normalized_eff_names = (uu___259_19440.normalized_eff_names);
         proof_ns = (uu___259_19440.proof_ns);
         synth_hook = (uu___259_19440.synth_hook);
         splice = (uu___259_19440.splice);
         is_native_tactic = (uu___259_19440.is_native_tactic);
         identifier_info = (uu___259_19440.identifier_info);
         tc_hooks = (uu___259_19440.tc_hooks);
         dsenv = (uu___259_19440.dsenv);
         nbe = (uu___259_19440.nbe)
       })
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env ->
    fun xs ->
      FStar_List.fold_left
        (fun env1 ->
           fun x ->
             push_local_binding env1 (FStar_Syntax_Syntax.Binding_univ x))
        env xs
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env, FStar_Syntax_Syntax.univ_names,
          FStar_Syntax_Syntax.term Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun uvs ->
      fun terms ->
        let uu____19482 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____19482 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____19510 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____19510)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env ->
    fun t ->
      let uu___260_19525 = env in
      {
        solver = (uu___260_19525.solver);
        range = (uu___260_19525.range);
        curmodule = (uu___260_19525.curmodule);
        gamma = (uu___260_19525.gamma);
        gamma_sig = (uu___260_19525.gamma_sig);
        gamma_cache = (uu___260_19525.gamma_cache);
        modules = (uu___260_19525.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___260_19525.sigtab);
        attrtab = (uu___260_19525.attrtab);
        is_pattern = (uu___260_19525.is_pattern);
        instantiate_imp = (uu___260_19525.instantiate_imp);
        effects = (uu___260_19525.effects);
        generalize = (uu___260_19525.generalize);
        letrecs = (uu___260_19525.letrecs);
        top_level = (uu___260_19525.top_level);
        check_uvars = (uu___260_19525.check_uvars);
        use_eq = false;
        is_iface = (uu___260_19525.is_iface);
        admit = (uu___260_19525.admit);
        lax = (uu___260_19525.lax);
        lax_universes = (uu___260_19525.lax_universes);
        phase1 = (uu___260_19525.phase1);
        failhard = (uu___260_19525.failhard);
        nosynth = (uu___260_19525.nosynth);
        uvar_subtyping = (uu___260_19525.uvar_subtyping);
        tc_term = (uu___260_19525.tc_term);
        type_of = (uu___260_19525.type_of);
        universe_of = (uu___260_19525.universe_of);
        check_type_of = (uu___260_19525.check_type_of);
        use_bv_sorts = (uu___260_19525.use_bv_sorts);
        qtbl_name_and_index = (uu___260_19525.qtbl_name_and_index);
        normalized_eff_names = (uu___260_19525.normalized_eff_names);
        proof_ns = (uu___260_19525.proof_ns);
        synth_hook = (uu___260_19525.synth_hook);
        splice = (uu___260_19525.splice);
        is_native_tactic = (uu___260_19525.is_native_tactic);
        identifier_info = (uu___260_19525.identifier_info);
        tc_hooks = (uu___260_19525.tc_hooks);
        dsenv = (uu___260_19525.dsenv);
        nbe = (uu___260_19525.nbe)
      }
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let (clear_expected_typ :
  env ->
    (env, FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun env_ ->
    let uu____19553 = expected_typ env_ in
    ((let uu___261_19559 = env_ in
      {
        solver = (uu___261_19559.solver);
        range = (uu___261_19559.range);
        curmodule = (uu___261_19559.curmodule);
        gamma = (uu___261_19559.gamma);
        gamma_sig = (uu___261_19559.gamma_sig);
        gamma_cache = (uu___261_19559.gamma_cache);
        modules = (uu___261_19559.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___261_19559.sigtab);
        attrtab = (uu___261_19559.attrtab);
        is_pattern = (uu___261_19559.is_pattern);
        instantiate_imp = (uu___261_19559.instantiate_imp);
        effects = (uu___261_19559.effects);
        generalize = (uu___261_19559.generalize);
        letrecs = (uu___261_19559.letrecs);
        top_level = (uu___261_19559.top_level);
        check_uvars = (uu___261_19559.check_uvars);
        use_eq = false;
        is_iface = (uu___261_19559.is_iface);
        admit = (uu___261_19559.admit);
        lax = (uu___261_19559.lax);
        lax_universes = (uu___261_19559.lax_universes);
        phase1 = (uu___261_19559.phase1);
        failhard = (uu___261_19559.failhard);
        nosynth = (uu___261_19559.nosynth);
        uvar_subtyping = (uu___261_19559.uvar_subtyping);
        tc_term = (uu___261_19559.tc_term);
        type_of = (uu___261_19559.type_of);
        universe_of = (uu___261_19559.universe_of);
        check_type_of = (uu___261_19559.check_type_of);
        use_bv_sorts = (uu___261_19559.use_bv_sorts);
        qtbl_name_and_index = (uu___261_19559.qtbl_name_and_index);
        normalized_eff_names = (uu___261_19559.normalized_eff_names);
        proof_ns = (uu___261_19559.proof_ns);
        synth_hook = (uu___261_19559.synth_hook);
        splice = (uu___261_19559.splice);
        is_native_tactic = (uu___261_19559.is_native_tactic);
        identifier_info = (uu___261_19559.identifier_info);
        tc_hooks = (uu___261_19559.tc_hooks);
        dsenv = (uu___261_19559.dsenv);
        nbe = (uu___261_19559.nbe)
      }), uu____19553)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____19569 =
      let uu____19572 = FStar_Ident.id_of_text "" in [uu____19572] in
    FStar_Ident.lid_of_ids uu____19569 in
  fun env ->
    fun m ->
      let sigs =
        let uu____19578 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____19578
        then
          let uu____19581 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu____19581 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___262_19608 = env in
       {
         solver = (uu___262_19608.solver);
         range = (uu___262_19608.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___262_19608.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___262_19608.expected_typ);
         sigtab = (uu___262_19608.sigtab);
         attrtab = (uu___262_19608.attrtab);
         is_pattern = (uu___262_19608.is_pattern);
         instantiate_imp = (uu___262_19608.instantiate_imp);
         effects = (uu___262_19608.effects);
         generalize = (uu___262_19608.generalize);
         letrecs = (uu___262_19608.letrecs);
         top_level = (uu___262_19608.top_level);
         check_uvars = (uu___262_19608.check_uvars);
         use_eq = (uu___262_19608.use_eq);
         is_iface = (uu___262_19608.is_iface);
         admit = (uu___262_19608.admit);
         lax = (uu___262_19608.lax);
         lax_universes = (uu___262_19608.lax_universes);
         phase1 = (uu___262_19608.phase1);
         failhard = (uu___262_19608.failhard);
         nosynth = (uu___262_19608.nosynth);
         uvar_subtyping = (uu___262_19608.uvar_subtyping);
         tc_term = (uu___262_19608.tc_term);
         type_of = (uu___262_19608.type_of);
         universe_of = (uu___262_19608.universe_of);
         check_type_of = (uu___262_19608.check_type_of);
         use_bv_sorts = (uu___262_19608.use_bv_sorts);
         qtbl_name_and_index = (uu___262_19608.qtbl_name_and_index);
         normalized_eff_names = (uu___262_19608.normalized_eff_names);
         proof_ns = (uu___262_19608.proof_ns);
         synth_hook = (uu___262_19608.synth_hook);
         splice = (uu___262_19608.splice);
         is_native_tactic = (uu___262_19608.is_native_tactic);
         identifier_info = (uu___262_19608.identifier_info);
         tc_hooks = (uu___262_19608.tc_hooks);
         dsenv = (uu___262_19608.dsenv);
         nbe = (uu___262_19608.nbe)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19659)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid
          (uu____19663, (uu____19664, t)))::tl1 ->
          let uu____19685 =
            let uu____19688 = FStar_Syntax_Free.uvars t in
            ext out uu____19688 in
          aux uu____19685 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19691;
            FStar_Syntax_Syntax.index = uu____19692;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19699 =
            let uu____19702 = FStar_Syntax_Free.uvars t in
            ext out uu____19702 in
          aux uu____19699 tl1 in
    aux no_uvs env.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____19759)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid
          (uu____19763, (uu____19764, t)))::tl1 ->
          let uu____19785 =
            let uu____19788 = FStar_Syntax_Free.univs t in
            ext out uu____19788 in
          aux uu____19785 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19791;
            FStar_Syntax_Syntax.index = uu____19792;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19799 =
            let uu____19802 = FStar_Syntax_Free.univs t in
            ext out uu____19802 in
          aux uu____19799 tl1 in
    aux no_univs env.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____19863 = FStar_Util.set_add uname out in
          aux uu____19863 tl1
      | (FStar_Syntax_Syntax.Binding_lid
          (uu____19866, (uu____19867, t)))::tl1 ->
          let uu____19888 =
            let uu____19891 = FStar_Syntax_Free.univnames t in
            ext out uu____19891 in
          aux uu____19888 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____19894;
            FStar_Syntax_Syntax.index = uu____19895;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____19902 =
            let uu____19905 = FStar_Syntax_Free.univnames t in
            ext out uu____19905 in
          aux uu____19902 tl1 in
    aux no_univ_names env.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___236_19925 ->
            match uu___236_19925 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____19929 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____19942 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____19952 =
      let uu____19961 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____19961
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____19952 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env -> bound_vars_of_bindings env.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env -> binders_of_bindings env.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu____20005 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___237_20015 ->
              match uu___237_20015 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20017 = FStar_Syntax_Print.bv_to_string x in
                  Prims.strcat "Binding_var " uu____20017
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l, uu____20020) ->
                  let uu____20037 = FStar_Ident.string_of_lid l in
                  Prims.strcat "Binding_lid " uu____20037)) in
    FStar_All.pipe_right uu____20005 (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___238_20044 ->
    match uu___238_20044 with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20046 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.strcat "Unfold " uu____20046
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20066 ->
         fun v1 ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env ->
    fun path ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([], uu____20108) -> true
        | (x::xs1, y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20127, uu____20128) -> false in
      let uu____20137 =
        FStar_List.tryFind
          (fun uu____20155 ->
             match uu____20155 with | (p, uu____20163) -> list_prefix p path)
          env.proof_ns in
      match uu____20137 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____20174, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____20196 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____20196
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___263_20214 = e in
        {
          solver = (uu___263_20214.solver);
          range = (uu___263_20214.range);
          curmodule = (uu___263_20214.curmodule);
          gamma = (uu___263_20214.gamma);
          gamma_sig = (uu___263_20214.gamma_sig);
          gamma_cache = (uu___263_20214.gamma_cache);
          modules = (uu___263_20214.modules);
          expected_typ = (uu___263_20214.expected_typ);
          sigtab = (uu___263_20214.sigtab);
          attrtab = (uu___263_20214.attrtab);
          is_pattern = (uu___263_20214.is_pattern);
          instantiate_imp = (uu___263_20214.instantiate_imp);
          effects = (uu___263_20214.effects);
          generalize = (uu___263_20214.generalize);
          letrecs = (uu___263_20214.letrecs);
          top_level = (uu___263_20214.top_level);
          check_uvars = (uu___263_20214.check_uvars);
          use_eq = (uu___263_20214.use_eq);
          is_iface = (uu___263_20214.is_iface);
          admit = (uu___263_20214.admit);
          lax = (uu___263_20214.lax);
          lax_universes = (uu___263_20214.lax_universes);
          phase1 = (uu___263_20214.phase1);
          failhard = (uu___263_20214.failhard);
          nosynth = (uu___263_20214.nosynth);
          uvar_subtyping = (uu___263_20214.uvar_subtyping);
          tc_term = (uu___263_20214.tc_term);
          type_of = (uu___263_20214.type_of);
          universe_of = (uu___263_20214.universe_of);
          check_type_of = (uu___263_20214.check_type_of);
          use_bv_sorts = (uu___263_20214.use_bv_sorts);
          qtbl_name_and_index = (uu___263_20214.qtbl_name_and_index);
          normalized_eff_names = (uu___263_20214.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___263_20214.synth_hook);
          splice = (uu___263_20214.splice);
          is_native_tactic = (uu___263_20214.is_native_tactic);
          identifier_info = (uu___263_20214.identifier_info);
          tc_hooks = (uu___263_20214.tc_hooks);
          dsenv = (uu___263_20214.dsenv);
          nbe = (uu___263_20214.nbe)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___264_20254 = e in
      {
        solver = (uu___264_20254.solver);
        range = (uu___264_20254.range);
        curmodule = (uu___264_20254.curmodule);
        gamma = (uu___264_20254.gamma);
        gamma_sig = (uu___264_20254.gamma_sig);
        gamma_cache = (uu___264_20254.gamma_cache);
        modules = (uu___264_20254.modules);
        expected_typ = (uu___264_20254.expected_typ);
        sigtab = (uu___264_20254.sigtab);
        attrtab = (uu___264_20254.attrtab);
        is_pattern = (uu___264_20254.is_pattern);
        instantiate_imp = (uu___264_20254.instantiate_imp);
        effects = (uu___264_20254.effects);
        generalize = (uu___264_20254.generalize);
        letrecs = (uu___264_20254.letrecs);
        top_level = (uu___264_20254.top_level);
        check_uvars = (uu___264_20254.check_uvars);
        use_eq = (uu___264_20254.use_eq);
        is_iface = (uu___264_20254.is_iface);
        admit = (uu___264_20254.admit);
        lax = (uu___264_20254.lax);
        lax_universes = (uu___264_20254.lax_universes);
        phase1 = (uu___264_20254.phase1);
        failhard = (uu___264_20254.failhard);
        nosynth = (uu___264_20254.nosynth);
        uvar_subtyping = (uu___264_20254.uvar_subtyping);
        tc_term = (uu___264_20254.tc_term);
        type_of = (uu___264_20254.type_of);
        universe_of = (uu___264_20254.universe_of);
        check_type_of = (uu___264_20254.check_type_of);
        use_bv_sorts = (uu___264_20254.use_bv_sorts);
        qtbl_name_and_index = (uu___264_20254.qtbl_name_and_index);
        normalized_eff_names = (uu___264_20254.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___264_20254.synth_hook);
        splice = (uu___264_20254.splice);
        is_native_tactic = (uu___264_20254.is_native_tactic);
        identifier_info = (uu___264_20254.identifier_info);
        tc_hooks = (uu___264_20254.tc_hooks);
        dsenv = (uu___264_20254.dsenv);
        nbe = (uu___264_20254.nbe)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____20269 = FStar_Syntax_Free.names t in
      let uu____20272 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____20269 uu____20272
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____20293 = unbound_vars e t in
      FStar_Util.set_is_empty uu____20293
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____20301 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____20301
let (string_of_proof_ns : env -> Prims.string) =
  fun env ->
    let aux uu____20318 =
      match uu____20318 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20328 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____20328) in
    let uu____20330 =
      let uu____20333 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____20333 FStar_List.rev in
    FStar_All.pipe_right uu____20330 (FStar_String.concat " ")
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> guard_t) =
  fun g ->
    { guard_f = g; deferred = []; univ_ineqs = ([], []); implicits = [] }
let (guard_form : guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g -> g.guard_f
let (is_trivial : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial; deferred = [];
        univ_ineqs = ([], []); implicits = i;_} ->
        FStar_All.pipe_right i
          (FStar_Util.for_all
             (fun imp ->
                ((imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_should_check =
                   FStar_Syntax_Syntax.Allow_unresolved)
                  ||
                  (let uu____20386 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu____20386 with
                   | FStar_Pervasives_Native.Some uu____20389 -> true
                   | FStar_Pervasives_Native.None -> false)))
    | uu____20390 -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial; deferred = uu____20396;
        univ_ineqs = uu____20397; implicits = uu____20398;_} -> true
    | uu____20409 -> false
let (trivial_guard : guard_t) =
  {
    guard_f = FStar_TypeChecker_Common.Trivial;
    deferred = [];
    univ_ineqs = ([], []);
    implicits = []
  }
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list -> guard_t -> guard_t) =
  fun bs ->
    fun g ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0)) in
          let uu___265_20436 = g in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___265_20436.deferred);
            univ_ineqs = (uu___265_20436.univ_ineqs);
            implicits = (uu___265_20436.implicits)
          }
let (abstract_guard : FStar_Syntax_Syntax.binder -> guard_t -> guard_t) =
  fun b -> fun g -> abstract_guard_n [b] g
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun vset ->
        fun t ->
          let uu____20471 = FStar_Options.defensive () in
          if uu____20471
          then
            let s = FStar_Syntax_Free.names t in
            let uu____20475 =
              let uu____20476 =
                let uu____20477 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____20477 in
              Prims.op_Negation uu____20476 in
            (if uu____20475
             then
               let uu____20482 =
                 let uu____20487 =
                   let uu____20488 = FStar_Syntax_Print.term_to_string t in
                   let uu____20489 =
                     let uu____20490 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____20490
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____20488 uu____20489 in
                 (FStar_Errors.Warning_Defensive, uu____20487) in
               FStar_Errors.log_issue rng uu____20482
             else ())
          else ()
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun l ->
        fun t ->
          let uu____20521 =
            let uu____20522 = FStar_Options.defensive () in
            Prims.op_Negation uu____20522 in
          if uu____20521
          then ()
          else
            (let uu____20524 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____20524 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____20547 =
            let uu____20548 = FStar_Options.defensive () in
            Prims.op_Negation uu____20548 in
          if uu____20547
          then ()
          else
            (let uu____20550 = bound_vars e in
             def_check_closed_in rng msg uu____20550 t)
let (def_check_guard_wf :
  FStar_Range.range -> Prims.string -> env -> guard_t -> unit) =
  fun rng ->
    fun msg ->
      fun env ->
        fun g ->
          match g.guard_f with
          | FStar_TypeChecker_Common.Trivial -> ()
          | FStar_TypeChecker_Common.NonTrivial f ->
              def_check_closed_in_env rng msg env f
let (apply_guard : guard_t -> FStar_Syntax_Syntax.term -> guard_t) =
  fun g ->
    fun e ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___266_20585 = g in
          let uu____20586 =
            let uu____20587 =
              let uu____20588 =
                let uu____20595 =
                  let uu____20596 =
                    let uu____20613 =
                      let uu____20624 = FStar_Syntax_Syntax.as_arg e in
                      [uu____20624] in
                    (f, uu____20613) in
                  FStar_Syntax_Syntax.Tm_app uu____20596 in
                FStar_Syntax_Syntax.mk uu____20595 in
              uu____20588 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_17 -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____20587 in
          {
            guard_f = uu____20586;
            deferred = (uu___266_20585.deferred);
            univ_ineqs = (uu___266_20585.univ_ineqs);
            implicits = (uu___266_20585.implicits)
          }
let (map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map1 ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___267_20680 = g in
          let uu____20681 =
            let uu____20682 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____20682 in
          {
            guard_f = uu____20681;
            deferred = (uu___267_20680.deferred);
            univ_ineqs = (uu___267_20680.univ_ineqs);
            implicits = (uu___267_20680.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map1 ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___268_20698 = g in
          let uu____20699 =
            let uu____20700 = map1 FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu____20700 in
          {
            guard_f = uu____20699;
            deferred = (uu___268_20698.deferred);
            univ_ineqs = (uu___268_20698.univ_ineqs);
            implicits = (uu___268_20698.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___269_20702 = g in
          let uu____20703 =
            let uu____20704 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____20704 in
          {
            guard_f = uu____20703;
            deferred = (uu___269_20702.deferred);
            univ_ineqs = (uu___269_20702.univ_ineqs);
            implicits = (uu___269_20702.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____20710 ->
        failwith "impossible"
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial, g) -> g
      | (g, FStar_TypeChecker_Common.Trivial) -> g
      | (FStar_TypeChecker_Common.NonTrivial f1,
         FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____20725 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____20725
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t ->
    let uu____20731 =
      let uu____20732 = FStar_Syntax_Util.unmeta t in
      uu____20732.FStar_Syntax_Syntax.n in
    match uu____20731 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____20736 -> FStar_TypeChecker_Common.NonTrivial t
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1 ->
    fun g2 ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial, g) -> g
      | (g, FStar_TypeChecker_Common.Trivial) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial f1,
         FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    -> guard_t -> guard_t -> guard_t)
  =
  fun f ->
    fun g1 ->
      fun g2 ->
        let uu____20777 = f g1.guard_f g2.guard_f in
        {
          guard_f = uu____20777;
          deferred = (FStar_List.append g1.deferred g2.deferred);
          univ_ineqs =
            ((FStar_List.append (FStar_Pervasives_Native.fst g1.univ_ineqs)
                (FStar_Pervasives_Native.fst g2.univ_ineqs)),
              (FStar_List.append (FStar_Pervasives_Native.snd g1.univ_ineqs)
                 (FStar_Pervasives_Native.snd g2.univ_ineqs)));
          implicits = (FStar_List.append g1.implicits g2.implicits)
        }
let (conj_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard conj_guard_f g1 g2
let (imp_guard : guard_t -> guard_t -> guard_t) =
  fun g1 -> fun g2 -> binop_guard imp_guard_f g1 g2
let (conj_guards : guard_t Prims.list -> guard_t) =
  fun gs -> FStar_List.fold_left conj_guard trivial_guard gs
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun us ->
    fun bs ->
      fun g ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u ->
                   fun b ->
                     fun f1 ->
                       let uu____20867 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____20867
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___270_20871 = g in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___270_20871.deferred);
              univ_ineqs = (uu___270_20871.univ_ineqs);
              implicits = (uu___270_20871.implicits)
            }
let (close_forall :
  env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun bs ->
      fun f ->
        FStar_List.fold_right
          (fun b ->
             fun f1 ->
               let uu____20904 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____20904
               then f1
               else
                 (let u =
                    env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
let (close_guard : env -> FStar_Syntax_Syntax.binders -> guard_t -> guard_t)
  =
  fun env ->
    fun binders ->
      fun g ->
        match g.guard_f with
        | FStar_TypeChecker_Common.Trivial -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___271_20927 = g in
            let uu____20928 =
              let uu____20929 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____20929 in
            {
              guard_f = uu____20928;
              deferred = (uu___271_20927.deferred);
              univ_ineqs = (uu___271_20927.univ_ineqs);
              implicits = (uu___271_20927.implicits)
            }
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      env ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term,
              (FStar_Syntax_Syntax.ctx_uvar, FStar_Range.range)
                FStar_Pervasives_Native.tuple2 Prims.list,
              guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun reason ->
    fun r ->
      fun env ->
        fun k ->
          fun should_check ->
            let uu____20967 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
            match uu____20967 with
            | FStar_Pervasives_Native.Some
                (uu____20992::(tm, uu____20994)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
                (t, [], trivial_guard)
            | uu____21058 ->
                let binders = all_binders env in
                let gamma = env.gamma in
                let ctx_uvar =
                  let uu____21076 = FStar_Syntax_Unionfind.fresh () in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21076;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  } in
                (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                   true gamma binders;
                 (let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_uvar
                         (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                      FStar_Pervasives_Native.None r in
                  let imp =
                    {
                      imp_reason = reason;
                      imp_uvar = ctx_uvar;
                      imp_tm = t;
                      imp_range = r;
                      imp_meta = FStar_Pervasives_Native.None
                    } in
                  let g =
                    let uu___272_21111 = trivial_guard in
                    {
                      guard_f = (uu___272_21111.guard_f);
                      deferred = (uu___272_21111.deferred);
                      univ_ineqs = (uu___272_21111.univ_ineqs);
                      implicits = [imp]
                    } in
                  (t, [(ctx_uvar, r)], g)))
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21128 -> ());
    push = (fun uu____21130 -> ());
    pop = (fun uu____21132 -> ());
    snapshot =
      (fun uu____21134 ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21143 -> fun uu____21144 -> ());
    encode_modul = (fun uu____21155 -> fun uu____21156 -> ());
    encode_sig = (fun uu____21159 -> fun uu____21160 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____21166 =
             let uu____21173 = FStar_Options.peek () in (e, g, uu____21173) in
           [uu____21166]);
    solve = (fun uu____21189 -> fun uu____21190 -> fun uu____21191 -> ());
    finish = (fun uu____21197 -> ());
    refresh = (fun uu____21199 -> ())
  }