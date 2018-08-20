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
  fv_delta_depths: FStar_Syntax_Syntax.delta_depth FStar_Util.smap ;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__normalized_eff_names
let (__proj__Mkenv__item__fv_delta_depths :
  env -> FStar_Syntax_Syntax.delta_depth FStar_Util.smap) =
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
        fv_delta_depths = __fname__fv_delta_depths;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        nbe = __fname__nbe;_} -> __fname__fv_delta_depths
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
        fv_delta_depths = __fname__fv_delta_depths;
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
           (fun uu___225_9955 ->
              match uu___225_9955 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let y =
                    let uu____9958 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____9958 in
                  let uu____9959 =
                    let uu____9960 = FStar_Syntax_Subst.compress y in
                    uu____9960.FStar_Syntax_Syntax.n in
                  (match uu____9959 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____9964 =
                         let uu___239_9965 = y1 in
                         let uu____9966 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___239_9965.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___239_9965.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____9966
                         } in
                       FStar_Syntax_Syntax.Binding_var uu____9964
                   | uu____9969 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1 ->
    fun env ->
      let uu___240_9981 = env in
      let uu____9982 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___240_9981.solver);
        range = (uu___240_9981.range);
        curmodule = (uu___240_9981.curmodule);
        gamma = uu____9982;
        gamma_sig = (uu___240_9981.gamma_sig);
        gamma_cache = (uu___240_9981.gamma_cache);
        modules = (uu___240_9981.modules);
        expected_typ = (uu___240_9981.expected_typ);
        sigtab = (uu___240_9981.sigtab);
        attrtab = (uu___240_9981.attrtab);
        is_pattern = (uu___240_9981.is_pattern);
        instantiate_imp = (uu___240_9981.instantiate_imp);
        effects = (uu___240_9981.effects);
        generalize = (uu___240_9981.generalize);
        letrecs = (uu___240_9981.letrecs);
        top_level = (uu___240_9981.top_level);
        check_uvars = (uu___240_9981.check_uvars);
        use_eq = (uu___240_9981.use_eq);
        is_iface = (uu___240_9981.is_iface);
        admit = (uu___240_9981.admit);
        lax = (uu___240_9981.lax);
        lax_universes = (uu___240_9981.lax_universes);
        phase1 = (uu___240_9981.phase1);
        failhard = (uu___240_9981.failhard);
        nosynth = (uu___240_9981.nosynth);
        uvar_subtyping = (uu___240_9981.uvar_subtyping);
        tc_term = (uu___240_9981.tc_term);
        type_of = (uu___240_9981.type_of);
        universe_of = (uu___240_9981.universe_of);
        check_type_of = (uu___240_9981.check_type_of);
        use_bv_sorts = (uu___240_9981.use_bv_sorts);
        qtbl_name_and_index = (uu___240_9981.qtbl_name_and_index);
        normalized_eff_names = (uu___240_9981.normalized_eff_names);
        fv_delta_depths = (uu___240_9981.fv_delta_depths);
        proof_ns = (uu___240_9981.proof_ns);
        synth_hook = (uu___240_9981.synth_hook);
        splice = (uu___240_9981.splice);
        is_native_tactic = (uu___240_9981.is_native_tactic);
        identifier_info = (uu___240_9981.identifier_info);
        tc_hooks = (uu___240_9981.tc_hooks);
        dsenv = (uu___240_9981.dsenv);
        nbe = (uu___240_9981.nbe)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____9989 -> fun uu____9990 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env -> env.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env ->
    fun hooks ->
      let uu___241_10010 = env in
      {
        solver = (uu___241_10010.solver);
        range = (uu___241_10010.range);
        curmodule = (uu___241_10010.curmodule);
        gamma = (uu___241_10010.gamma);
        gamma_sig = (uu___241_10010.gamma_sig);
        gamma_cache = (uu___241_10010.gamma_cache);
        modules = (uu___241_10010.modules);
        expected_typ = (uu___241_10010.expected_typ);
        sigtab = (uu___241_10010.sigtab);
        attrtab = (uu___241_10010.attrtab);
        is_pattern = (uu___241_10010.is_pattern);
        instantiate_imp = (uu___241_10010.instantiate_imp);
        effects = (uu___241_10010.effects);
        generalize = (uu___241_10010.generalize);
        letrecs = (uu___241_10010.letrecs);
        top_level = (uu___241_10010.top_level);
        check_uvars = (uu___241_10010.check_uvars);
        use_eq = (uu___241_10010.use_eq);
        is_iface = (uu___241_10010.is_iface);
        admit = (uu___241_10010.admit);
        lax = (uu___241_10010.lax);
        lax_universes = (uu___241_10010.lax_universes);
        phase1 = (uu___241_10010.phase1);
        failhard = (uu___241_10010.failhard);
        nosynth = (uu___241_10010.nosynth);
        uvar_subtyping = (uu___241_10010.uvar_subtyping);
        tc_term = (uu___241_10010.tc_term);
        type_of = (uu___241_10010.type_of);
        universe_of = (uu___241_10010.universe_of);
        check_type_of = (uu___241_10010.check_type_of);
        use_bv_sorts = (uu___241_10010.use_bv_sorts);
        qtbl_name_and_index = (uu___241_10010.qtbl_name_and_index);
        normalized_eff_names = (uu___241_10010.normalized_eff_names);
        fv_delta_depths = (uu___241_10010.fv_delta_depths);
        proof_ns = (uu___241_10010.proof_ns);
        synth_hook = (uu___241_10010.synth_hook);
        splice = (uu___241_10010.splice);
        is_native_tactic = (uu___241_10010.is_native_tactic);
        identifier_info = (uu___241_10010.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___241_10010.dsenv);
        nbe = (uu___241_10010.nbe)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___242_10021 = e in
      let uu____10022 = FStar_Syntax_DsEnv.set_dep_graph e.dsenv g in
      {
        solver = (uu___242_10021.solver);
        range = (uu___242_10021.range);
        curmodule = (uu___242_10021.curmodule);
        gamma = (uu___242_10021.gamma);
        gamma_sig = (uu___242_10021.gamma_sig);
        gamma_cache = (uu___242_10021.gamma_cache);
        modules = (uu___242_10021.modules);
        expected_typ = (uu___242_10021.expected_typ);
        sigtab = (uu___242_10021.sigtab);
        attrtab = (uu___242_10021.attrtab);
        is_pattern = (uu___242_10021.is_pattern);
        instantiate_imp = (uu___242_10021.instantiate_imp);
        effects = (uu___242_10021.effects);
        generalize = (uu___242_10021.generalize);
        letrecs = (uu___242_10021.letrecs);
        top_level = (uu___242_10021.top_level);
        check_uvars = (uu___242_10021.check_uvars);
        use_eq = (uu___242_10021.use_eq);
        is_iface = (uu___242_10021.is_iface);
        admit = (uu___242_10021.admit);
        lax = (uu___242_10021.lax);
        lax_universes = (uu___242_10021.lax_universes);
        phase1 = (uu___242_10021.phase1);
        failhard = (uu___242_10021.failhard);
        nosynth = (uu___242_10021.nosynth);
        uvar_subtyping = (uu___242_10021.uvar_subtyping);
        tc_term = (uu___242_10021.tc_term);
        type_of = (uu___242_10021.type_of);
        universe_of = (uu___242_10021.universe_of);
        check_type_of = (uu___242_10021.check_type_of);
        use_bv_sorts = (uu___242_10021.use_bv_sorts);
        qtbl_name_and_index = (uu___242_10021.qtbl_name_and_index);
        normalized_eff_names = (uu___242_10021.normalized_eff_names);
        fv_delta_depths = (uu___242_10021.fv_delta_depths);
        proof_ns = (uu___242_10021.proof_ns);
        synth_hook = (uu___242_10021.synth_hook);
        splice = (uu___242_10021.splice);
        is_native_tactic = (uu___242_10021.is_native_tactic);
        identifier_info = (uu___242_10021.identifier_info);
        tc_hooks = (uu___242_10021.tc_hooks);
        dsenv = uu____10022;
        nbe = (uu___242_10021.nbe)
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
      | (NoDelta, uu____10045) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____10046,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____10047, FStar_Syntax_Syntax.Visible_default) -> true
      | (InliningDelta, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu____10048 -> false
let (default_table_size : Prims.int) = (Prims.parse_int "200")
let new_sigtab : 'Auu____10057 . unit -> 'Auu____10057 FStar_Util.smap =
  fun uu____10064 -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'Auu____10069 . unit -> 'Auu____10069 FStar_Util.smap =
  fun uu____10076 -> FStar_Util.smap_create (Prims.parse_int "100")
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
                  let uu____10210 = new_gamma_cache () in
                  let uu____10213 = new_sigtab () in
                  let uu____10216 = new_sigtab () in
                  let uu____10223 =
                    let uu____10236 =
                      FStar_Util.smap_create (Prims.parse_int "10") in
                    (uu____10236, FStar_Pervasives_Native.None) in
                  let uu____10251 =
                    FStar_Util.smap_create (Prims.parse_int "20") in
                  let uu____10254 =
                    FStar_Util.smap_create (Prims.parse_int "50") in
                  let uu____10257 = FStar_Options.using_facts_from () in
                  let uu____10258 =
                    FStar_Util.mk_ref
                      FStar_TypeChecker_Common.id_info_table_empty in
                  let uu____10261 = FStar_Syntax_DsEnv.empty_env deps in
                  {
                    solver;
                    range = FStar_Range.dummyRange;
                    curmodule = module_lid;
                    gamma = [];
                    gamma_sig = [];
                    gamma_cache = uu____10210;
                    modules = [];
                    expected_typ = FStar_Pervasives_Native.None;
                    sigtab = uu____10213;
                    attrtab = uu____10216;
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
                    qtbl_name_and_index = uu____10223;
                    normalized_eff_names = uu____10251;
                    fv_delta_depths = uu____10254;
                    proof_ns = uu____10257;
                    synth_hook =
                      (fun e ->
                         fun g ->
                           fun tau -> failwith "no synthesizer available");
                    splice =
                      (fun e -> fun tau -> failwith "no splicer available");
                    is_native_tactic = (fun uu____10297 -> false);
                    identifier_info = uu____10258;
                    tc_hooks = default_tc_hooks;
                    dsenv = uu____10261;
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
  fun uu____10397 ->
    let uu____10398 = FStar_ST.op_Bang query_indices in
    match uu____10398 with
    | [] -> failwith "Empty query indices!"
    | uu____10448 ->
        let uu____10457 =
          let uu____10466 =
            let uu____10473 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____10473 in
          let uu____10523 = FStar_ST.op_Bang query_indices in uu____10466 ::
            uu____10523 in
        FStar_ST.op_Colon_Equals query_indices uu____10457
let (pop_query_indices : unit -> unit) =
  fun uu____10612 ->
    let uu____10613 = FStar_ST.op_Bang query_indices in
    match uu____10613 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let (snapshot_query_indices :
  unit -> (Prims.int, unit) FStar_Pervasives_Native.tuple2) =
  fun uu____10728 ->
    FStar_Common.snapshot push_query_indices query_indices ()
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth -> FStar_Common.rollback pop_query_indices query_indices depth
let (add_query_index :
  (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____10758 ->
    match uu____10758 with
    | (l, n1) ->
        let uu____10765 = FStar_ST.op_Bang query_indices in
        (match uu____10765 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____10876 -> failwith "Empty query indices")
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____10895 ->
    let uu____10896 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____10896
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env ->
    (let uu____10969 =
       let uu____10972 = FStar_ST.op_Bang stack in env :: uu____10972 in
     FStar_ST.op_Colon_Equals stack uu____10969);
    (let uu___243_11021 = env in
     let uu____11022 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____11025 = FStar_Util.smap_copy (sigtab env) in
     let uu____11028 = FStar_Util.smap_copy (attrtab env) in
     let uu____11035 =
       let uu____11048 =
         let uu____11051 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu____11051 in
       let uu____11076 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu____11048, uu____11076) in
     let uu____11117 = FStar_Util.smap_copy env.normalized_eff_names in
     let uu____11120 = FStar_Util.smap_copy env.fv_delta_depths in
     let uu____11123 =
       let uu____11126 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____11126 in
     {
       solver = (uu___243_11021.solver);
       range = (uu___243_11021.range);
       curmodule = (uu___243_11021.curmodule);
       gamma = (uu___243_11021.gamma);
       gamma_sig = (uu___243_11021.gamma_sig);
       gamma_cache = uu____11022;
       modules = (uu___243_11021.modules);
       expected_typ = (uu___243_11021.expected_typ);
       sigtab = uu____11025;
       attrtab = uu____11028;
       is_pattern = (uu___243_11021.is_pattern);
       instantiate_imp = (uu___243_11021.instantiate_imp);
       effects = (uu___243_11021.effects);
       generalize = (uu___243_11021.generalize);
       letrecs = (uu___243_11021.letrecs);
       top_level = (uu___243_11021.top_level);
       check_uvars = (uu___243_11021.check_uvars);
       use_eq = (uu___243_11021.use_eq);
       is_iface = (uu___243_11021.is_iface);
       admit = (uu___243_11021.admit);
       lax = (uu___243_11021.lax);
       lax_universes = (uu___243_11021.lax_universes);
       phase1 = (uu___243_11021.phase1);
       failhard = (uu___243_11021.failhard);
       nosynth = (uu___243_11021.nosynth);
       uvar_subtyping = (uu___243_11021.uvar_subtyping);
       tc_term = (uu___243_11021.tc_term);
       type_of = (uu___243_11021.type_of);
       universe_of = (uu___243_11021.universe_of);
       check_type_of = (uu___243_11021.check_type_of);
       use_bv_sorts = (uu___243_11021.use_bv_sorts);
       qtbl_name_and_index = uu____11035;
       normalized_eff_names = uu____11117;
       fv_delta_depths = uu____11120;
       proof_ns = (uu___243_11021.proof_ns);
       synth_hook = (uu___243_11021.synth_hook);
       splice = (uu___243_11021.splice);
       is_native_tactic = (uu___243_11021.is_native_tactic);
       identifier_info = uu____11123;
       tc_hooks = (uu___243_11021.tc_hooks);
       dsenv = (uu___243_11021.dsenv);
       nbe = (uu___243_11021.nbe)
     })
let (pop_stack : unit -> env) =
  fun uu____11172 ->
    let uu____11173 = FStar_ST.op_Bang stack in
    match uu____11173 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____11227 -> failwith "Impossible: Too many pops"
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
        (fun uu____11299 ->
           let uu____11300 = snapshot_stack env in
           match uu____11300 with
           | (stack_depth, env1) ->
               let uu____11325 = snapshot_query_indices () in
               (match uu____11325 with
                | (query_indices_depth, ()) ->
                    let uu____11349 = (env1.solver).snapshot msg in
                    (match uu____11349 with
                     | (solver_depth, ()) ->
                         let uu____11391 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv in
                         (match uu____11391 with
                          | (dsenv_depth, dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___244_11437 = env1 in
                                 {
                                   solver = (uu___244_11437.solver);
                                   range = (uu___244_11437.range);
                                   curmodule = (uu___244_11437.curmodule);
                                   gamma = (uu___244_11437.gamma);
                                   gamma_sig = (uu___244_11437.gamma_sig);
                                   gamma_cache = (uu___244_11437.gamma_cache);
                                   modules = (uu___244_11437.modules);
                                   expected_typ =
                                     (uu___244_11437.expected_typ);
                                   sigtab = (uu___244_11437.sigtab);
                                   attrtab = (uu___244_11437.attrtab);
                                   is_pattern = (uu___244_11437.is_pattern);
                                   instantiate_imp =
                                     (uu___244_11437.instantiate_imp);
                                   effects = (uu___244_11437.effects);
                                   generalize = (uu___244_11437.generalize);
                                   letrecs = (uu___244_11437.letrecs);
                                   top_level = (uu___244_11437.top_level);
                                   check_uvars = (uu___244_11437.check_uvars);
                                   use_eq = (uu___244_11437.use_eq);
                                   is_iface = (uu___244_11437.is_iface);
                                   admit = (uu___244_11437.admit);
                                   lax = (uu___244_11437.lax);
                                   lax_universes =
                                     (uu___244_11437.lax_universes);
                                   phase1 = (uu___244_11437.phase1);
                                   failhard = (uu___244_11437.failhard);
                                   nosynth = (uu___244_11437.nosynth);
                                   uvar_subtyping =
                                     (uu___244_11437.uvar_subtyping);
                                   tc_term = (uu___244_11437.tc_term);
                                   type_of = (uu___244_11437.type_of);
                                   universe_of = (uu___244_11437.universe_of);
                                   check_type_of =
                                     (uu___244_11437.check_type_of);
                                   use_bv_sorts =
                                     (uu___244_11437.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___244_11437.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___244_11437.normalized_eff_names);
                                   fv_delta_depths =
                                     (uu___244_11437.fv_delta_depths);
                                   proof_ns = (uu___244_11437.proof_ns);
                                   synth_hook = (uu___244_11437.synth_hook);
                                   splice = (uu___244_11437.splice);
                                   is_native_tactic =
                                     (uu___244_11437.is_native_tactic);
                                   identifier_info =
                                     (uu___244_11437.identifier_info);
                                   tc_hooks = (uu___244_11437.tc_hooks);
                                   dsenv = dsenv1;
                                   nbe = (uu___244_11437.nbe)
                                 }))))))
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Util.atomically
          (fun uu____11468 ->
             let uu____11469 =
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
             match uu____11469 with
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
                             ((let uu____11595 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1 in
                               FStar_Common.runtime_assert uu____11595
                                 "Inconsistent stack state");
                              tcenv))))))
let (push : env -> Prims.string -> env) =
  fun env ->
    fun msg ->
      let uu____11606 = snapshot env msg in
      FStar_Pervasives_Native.snd uu____11606
let (pop : env -> Prims.string -> env) =
  fun env -> fun msg -> rollback env.solver msg FStar_Pervasives_Native.None
let (incr_query_index : env -> env) =
  fun env ->
    let qix = peek_query_indices () in
    match env.qtbl_name_and_index with
    | (uu____11633, FStar_Pervasives_Native.None) -> env
    | (tbl, FStar_Pervasives_Native.Some (l, n1)) ->
        let uu____11665 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____11691 ->
                  match uu____11691 with
                  | (m, uu____11697) -> FStar_Ident.lid_equals l m)) in
        (match uu____11665 with
         | FStar_Pervasives_Native.None ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___245_11705 = env in
               {
                 solver = (uu___245_11705.solver);
                 range = (uu___245_11705.range);
                 curmodule = (uu___245_11705.curmodule);
                 gamma = (uu___245_11705.gamma);
                 gamma_sig = (uu___245_11705.gamma_sig);
                 gamma_cache = (uu___245_11705.gamma_cache);
                 modules = (uu___245_11705.modules);
                 expected_typ = (uu___245_11705.expected_typ);
                 sigtab = (uu___245_11705.sigtab);
                 attrtab = (uu___245_11705.attrtab);
                 is_pattern = (uu___245_11705.is_pattern);
                 instantiate_imp = (uu___245_11705.instantiate_imp);
                 effects = (uu___245_11705.effects);
                 generalize = (uu___245_11705.generalize);
                 letrecs = (uu___245_11705.letrecs);
                 top_level = (uu___245_11705.top_level);
                 check_uvars = (uu___245_11705.check_uvars);
                 use_eq = (uu___245_11705.use_eq);
                 is_iface = (uu___245_11705.is_iface);
                 admit = (uu___245_11705.admit);
                 lax = (uu___245_11705.lax);
                 lax_universes = (uu___245_11705.lax_universes);
                 phase1 = (uu___245_11705.phase1);
                 failhard = (uu___245_11705.failhard);
                 nosynth = (uu___245_11705.nosynth);
                 uvar_subtyping = (uu___245_11705.uvar_subtyping);
                 tc_term = (uu___245_11705.tc_term);
                 type_of = (uu___245_11705.type_of);
                 universe_of = (uu___245_11705.universe_of);
                 check_type_of = (uu___245_11705.check_type_of);
                 use_bv_sorts = (uu___245_11705.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___245_11705.normalized_eff_names);
                 fv_delta_depths = (uu___245_11705.fv_delta_depths);
                 proof_ns = (uu___245_11705.proof_ns);
                 synth_hook = (uu___245_11705.synth_hook);
                 splice = (uu___245_11705.splice);
                 is_native_tactic = (uu___245_11705.is_native_tactic);
                 identifier_info = (uu___245_11705.identifier_info);
                 tc_hooks = (uu___245_11705.tc_hooks);
                 dsenv = (uu___245_11705.dsenv);
                 nbe = (uu___245_11705.nbe)
               }))
         | FStar_Pervasives_Native.Some (uu____11718, m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___246_11727 = env in
               {
                 solver = (uu___246_11727.solver);
                 range = (uu___246_11727.range);
                 curmodule = (uu___246_11727.curmodule);
                 gamma = (uu___246_11727.gamma);
                 gamma_sig = (uu___246_11727.gamma_sig);
                 gamma_cache = (uu___246_11727.gamma_cache);
                 modules = (uu___246_11727.modules);
                 expected_typ = (uu___246_11727.expected_typ);
                 sigtab = (uu___246_11727.sigtab);
                 attrtab = (uu___246_11727.attrtab);
                 is_pattern = (uu___246_11727.is_pattern);
                 instantiate_imp = (uu___246_11727.instantiate_imp);
                 effects = (uu___246_11727.effects);
                 generalize = (uu___246_11727.generalize);
                 letrecs = (uu___246_11727.letrecs);
                 top_level = (uu___246_11727.top_level);
                 check_uvars = (uu___246_11727.check_uvars);
                 use_eq = (uu___246_11727.use_eq);
                 is_iface = (uu___246_11727.is_iface);
                 admit = (uu___246_11727.admit);
                 lax = (uu___246_11727.lax);
                 lax_universes = (uu___246_11727.lax_universes);
                 phase1 = (uu___246_11727.phase1);
                 failhard = (uu___246_11727.failhard);
                 nosynth = (uu___246_11727.nosynth);
                 uvar_subtyping = (uu___246_11727.uvar_subtyping);
                 tc_term = (uu___246_11727.tc_term);
                 type_of = (uu___246_11727.type_of);
                 universe_of = (uu___246_11727.universe_of);
                 check_type_of = (uu___246_11727.check_type_of);
                 use_bv_sorts = (uu___246_11727.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___246_11727.normalized_eff_names);
                 fv_delta_depths = (uu___246_11727.fv_delta_depths);
                 proof_ns = (uu___246_11727.proof_ns);
                 synth_hook = (uu___246_11727.synth_hook);
                 splice = (uu___246_11727.splice);
                 is_native_tactic = (uu___246_11727.is_native_tactic);
                 identifier_info = (uu___246_11727.identifier_info);
                 tc_hooks = (uu___246_11727.tc_hooks);
                 dsenv = (uu___246_11727.dsenv);
                 nbe = (uu___246_11727.nbe)
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
        (let uu___247_11761 = e in
         {
           solver = (uu___247_11761.solver);
           range = r;
           curmodule = (uu___247_11761.curmodule);
           gamma = (uu___247_11761.gamma);
           gamma_sig = (uu___247_11761.gamma_sig);
           gamma_cache = (uu___247_11761.gamma_cache);
           modules = (uu___247_11761.modules);
           expected_typ = (uu___247_11761.expected_typ);
           sigtab = (uu___247_11761.sigtab);
           attrtab = (uu___247_11761.attrtab);
           is_pattern = (uu___247_11761.is_pattern);
           instantiate_imp = (uu___247_11761.instantiate_imp);
           effects = (uu___247_11761.effects);
           generalize = (uu___247_11761.generalize);
           letrecs = (uu___247_11761.letrecs);
           top_level = (uu___247_11761.top_level);
           check_uvars = (uu___247_11761.check_uvars);
           use_eq = (uu___247_11761.use_eq);
           is_iface = (uu___247_11761.is_iface);
           admit = (uu___247_11761.admit);
           lax = (uu___247_11761.lax);
           lax_universes = (uu___247_11761.lax_universes);
           phase1 = (uu___247_11761.phase1);
           failhard = (uu___247_11761.failhard);
           nosynth = (uu___247_11761.nosynth);
           uvar_subtyping = (uu___247_11761.uvar_subtyping);
           tc_term = (uu___247_11761.tc_term);
           type_of = (uu___247_11761.type_of);
           universe_of = (uu___247_11761.universe_of);
           check_type_of = (uu___247_11761.check_type_of);
           use_bv_sorts = (uu___247_11761.use_bv_sorts);
           qtbl_name_and_index = (uu___247_11761.qtbl_name_and_index);
           normalized_eff_names = (uu___247_11761.normalized_eff_names);
           fv_delta_depths = (uu___247_11761.fv_delta_depths);
           proof_ns = (uu___247_11761.proof_ns);
           synth_hook = (uu___247_11761.synth_hook);
           splice = (uu___247_11761.splice);
           is_native_tactic = (uu___247_11761.is_native_tactic);
           identifier_info = (uu___247_11761.identifier_info);
           tc_hooks = (uu___247_11761.tc_hooks);
           dsenv = (uu___247_11761.dsenv);
           nbe = (uu___247_11761.nbe)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env ->
    fun enabled ->
      let uu____11777 =
        let uu____11778 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____11778 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11777
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env ->
    fun bv ->
      fun ty ->
        let uu____11832 =
          let uu____11833 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____11833 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11832
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env ->
    fun fv ->
      fun ty ->
        let uu____11887 =
          let uu____11888 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____11888 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____11887
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env ->
    fun ty_map ->
      let uu____11942 =
        let uu____11943 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____11943 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____11942
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env -> env.modules
let (current_module : env -> FStar_Ident.lident) = fun env -> env.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun lid ->
      let uu___248_12004 = env in
      {
        solver = (uu___248_12004.solver);
        range = (uu___248_12004.range);
        curmodule = lid;
        gamma = (uu___248_12004.gamma);
        gamma_sig = (uu___248_12004.gamma_sig);
        gamma_cache = (uu___248_12004.gamma_cache);
        modules = (uu___248_12004.modules);
        expected_typ = (uu___248_12004.expected_typ);
        sigtab = (uu___248_12004.sigtab);
        attrtab = (uu___248_12004.attrtab);
        is_pattern = (uu___248_12004.is_pattern);
        instantiate_imp = (uu___248_12004.instantiate_imp);
        effects = (uu___248_12004.effects);
        generalize = (uu___248_12004.generalize);
        letrecs = (uu___248_12004.letrecs);
        top_level = (uu___248_12004.top_level);
        check_uvars = (uu___248_12004.check_uvars);
        use_eq = (uu___248_12004.use_eq);
        is_iface = (uu___248_12004.is_iface);
        admit = (uu___248_12004.admit);
        lax = (uu___248_12004.lax);
        lax_universes = (uu___248_12004.lax_universes);
        phase1 = (uu___248_12004.phase1);
        failhard = (uu___248_12004.failhard);
        nosynth = (uu___248_12004.nosynth);
        uvar_subtyping = (uu___248_12004.uvar_subtyping);
        tc_term = (uu___248_12004.tc_term);
        type_of = (uu___248_12004.type_of);
        universe_of = (uu___248_12004.universe_of);
        check_type_of = (uu___248_12004.check_type_of);
        use_bv_sorts = (uu___248_12004.use_bv_sorts);
        qtbl_name_and_index = (uu___248_12004.qtbl_name_and_index);
        normalized_eff_names = (uu___248_12004.normalized_eff_names);
        fv_delta_depths = (uu___248_12004.fv_delta_depths);
        proof_ns = (uu___248_12004.proof_ns);
        synth_hook = (uu___248_12004.synth_hook);
        splice = (uu___248_12004.splice);
        is_native_tactic = (uu___248_12004.is_native_tactic);
        identifier_info = (uu___248_12004.identifier_info);
        tc_hooks = (uu___248_12004.tc_hooks);
        dsenv = (uu___248_12004.dsenv);
        nbe = (uu___248_12004.nbe)
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
      let uu____12031 = FStar_Ident.text_of_lid lid in
      FStar_Util.smap_try_find (sigtab env) uu____12031
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    let uu____12041 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str in
    (FStar_Errors.Fatal_NameNotFound, uu____12041)
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1 ->
    let uu____12051 =
      let uu____12052 = FStar_Syntax_Print.bv_to_string v1 in
      FStar_Util.format1 "Variable \"%s\" not found" uu____12052 in
    (FStar_Errors.Fatal_VariableNotFound, uu____12051)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____12057 ->
    let uu____12058 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____12058
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
      | ((formals, t), uu____12152) ->
          let vs = mk_univ_subst formals us in
          let uu____12176 = FStar_Syntax_Subst.subst vs t in
          (us, uu____12176)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___226_12192 ->
    match uu___226_12192 with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____12218 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r ->
    fun t ->
      let uu____12237 = inst_tscheme t in
      match uu____12237 with
      | (us, t1) ->
          let uu____12248 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____12248)
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts ->
    fun env ->
      fun ed ->
        fun uu____12268 ->
          match uu____12268 with
          | (us, t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____12289 =
                         let uu____12290 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____12291 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____12292 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____12293 =
                           FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____12290 uu____12291 uu____12292 uu____12293 in
                       failwith uu____12289)
                    else ();
                    (let uu____12295 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____12295))
               | uu____12304 ->
                   let uu____12305 =
                     let uu____12306 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____12306 in
                   failwith uu____12305)
type tri =
  | Yes 
  | No 
  | Maybe 
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu____12312 -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____12318 -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee ->
    match projectee with | Maybe -> true | uu____12324 -> false
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
             | ([], uu____12366) -> Maybe
             | (uu____12373, []) -> No
             | (hd1::tl1, hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____12392 -> No in
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
          let uu____12483 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____12483 with
          | FStar_Pervasives_Native.None ->
              let uu____12506 =
                FStar_Util.find_map env.gamma
                  (fun uu___227_12550 ->
                     match uu___227_12550 with
                     | FStar_Syntax_Syntax.Binding_lid (l, t) ->
                         let uu____12589 = FStar_Ident.lid_equals lid l in
                         if uu____12589
                         then
                           let uu____12610 =
                             let uu____12629 =
                               let uu____12644 = inst_tscheme t in
                               FStar_Util.Inl uu____12644 in
                             let uu____12659 = FStar_Ident.range_of_lid l in
                             (uu____12629, uu____12659) in
                           FStar_Pervasives_Native.Some uu____12610
                         else FStar_Pervasives_Native.None
                     | uu____12711 -> FStar_Pervasives_Native.None) in
              FStar_Util.catch_opt uu____12506
                (fun uu____12749 ->
                   FStar_Util.find_map env.gamma_sig
                     (fun uu___228_12758 ->
                        match uu___228_12758 with
                        | (uu____12761,
                           {
                             FStar_Syntax_Syntax.sigel =
                               FStar_Syntax_Syntax.Sig_bundle
                               (ses, uu____12763);
                             FStar_Syntax_Syntax.sigrng = uu____12764;
                             FStar_Syntax_Syntax.sigquals = uu____12765;
                             FStar_Syntax_Syntax.sigmeta = uu____12766;
                             FStar_Syntax_Syntax.sigattrs = uu____12767;_})
                            ->
                            FStar_Util.find_map ses
                              (fun se ->
                                 let uu____12787 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.lids_of_sigelt se)
                                     (FStar_Util.for_some
                                        (FStar_Ident.lid_equals lid)) in
                                 if uu____12787
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
                                  uu____12835 ->
                                  FStar_Pervasives_Native.Some t
                              | uu____12842 -> cache t in
                            let uu____12843 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids in
                            (match uu____12843 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some l ->
                                 let uu____12849 =
                                   let uu____12850 =
                                     FStar_Ident.range_of_lid l in
                                   ((FStar_Util.Inr
                                       (s, FStar_Pervasives_Native.None)),
                                     uu____12850) in
                                 maybe_cache uu____12849)))
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____12918 = find_in_sigtab env lid in
         match uu____12918 with
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
      let uu____12998 = lookup_qname env lid in
      match uu____12998 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inl uu____13019, rng) ->
          FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) ->
          FStar_Pervasives_Native.Some se
let (lookup_attr :
  env -> Prims.string -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun env ->
    fun attr ->
      let uu____13130 = FStar_Util.smap_try_find (attrtab env) attr in
      match uu____13130 with
      | FStar_Pervasives_Native.Some ses -> ses
      | FStar_Pervasives_Native.None -> []
let (add_se_to_attrtab : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let add_one1 env1 se1 attr =
        let uu____13172 =
          let uu____13175 = lookup_attr env1 attr in se1 :: uu____13175 in
        FStar_Util.smap_add (attrtab env1) attr uu____13172 in
      FStar_List.iter
        (fun attr ->
           let uu____13185 =
             let uu____13186 = FStar_Syntax_Subst.compress attr in
             uu____13186.FStar_Syntax_Syntax.n in
           match uu____13185 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____13190 =
                 let uu____13191 = FStar_Syntax_Syntax.lid_of_fv fv in
                 uu____13191.FStar_Ident.str in
               add_one1 env se uu____13190
           | uu____13192 -> ()) se.FStar_Syntax_Syntax.sigattrs
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____13214) ->
          add_sigelts env ses
      | uu____13223 ->
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
            | uu____13238 -> ()))
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
        (fun uu___229_13269 ->
           match uu___229_13269 with
           | FStar_Syntax_Syntax.Binding_var id1 when
               FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____13287 -> FStar_Pervasives_Native.None)
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
        | FStar_Syntax_Syntax.Sig_let ((uu____13348, lb::[]), uu____13350) ->
            let uu____13357 =
              let uu____13366 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____13375 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____13366, uu____13375) in
            FStar_Pervasives_Native.Some uu____13357
        | FStar_Syntax_Syntax.Sig_let ((uu____13388, lbs), uu____13390) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____13420 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____13432 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____13432
                     then
                       let uu____13443 =
                         let uu____13452 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____13461 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____13452, uu____13461) in
                       FStar_Pervasives_Native.Some uu____13443
                     else FStar_Pervasives_Native.None)
        | uu____13483 -> FStar_Pervasives_Native.None
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
          let uu____13542 =
            let uu____13551 =
              let uu____13556 =
                let uu____13557 =
                  let uu____13560 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____13560 in
                ((ne.FStar_Syntax_Syntax.univs), uu____13557) in
              inst_tscheme1 uu____13556 in
            (uu____13551, (se.FStar_Syntax_Syntax.sigrng)) in
          FStar_Pervasives_Native.Some uu____13542
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, us, binders, uu____13582, uu____13583) ->
          let uu____13588 =
            let uu____13597 =
              let uu____13602 =
                let uu____13603 =
                  let uu____13606 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                  FStar_Syntax_Util.arrow binders uu____13606 in
                (us, uu____13603) in
              inst_tscheme1 uu____13602 in
            (uu____13597, (se.FStar_Syntax_Syntax.sigrng)) in
          FStar_Pervasives_Native.Some uu____13588
      | uu____13625 -> FStar_Pervasives_Native.None
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
        let mapper uu____13713 =
          match uu____13713 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____13809, uvs, t, uu____13812, uu____13813,
                         uu____13814);
                      FStar_Syntax_Syntax.sigrng = uu____13815;
                      FStar_Syntax_Syntax.sigquals = uu____13816;
                      FStar_Syntax_Syntax.sigmeta = uu____13817;
                      FStar_Syntax_Syntax.sigattrs = uu____13818;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____13839 =
                     let uu____13848 = inst_tscheme1 (uvs, t) in
                     (uu____13848, rng) in
                   FStar_Pervasives_Native.Some uu____13839
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____13872;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____13874;
                      FStar_Syntax_Syntax.sigattrs = uu____13875;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____13892 =
                     let uu____13893 = in_cur_mod env l in uu____13893 = Yes in
                   if uu____13892
                   then
                     let uu____13904 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface in
                     (if uu____13904
                      then
                        let uu____13917 =
                          let uu____13926 = inst_tscheme1 (uvs, t) in
                          (uu____13926, rng) in
                        FStar_Pervasives_Native.Some uu____13917
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____13957 =
                        let uu____13966 = inst_tscheme1 (uvs, t) in
                        (uu____13966, rng) in
                      FStar_Pervasives_Native.Some uu____13957)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____13991, uu____13992);
                      FStar_Syntax_Syntax.sigrng = uu____13993;
                      FStar_Syntax_Syntax.sigquals = uu____13994;
                      FStar_Syntax_Syntax.sigmeta = uu____13995;
                      FStar_Syntax_Syntax.sigattrs = uu____13996;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14037 =
                          let uu____14046 = inst_tscheme1 (uvs, k) in
                          (uu____14046, rng) in
                        FStar_Pervasives_Native.Some uu____14037
                    | uu____14067 ->
                        let uu____14068 =
                          let uu____14077 =
                            let uu____14082 =
                              let uu____14083 =
                                let uu____14086 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____14086 in
                              (uvs, uu____14083) in
                            inst_tscheme1 uu____14082 in
                          (uu____14077, rng) in
                        FStar_Pervasives_Native.Some uu____14068)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____14109, uu____14110);
                      FStar_Syntax_Syntax.sigrng = uu____14111;
                      FStar_Syntax_Syntax.sigquals = uu____14112;
                      FStar_Syntax_Syntax.sigmeta = uu____14113;
                      FStar_Syntax_Syntax.sigattrs = uu____14114;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____14156 =
                          let uu____14165 = inst_tscheme_with (uvs, k) us in
                          (uu____14165, rng) in
                        FStar_Pervasives_Native.Some uu____14156
                    | uu____14186 ->
                        let uu____14187 =
                          let uu____14196 =
                            let uu____14201 =
                              let uu____14202 =
                                let uu____14205 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____14205 in
                              (uvs, uu____14202) in
                            inst_tscheme_with uu____14201 us in
                          (uu____14196, rng) in
                        FStar_Pervasives_Native.Some uu____14187)
               | FStar_Util.Inr se ->
                   let uu____14241 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____14262;
                          FStar_Syntax_Syntax.sigrng = uu____14263;
                          FStar_Syntax_Syntax.sigquals = uu____14264;
                          FStar_Syntax_Syntax.sigmeta = uu____14265;
                          FStar_Syntax_Syntax.sigattrs = uu____14266;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____14281 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) in
                   FStar_All.pipe_right uu____14241
                     (FStar_Util.map_option
                        (fun uu____14329 ->
                           match uu____14329 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____14360 =
          let uu____14371 = lookup_qname env lid in
          FStar_Util.bind_opt uu____14371 mapper in
        match uu____14360 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____14445 =
              let uu____14456 =
                let uu____14463 =
                  let uu___249_14466 = t in
                  let uu____14467 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___249_14466.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____14467;
                    FStar_Syntax_Syntax.vars =
                      (uu___249_14466.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____14463) in
              (uu____14456, r) in
            FStar_Pervasives_Native.Some uu____14445
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____14514 = lookup_qname env l in
      match uu____14514 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____14533 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ, FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____14585 = try_lookup_bv env bv in
      match uu____14585 with
      | FStar_Pervasives_Native.None ->
          let uu____14600 = variable_not_found bv in
          FStar_Errors.raise_error uu____14600 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____14615 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____14616 =
            let uu____14617 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____14617 in
          (uu____14615, uu____14616)
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
      let uu____14638 = try_lookup_lid_aux FStar_Pervasives_Native.None env l in
      match uu____14638 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____14704 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____14704 in
          let uu____14705 =
            let uu____14714 =
              let uu____14719 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____14719) in
            (uu____14714, r1) in
          FStar_Pervasives_Native.Some uu____14705
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
        let uu____14753 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l in
        match uu____14753 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____14786, t), r) ->
            let use_range1 = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____14811 = FStar_Range.use_range use_range1 in
              FStar_Range.set_use_range r uu____14811 in
            let uu____14812 =
              let uu____14817 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (uu____14817, r1) in
            FStar_Pervasives_Native.Some uu____14812
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun l ->
      let uu____14840 = try_lookup_lid env l in
      match uu____14840 with
      | FStar_Pervasives_Native.None ->
          let uu____14867 = name_not_found l in
          let uu____14872 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____14867 uu____14872
      | FStar_Pervasives_Native.Some v1 -> v1
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___230_14912 ->
              match uu___230_14912 with
              | FStar_Syntax_Syntax.Binding_univ y ->
                  x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____14914 -> false) env.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme, FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____14933 = lookup_qname env lid in
      match uu____14933 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14942, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____14945;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____14947;
              FStar_Syntax_Syntax.sigattrs = uu____14948;_},
            FStar_Pervasives_Native.None),
           uu____14949)
          ->
          let uu____14998 =
            let uu____15005 =
              let uu____15006 =
                let uu____15009 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____15009 t in
              (uvs, uu____15006) in
            (uu____15005, q) in
          FStar_Pervasives_Native.Some uu____14998
      | uu____15022 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____15043 = lookup_qname env lid in
      match uu____15043 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____15048, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____15051;
              FStar_Syntax_Syntax.sigquals = uu____15052;
              FStar_Syntax_Syntax.sigmeta = uu____15053;
              FStar_Syntax_Syntax.sigattrs = uu____15054;_},
            FStar_Pervasives_Native.None),
           uu____15055)
          ->
          let uu____15104 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____15104 (uvs, t)
      | uu____15109 ->
          let uu____15110 = name_not_found lid in
          let uu____15115 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____15110 uu____15115
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____15134 = lookup_qname env lid in
      match uu____15134 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15139, uvs, t, uu____15142, uu____15143, uu____15144);
              FStar_Syntax_Syntax.sigrng = uu____15145;
              FStar_Syntax_Syntax.sigquals = uu____15146;
              FStar_Syntax_Syntax.sigmeta = uu____15147;
              FStar_Syntax_Syntax.sigattrs = uu____15148;_},
            FStar_Pervasives_Native.None),
           uu____15149)
          ->
          let uu____15202 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____15202 (uvs, t)
      | uu____15207 ->
          let uu____15208 = name_not_found lid in
          let uu____15213 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____15208 uu____15213
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool, FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____15234 = lookup_qname env lid in
      match uu____15234 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____15241, uu____15242, uu____15243, uu____15244,
                 uu____15245, dcs);
              FStar_Syntax_Syntax.sigrng = uu____15247;
              FStar_Syntax_Syntax.sigquals = uu____15248;
              FStar_Syntax_Syntax.sigmeta = uu____15249;
              FStar_Syntax_Syntax.sigattrs = uu____15250;_},
            uu____15251),
           uu____15252)
          -> (true, dcs)
      | uu____15313 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      let uu____15326 = lookup_qname env lid in
      match uu____15326 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____15327, uu____15328, uu____15329, l, uu____15331,
                 uu____15332);
              FStar_Syntax_Syntax.sigrng = uu____15333;
              FStar_Syntax_Syntax.sigquals = uu____15334;
              FStar_Syntax_Syntax.sigmeta = uu____15335;
              FStar_Syntax_Syntax.sigattrs = uu____15336;_},
            uu____15337),
           uu____15338)
          -> l
      | uu____15393 ->
          let uu____15394 =
            let uu____15395 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____15395 in
          failwith uu____15394
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
            (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____15444)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____15495, lbs), uu____15497)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____15519 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____15519
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____15551 -> FStar_Pervasives_Native.None)
        | uu____15556 -> FStar_Pervasives_Native.None
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
        let uu____15586 = lookup_qname env lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____15586
let (delta_depth_of_qninfo :
  FStar_Syntax_Syntax.fv ->
    qninfo -> FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun fv ->
    fun qn ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      if lid.FStar_Ident.nsstr = "Prims"
      then FStar_Pervasives_Native.Some (fv.FStar_Syntax_Syntax.fv_delta)
      else
        (match qn with
         | FStar_Pervasives_Native.None ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inl uu____15631, uu____15632) ->
             FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.parse_int "0"))
         | FStar_Pervasives_Native.Some
             (FStar_Util.Inr (se, uu____15680), uu____15681) ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_inductive_typ uu____15730 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_bundle uu____15747 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_datacon uu____15756 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "0"))
              | FStar_Syntax_Syntax.Sig_declare_typ uu____15771 ->
                  let uu____15778 =
                    FStar_Syntax_DsEnv.delta_depth_of_declaration lid
                      se.FStar_Syntax_Syntax.sigquals in
                  FStar_Pervasives_Native.Some uu____15778
              | FStar_Syntax_Syntax.Sig_let ((uu____15779, lbs), uu____15781)
                  ->
                  FStar_Util.find_map lbs
                    (fun lb ->
                       let fv1 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       let uu____15795 =
                         FStar_Syntax_Syntax.fv_eq_lid fv1 lid in
                       if uu____15795
                       then
                         FStar_Pervasives_Native.Some
                           (fv1.FStar_Syntax_Syntax.fv_delta)
                       else FStar_Pervasives_Native.None)
              | FStar_Syntax_Syntax.Sig_splice uu____15799 ->
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       (Prims.parse_int "1"))
              | FStar_Syntax_Syntax.Sig_main uu____15806 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_assume uu____15807 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect uu____15814 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____15815 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_sub_effect uu____15816 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_effect_abbrev uu____15817 ->
                  FStar_Pervasives_Native.None
              | FStar_Syntax_Syntax.Sig_pragma uu____15830 ->
                  FStar_Pervasives_Native.None))
let (delta_depth_of_fv :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth) =
  fun env ->
    fun fv ->
      let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      if lid.FStar_Ident.nsstr = "Prims"
      then fv.FStar_Syntax_Syntax.fv_delta
      else
        (let uu____15843 =
           FStar_All.pipe_right lid.FStar_Ident.str
             (FStar_Util.smap_try_find env.fv_delta_depths) in
         FStar_All.pipe_right uu____15843
           (fun d_opt ->
              let uu____15855 = FStar_All.pipe_right d_opt FStar_Util.is_some in
              if uu____15855
              then FStar_All.pipe_right d_opt FStar_Util.must
              else
                (let uu____15861 =
                   let uu____15864 =
                     lookup_qname env
                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   delta_depth_of_qninfo fv uu____15864 in
                 match uu____15861 with
                 | FStar_Pervasives_Native.None ->
                     let uu____15865 =
                       let uu____15866 = FStar_Syntax_Print.fv_to_string fv in
                       FStar_Util.format1 "Delta depth not found for %s"
                         uu____15866 in
                     failwith uu____15865
                 | FStar_Pervasives_Native.Some d ->
                     ((let uu____15869 =
                         (d <> fv.FStar_Syntax_Syntax.fv_delta) &&
                           (FStar_Options.debug_any ()) in
                       if uu____15869
                       then
                         let uu____15870 = FStar_Syntax_Print.fv_to_string fv in
                         let uu____15871 =
                           FStar_Syntax_Print.delta_depth_to_string
                             fv.FStar_Syntax_Syntax.fv_delta in
                         let uu____15872 =
                           FStar_Syntax_Print.delta_depth_to_string d in
                         FStar_Util.print3
                           "WARNING WARNING WARNING fv=%s, delta_depth=%s, env.delta_depth=%s\n"
                           uu____15870 uu____15871 uu____15872
                       else ());
                      FStar_Util.smap_add env.fv_delta_depths
                        lid.FStar_Ident.str d;
                      d))))
let (quals_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.qualifier Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____15893), uu____15894) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
    | uu____15943 -> FStar_Pervasives_Native.None
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____15964), uu____15965) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____16014 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____16035 = lookup_qname env lid in
      FStar_All.pipe_left attrs_of_qninfo uu____16035
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ftv ->
      let uu____16054 = lookup_qname env ftv in
      match uu____16054 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____16058) ->
          let uu____16103 = effect_signature FStar_Pervasives_Native.None se in
          (match uu____16103 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____16124, t), r) ->
               let uu____16139 =
                 let uu____16140 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____16140 t in
               FStar_Pervasives_Native.Some uu____16139)
      | uu____16141 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun ftv ->
      let uu____16152 = try_lookup_effect_lid env ftv in
      match uu____16152 with
      | FStar_Pervasives_Native.None ->
          let uu____16155 = name_not_found ftv in
          let uu____16160 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____16155 uu____16160
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
        let uu____16183 = lookup_qname env lid0 in
        match uu____16183 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs1, binders, c, uu____16194);
                FStar_Syntax_Syntax.sigrng = uu____16195;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____16197;
                FStar_Syntax_Syntax.sigattrs = uu____16198;_},
              FStar_Pervasives_Native.None),
             uu____16199)
            ->
            let lid1 =
              let uu____16253 =
                let uu____16254 = FStar_Ident.range_of_lid lid in
                let uu____16255 =
                  let uu____16256 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____16256 in
                FStar_Range.set_use_range uu____16254 uu____16255 in
              FStar_Ident.set_lid_range lid uu____16253 in
            let uu____16257 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___231_16261 ->
                      match uu___231_16261 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____16262 -> false)) in
            if uu____16257
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____16276 =
                      let uu____16277 =
                        let uu____16278 = get_range env in
                        FStar_Range.string_of_range uu____16278 in
                      let uu____16279 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____16280 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____16277 uu____16279 uu____16280 in
                    failwith uu____16276) in
               match (binders, univs1) with
               | ([], uu____16297) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____16322, uu____16323::uu____16324::uu____16325) ->
                   let uu____16346 =
                     let uu____16347 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____16348 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____16347 uu____16348 in
                   failwith uu____16346
               | uu____16355 ->
                   let uu____16370 =
                     let uu____16375 =
                       let uu____16376 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____16376) in
                     inst_tscheme_with uu____16375 insts in
                   (match uu____16370 with
                    | (uu____16389, t) ->
                        let t1 =
                          let uu____16392 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____16392 t in
                        let uu____16393 =
                          let uu____16394 = FStar_Syntax_Subst.compress t1 in
                          uu____16394.FStar_Syntax_Syntax.n in
                        (match uu____16393 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____16429 -> failwith "Impossible")))
        | uu____16436 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun l ->
      let rec find1 l1 =
        let uu____16459 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____16459 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____16472, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____16479 = find1 l2 in
            (match uu____16479 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____16486 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str in
        match uu____16486 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____16490 = find1 l in
            (match uu____16490 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m)) in
      let uu____16495 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____16495
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env ->
    fun l ->
      let l1 = norm_eff_name env l in
      let uu____16509 = lookup_qname env l1 in
      match uu____16509 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____16512;
              FStar_Syntax_Syntax.sigrng = uu____16513;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____16515;
              FStar_Syntax_Syntax.sigattrs = uu____16516;_},
            uu____16517),
           uu____16518)
          -> q
      | uu____16569 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      fun i ->
        let fail1 uu____16590 =
          let uu____16591 =
            let uu____16592 = FStar_Util.string_of_int i in
            let uu____16593 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____16592 uu____16593 in
          failwith uu____16591 in
        let uu____16594 = lookup_datacon env lid in
        match uu____16594 with
        | (uu____16599, t) ->
            let uu____16601 =
              let uu____16602 = FStar_Syntax_Subst.compress t in
              uu____16602.FStar_Syntax_Syntax.n in
            (match uu____16601 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____16606) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____16647 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____16647
                      FStar_Pervasives_Native.fst)
             | uu____16658 -> fail1 ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____16669 = lookup_qname env l in
      match uu____16669 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____16670, uu____16671, uu____16672);
              FStar_Syntax_Syntax.sigrng = uu____16673;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16675;
              FStar_Syntax_Syntax.sigattrs = uu____16676;_},
            uu____16677),
           uu____16678)
          ->
          FStar_Util.for_some
            (fun uu___232_16731 ->
               match uu___232_16731 with
               | FStar_Syntax_Syntax.Projector uu____16732 -> true
               | uu____16737 -> false) quals
      | uu____16738 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____16749 = lookup_qname env lid in
      match uu____16749 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____16750, uu____16751, uu____16752, uu____16753,
                 uu____16754, uu____16755);
              FStar_Syntax_Syntax.sigrng = uu____16756;
              FStar_Syntax_Syntax.sigquals = uu____16757;
              FStar_Syntax_Syntax.sigmeta = uu____16758;
              FStar_Syntax_Syntax.sigattrs = uu____16759;_},
            uu____16760),
           uu____16761)
          -> true
      | uu____16816 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____16827 = lookup_qname env lid in
      match uu____16827 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____16828, uu____16829, uu____16830, uu____16831,
                 uu____16832, uu____16833);
              FStar_Syntax_Syntax.sigrng = uu____16834;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____16836;
              FStar_Syntax_Syntax.sigattrs = uu____16837;_},
            uu____16838),
           uu____16839)
          ->
          FStar_Util.for_some
            (fun uu___233_16900 ->
               match uu___233_16900 with
               | FStar_Syntax_Syntax.RecordType uu____16901 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____16910 -> true
               | uu____16919 -> false) quals
      | uu____16920 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____16926, uu____16927);
            FStar_Syntax_Syntax.sigrng = uu____16928;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____16930;
            FStar_Syntax_Syntax.sigattrs = uu____16931;_},
          uu____16932),
         uu____16933)
        ->
        FStar_Util.for_some
          (fun uu___234_16990 ->
             match uu___234_16990 with
             | FStar_Syntax_Syntax.Action uu____16991 -> true
             | uu____16992 -> false) quals
    | uu____16993 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____17004 = lookup_qname env lid in
      FStar_All.pipe_left qninfo_is_action uu____17004
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
      let uu____17018 =
        let uu____17019 = FStar_Syntax_Util.un_uinst head1 in
        uu____17019.FStar_Syntax_Syntax.n in
      match uu____17018 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____17023 ->
               true
           | uu____17024 -> false)
      | uu____17025 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____17036 = lookup_qname env l in
      match uu____17036 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____17038), uu____17039) ->
          FStar_Util.for_some
            (fun uu___235_17087 ->
               match uu___235_17087 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____17088 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____17089 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____17160 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____17176) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____17193 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____17200 ->
                 FStar_Pervasives_Native.Some true
             | uu____17217 -> FStar_Pervasives_Native.Some false) in
      let uu____17218 =
        let uu____17221 = lookup_qname env lid in
        FStar_Util.bind_opt uu____17221 mapper in
      match uu____17218 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params :
  env -> FStar_Ident.lident -> Prims.int FStar_Pervasives_Native.option) =
  fun env ->
    fun lid ->
      let uu____17273 = lookup_qname env lid in
      match uu____17273 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____17276, uu____17277, tps, uu____17279, uu____17280,
                 uu____17281);
              FStar_Syntax_Syntax.sigrng = uu____17282;
              FStar_Syntax_Syntax.sigquals = uu____17283;
              FStar_Syntax_Syntax.sigmeta = uu____17284;
              FStar_Syntax_Syntax.sigattrs = uu____17285;_},
            uu____17286),
           uu____17287)
          -> FStar_Pervasives_Native.Some (FStar_List.length tps)
      | uu____17352 -> FStar_Pervasives_Native.None
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
           (fun uu____17396 ->
              match uu____17396 with
              | (d, uu____17404) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env ->
    fun l ->
      let uu____17419 = effect_decl_opt env l in
      match uu____17419 with
      | FStar_Pervasives_Native.None ->
          let uu____17434 = name_not_found l in
          let uu____17439 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____17434 uu____17439
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____17461 -> fun t -> fun wp -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____17480 ->
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
        let uu____17511 = FStar_Ident.lid_equals l1 l2 in
        if uu____17511
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____17519 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____17519
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____17527 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____17580 ->
                        match uu____17580 with
                        | (m1, m2, uu____17593, uu____17594, uu____17595) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____17527 with
              | FStar_Pervasives_Native.None ->
                  let uu____17612 =
                    let uu____17617 =
                      let uu____17618 = FStar_Syntax_Print.lid_to_string l1 in
                      let uu____17619 = FStar_Syntax_Print.lid_to_string l2 in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____17618
                        uu____17619 in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____17617) in
                  FStar_Errors.raise_error uu____17612 env.range
              | FStar_Pervasives_Native.Some
                  (uu____17626, uu____17627, m3, j1, j2) -> (m3, j1, j2)))
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l1 ->
      fun l2 ->
        let uu____17660 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____17660
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
  'Auu____17676 .
    (FStar_Syntax_Syntax.eff_decl, 'Auu____17676)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls ->
    fun m ->
      let uu____17705 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____17731 ->
                match uu____17731 with
                | (d, uu____17737) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____17705 with
      | FStar_Pervasives_Native.None ->
          let uu____17748 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____17748
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____17761 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____17761 with
           | (uu____17776, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____17794)::(wp, uu____17796)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____17852 -> failwith "Impossible"))
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
          let uu____17907 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid in
          if uu____17907
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____17909 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid in
             if uu____17909
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
                  let uu____17917 = get_range env in
                  let uu____17918 =
                    let uu____17925 =
                      let uu____17926 =
                        let uu____17943 =
                          let uu____17954 = FStar_Syntax_Syntax.as_arg res_t in
                          [uu____17954] in
                        (null_wp, uu____17943) in
                      FStar_Syntax_Syntax.Tm_app uu____17926 in
                    FStar_Syntax_Syntax.mk uu____17925 in
                  uu____17918 FStar_Pervasives_Native.None uu____17917 in
                let uu____17994 =
                  let uu____17995 =
                    let uu____18006 = FStar_Syntax_Syntax.as_arg null_wp_res in
                    [uu____18006] in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____17995;
                    FStar_Syntax_Syntax.flags = []
                  } in
                FStar_Syntax_Syntax.mk_Comp uu____17994))
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___250_18043 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___250_18043.order);
              joins = (uu___250_18043.joins)
            } in
          let uu___251_18052 = env in
          {
            solver = (uu___251_18052.solver);
            range = (uu___251_18052.range);
            curmodule = (uu___251_18052.curmodule);
            gamma = (uu___251_18052.gamma);
            gamma_sig = (uu___251_18052.gamma_sig);
            gamma_cache = (uu___251_18052.gamma_cache);
            modules = (uu___251_18052.modules);
            expected_typ = (uu___251_18052.expected_typ);
            sigtab = (uu___251_18052.sigtab);
            attrtab = (uu___251_18052.attrtab);
            is_pattern = (uu___251_18052.is_pattern);
            instantiate_imp = (uu___251_18052.instantiate_imp);
            effects;
            generalize = (uu___251_18052.generalize);
            letrecs = (uu___251_18052.letrecs);
            top_level = (uu___251_18052.top_level);
            check_uvars = (uu___251_18052.check_uvars);
            use_eq = (uu___251_18052.use_eq);
            is_iface = (uu___251_18052.is_iface);
            admit = (uu___251_18052.admit);
            lax = (uu___251_18052.lax);
            lax_universes = (uu___251_18052.lax_universes);
            phase1 = (uu___251_18052.phase1);
            failhard = (uu___251_18052.failhard);
            nosynth = (uu___251_18052.nosynth);
            uvar_subtyping = (uu___251_18052.uvar_subtyping);
            tc_term = (uu___251_18052.tc_term);
            type_of = (uu___251_18052.type_of);
            universe_of = (uu___251_18052.universe_of);
            check_type_of = (uu___251_18052.check_type_of);
            use_bv_sorts = (uu___251_18052.use_bv_sorts);
            qtbl_name_and_index = (uu___251_18052.qtbl_name_and_index);
            normalized_eff_names = (uu___251_18052.normalized_eff_names);
            fv_delta_depths = (uu___251_18052.fv_delta_depths);
            proof_ns = (uu___251_18052.proof_ns);
            synth_hook = (uu___251_18052.synth_hook);
            splice = (uu___251_18052.splice);
            is_native_tactic = (uu___251_18052.is_native_tactic);
            identifier_info = (uu___251_18052.identifier_info);
            tc_hooks = (uu___251_18052.tc_hooks);
            dsenv = (uu___251_18052.dsenv);
            nbe = (uu___251_18052.nbe)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____18082 = (e1.mlift).mlift_wp u r wp1 in
                (e2.mlift).mlift_wp u r uu____18082 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun wp ->
                              fun e ->
                                let uu____18240 = (e1.mlift).mlift_wp u t wp in
                                let uu____18241 = l1 u t wp e in
                                l2 u t uu____18240 uu____18241))
                | uu____18242 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____18314 = inst_tscheme_with lift_t [u] in
            match uu____18314 with
            | (uu____18321, lift_t1) ->
                let uu____18323 =
                  let uu____18330 =
                    let uu____18331 =
                      let uu____18348 =
                        let uu____18359 = FStar_Syntax_Syntax.as_arg r in
                        let uu____18368 =
                          let uu____18379 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____18379] in
                        uu____18359 :: uu____18368 in
                      (lift_t1, uu____18348) in
                    FStar_Syntax_Syntax.Tm_app uu____18331 in
                  FStar_Syntax_Syntax.mk uu____18330 in
                uu____18323 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____18491 = inst_tscheme_with lift_t [u] in
            match uu____18491 with
            | (uu____18498, lift_t1) ->
                let uu____18500 =
                  let uu____18507 =
                    let uu____18508 =
                      let uu____18525 =
                        let uu____18536 = FStar_Syntax_Syntax.as_arg r in
                        let uu____18545 =
                          let uu____18556 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____18565 =
                            let uu____18576 = FStar_Syntax_Syntax.as_arg e in
                            [uu____18576] in
                          uu____18556 :: uu____18565 in
                        uu____18536 :: uu____18545 in
                      (lift_t1, uu____18525) in
                    FStar_Syntax_Syntax.Tm_app uu____18508 in
                  FStar_Syntax_Syntax.mk uu____18507 in
                uu____18500 FStar_Pervasives_Native.None
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
              let uu____18678 =
                let uu____18679 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____18679
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____18678 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____18683 =
              let uu____18684 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp in
              FStar_Syntax_Print.term_to_string uu____18684 in
            let uu____18685 =
              let uu____18686 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1 ->
                     let uu____18712 = l1 FStar_Syntax_Syntax.U_zero arg wp e in
                     FStar_Syntax_Print.term_to_string uu____18712) in
              FStar_Util.dflt "none" uu____18686 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____18683
              uu____18685 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____18738 ->
                    match uu____18738 with
                    | (e, uu____18746) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____18769 =
            match uu____18769 with
            | (i, j) ->
                let uu____18780 = FStar_Ident.lid_equals i j in
                if uu____18780
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
              let uu____18812 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i ->
                        let uu____18822 = FStar_Ident.lid_equals i k in
                        if uu____18822
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j ->
                                  let uu____18833 =
                                    FStar_Ident.lid_equals j k in
                                  if uu____18833
                                  then []
                                  else
                                    (let uu____18837 =
                                       let uu____18846 =
                                         find_edge order1 (i, k) in
                                       let uu____18849 =
                                         find_edge order1 (k, j) in
                                       (uu____18846, uu____18849) in
                                     match uu____18837 with
                                     | (FStar_Pervasives_Native.Some e1,
                                        FStar_Pervasives_Native.Some e2) ->
                                         let uu____18864 =
                                           compose_edges e1 e2 in
                                         [uu____18864]
                                     | uu____18865 -> []))))) in
              FStar_List.append order1 uu____18812 in
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
                   let uu____18895 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____18897 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____18897
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____18895
                   then
                     let uu____18902 =
                       let uu____18907 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____18907) in
                     let uu____18908 = get_range env in
                     FStar_Errors.raise_error uu____18902 uu____18908
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j ->
                              let join_opt =
                                let uu____18985 = FStar_Ident.lid_equals i j in
                                if uu____18985
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt ->
                                          fun k ->
                                            let uu____19034 =
                                              let uu____19043 =
                                                find_edge order2 (i, k) in
                                              let uu____19046 =
                                                find_edge order2 (j, k) in
                                              (uu____19043, uu____19046) in
                                            match uu____19034 with
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
                                                     (ub, uu____19088,
                                                      uu____19089)
                                                     ->
                                                     let uu____19096 =
                                                       let uu____19101 =
                                                         let uu____19102 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____19102 in
                                                       let uu____19105 =
                                                         let uu____19106 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____19106 in
                                                       (uu____19101,
                                                         uu____19105) in
                                                     (match uu____19096 with
                                                      | (true, true) ->
                                                          let uu____19117 =
                                                            FStar_Ident.lid_equals
                                                              k ub in
                                                          if uu____19117
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
                                            | uu____19142 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None -> []
                              | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___252_19215 = env.effects in
              { decls = (uu___252_19215.decls); order = order2; joins } in
            let uu___253_19216 = env in
            {
              solver = (uu___253_19216.solver);
              range = (uu___253_19216.range);
              curmodule = (uu___253_19216.curmodule);
              gamma = (uu___253_19216.gamma);
              gamma_sig = (uu___253_19216.gamma_sig);
              gamma_cache = (uu___253_19216.gamma_cache);
              modules = (uu___253_19216.modules);
              expected_typ = (uu___253_19216.expected_typ);
              sigtab = (uu___253_19216.sigtab);
              attrtab = (uu___253_19216.attrtab);
              is_pattern = (uu___253_19216.is_pattern);
              instantiate_imp = (uu___253_19216.instantiate_imp);
              effects;
              generalize = (uu___253_19216.generalize);
              letrecs = (uu___253_19216.letrecs);
              top_level = (uu___253_19216.top_level);
              check_uvars = (uu___253_19216.check_uvars);
              use_eq = (uu___253_19216.use_eq);
              is_iface = (uu___253_19216.is_iface);
              admit = (uu___253_19216.admit);
              lax = (uu___253_19216.lax);
              lax_universes = (uu___253_19216.lax_universes);
              phase1 = (uu___253_19216.phase1);
              failhard = (uu___253_19216.failhard);
              nosynth = (uu___253_19216.nosynth);
              uvar_subtyping = (uu___253_19216.uvar_subtyping);
              tc_term = (uu___253_19216.tc_term);
              type_of = (uu___253_19216.type_of);
              universe_of = (uu___253_19216.universe_of);
              check_type_of = (uu___253_19216.check_type_of);
              use_bv_sorts = (uu___253_19216.use_bv_sorts);
              qtbl_name_and_index = (uu___253_19216.qtbl_name_and_index);
              normalized_eff_names = (uu___253_19216.normalized_eff_names);
              fv_delta_depths = (uu___253_19216.fv_delta_depths);
              proof_ns = (uu___253_19216.proof_ns);
              synth_hook = (uu___253_19216.synth_hook);
              splice = (uu___253_19216.splice);
              is_native_tactic = (uu___253_19216.is_native_tactic);
              identifier_info = (uu___253_19216.identifier_info);
              tc_hooks = (uu___253_19216.tc_hooks);
              dsenv = (uu___253_19216.dsenv);
              nbe = (uu___253_19216.nbe)
            }))
      | uu____19217 -> env
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
        | uu____19245 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env ->
    fun comp ->
      let c = comp_to_comp_typ env comp in
      let uu____19257 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____19257 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____19274 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____19274 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____19296 =
                     let uu____19301 =
                       let uu____19302 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____19309 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1")) in
                       let uu____19318 =
                         let uu____19319 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____19319 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____19302 uu____19309 uu____19318 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____19301) in
                   FStar_Errors.raise_error uu____19296
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____19324 =
                     let uu____19335 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____19335 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____19372 ->
                        fun uu____19373 ->
                          match (uu____19372, uu____19373) with
                          | ((x, uu____19403), (t, uu____19405)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____19324 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____19436 =
                     let uu___254_19437 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___254_19437.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___254_19437.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___254_19437.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___254_19437.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____19436
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux :
  'Auu____19448 .
    'Auu____19448 ->
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
          let uu____19478 = effect_decl_opt env effect_name in
          match uu____19478 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, qualifiers) ->
              (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_unknown ->
                   FStar_Pervasives_Native.None
               | uu____19517 ->
                   let c1 = unfold_effect_abbrev env c in
                   let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                   let wp =
                     match c1.FStar_Syntax_Syntax.effect_args with
                     | hd1::uu____19540 -> hd1
                     | [] ->
                         let name = FStar_Ident.string_of_lid effect_name in
                         let message =
                           let uu____19577 =
                             FStar_Util.format1
                               "Not enough arguments for effect %s. " name in
                           Prims.strcat uu____19577
                             (Prims.strcat
                                "This usually happens when you use a partially applied DM4F effect, "
                                "like [TAC int] instead of [Tac int].") in
                         let uu____19578 = get_range env in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                             message) uu____19578 in
                   let repr =
                     inst_effect_fun_with [u_c] env ed
                       ([], (ed.FStar_Syntax_Syntax.repr)) in
                   let uu____19592 =
                     let uu____19595 = get_range env in
                     let uu____19596 =
                       let uu____19603 =
                         let uu____19604 =
                           let uu____19621 =
                             let uu____19632 =
                               FStar_Syntax_Syntax.as_arg res_typ in
                             [uu____19632; wp] in
                           (repr, uu____19621) in
                         FStar_Syntax_Syntax.Tm_app uu____19604 in
                       FStar_Syntax_Syntax.mk uu____19603 in
                     uu____19596 FStar_Pervasives_Native.None uu____19595 in
                   FStar_Pervasives_Native.Some uu____19592)
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
      | uu____19747 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____19758 =
        let uu____19759 = FStar_Syntax_Subst.compress t in
        uu____19759.FStar_Syntax_Syntax.n in
      match uu____19758 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____19762, c) ->
          is_reifiable_comp env c
      | uu____19784 -> false
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun c ->
      fun u_c ->
        let l = FStar_Syntax_Util.comp_effect_name c in
        (let uu____19802 =
           let uu____19803 = is_reifiable_effect env l in
           Prims.op_Negation uu____19803 in
         if uu____19802
         then
           let uu____19804 =
             let uu____19809 =
               let uu____19810 = FStar_Ident.string_of_lid l in
               FStar_Util.format1 "Effect %s cannot be reified" uu____19810 in
             (FStar_Errors.Fatal_EffectCannotBeReified, uu____19809) in
           let uu____19811 = get_range env in
           FStar_Errors.raise_error uu____19804 uu____19811
         else ());
        (let uu____19813 = effect_repr_aux true env c u_c in
         match uu____19813 with
         | FStar_Pervasives_Native.None ->
             failwith "internal error: reifiable effect has no repr?"
         | FStar_Pervasives_Native.Some tm -> tm)
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun s ->
      let sb = ((FStar_Syntax_Util.lids_of_sigelt s), s) in
      let env1 =
        let uu___255_19845 = env in
        {
          solver = (uu___255_19845.solver);
          range = (uu___255_19845.range);
          curmodule = (uu___255_19845.curmodule);
          gamma = (uu___255_19845.gamma);
          gamma_sig = (sb :: (env.gamma_sig));
          gamma_cache = (uu___255_19845.gamma_cache);
          modules = (uu___255_19845.modules);
          expected_typ = (uu___255_19845.expected_typ);
          sigtab = (uu___255_19845.sigtab);
          attrtab = (uu___255_19845.attrtab);
          is_pattern = (uu___255_19845.is_pattern);
          instantiate_imp = (uu___255_19845.instantiate_imp);
          effects = (uu___255_19845.effects);
          generalize = (uu___255_19845.generalize);
          letrecs = (uu___255_19845.letrecs);
          top_level = (uu___255_19845.top_level);
          check_uvars = (uu___255_19845.check_uvars);
          use_eq = (uu___255_19845.use_eq);
          is_iface = (uu___255_19845.is_iface);
          admit = (uu___255_19845.admit);
          lax = (uu___255_19845.lax);
          lax_universes = (uu___255_19845.lax_universes);
          phase1 = (uu___255_19845.phase1);
          failhard = (uu___255_19845.failhard);
          nosynth = (uu___255_19845.nosynth);
          uvar_subtyping = (uu___255_19845.uvar_subtyping);
          tc_term = (uu___255_19845.tc_term);
          type_of = (uu___255_19845.type_of);
          universe_of = (uu___255_19845.universe_of);
          check_type_of = (uu___255_19845.check_type_of);
          use_bv_sorts = (uu___255_19845.use_bv_sorts);
          qtbl_name_and_index = (uu___255_19845.qtbl_name_and_index);
          normalized_eff_names = (uu___255_19845.normalized_eff_names);
          fv_delta_depths = (uu___255_19845.fv_delta_depths);
          proof_ns = (uu___255_19845.proof_ns);
          synth_hook = (uu___255_19845.synth_hook);
          splice = (uu___255_19845.splice);
          is_native_tactic = (uu___255_19845.is_native_tactic);
          identifier_info = (uu___255_19845.identifier_info);
          tc_hooks = (uu___255_19845.tc_hooks);
          dsenv = (uu___255_19845.dsenv);
          nbe = (uu___255_19845.nbe)
        } in
      add_sigelt env1 s;
      (env1.tc_hooks).tc_push_in_gamma_hook env1 (FStar_Util.Inr sb);
      build_lattice env1 s
let (push_local_binding : env -> FStar_Syntax_Syntax.binding -> env) =
  fun env ->
    fun b ->
      let uu___256_19858 = env in
      {
        solver = (uu___256_19858.solver);
        range = (uu___256_19858.range);
        curmodule = (uu___256_19858.curmodule);
        gamma = (b :: (env.gamma));
        gamma_sig = (uu___256_19858.gamma_sig);
        gamma_cache = (uu___256_19858.gamma_cache);
        modules = (uu___256_19858.modules);
        expected_typ = (uu___256_19858.expected_typ);
        sigtab = (uu___256_19858.sigtab);
        attrtab = (uu___256_19858.attrtab);
        is_pattern = (uu___256_19858.is_pattern);
        instantiate_imp = (uu___256_19858.instantiate_imp);
        effects = (uu___256_19858.effects);
        generalize = (uu___256_19858.generalize);
        letrecs = (uu___256_19858.letrecs);
        top_level = (uu___256_19858.top_level);
        check_uvars = (uu___256_19858.check_uvars);
        use_eq = (uu___256_19858.use_eq);
        is_iface = (uu___256_19858.is_iface);
        admit = (uu___256_19858.admit);
        lax = (uu___256_19858.lax);
        lax_universes = (uu___256_19858.lax_universes);
        phase1 = (uu___256_19858.phase1);
        failhard = (uu___256_19858.failhard);
        nosynth = (uu___256_19858.nosynth);
        uvar_subtyping = (uu___256_19858.uvar_subtyping);
        tc_term = (uu___256_19858.tc_term);
        type_of = (uu___256_19858.type_of);
        universe_of = (uu___256_19858.universe_of);
        check_type_of = (uu___256_19858.check_type_of);
        use_bv_sorts = (uu___256_19858.use_bv_sorts);
        qtbl_name_and_index = (uu___256_19858.qtbl_name_and_index);
        normalized_eff_names = (uu___256_19858.normalized_eff_names);
        fv_delta_depths = (uu___256_19858.fv_delta_depths);
        proof_ns = (uu___256_19858.proof_ns);
        synth_hook = (uu___256_19858.synth_hook);
        splice = (uu___256_19858.splice);
        is_native_tactic = (uu___256_19858.is_native_tactic);
        identifier_info = (uu___256_19858.identifier_info);
        tc_hooks = (uu___256_19858.tc_hooks);
        dsenv = (uu___256_19858.dsenv);
        nbe = (uu___256_19858.nbe)
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
            (let uu___257_19913 = env in
             {
               solver = (uu___257_19913.solver);
               range = (uu___257_19913.range);
               curmodule = (uu___257_19913.curmodule);
               gamma = rest;
               gamma_sig = (uu___257_19913.gamma_sig);
               gamma_cache = (uu___257_19913.gamma_cache);
               modules = (uu___257_19913.modules);
               expected_typ = (uu___257_19913.expected_typ);
               sigtab = (uu___257_19913.sigtab);
               attrtab = (uu___257_19913.attrtab);
               is_pattern = (uu___257_19913.is_pattern);
               instantiate_imp = (uu___257_19913.instantiate_imp);
               effects = (uu___257_19913.effects);
               generalize = (uu___257_19913.generalize);
               letrecs = (uu___257_19913.letrecs);
               top_level = (uu___257_19913.top_level);
               check_uvars = (uu___257_19913.check_uvars);
               use_eq = (uu___257_19913.use_eq);
               is_iface = (uu___257_19913.is_iface);
               admit = (uu___257_19913.admit);
               lax = (uu___257_19913.lax);
               lax_universes = (uu___257_19913.lax_universes);
               phase1 = (uu___257_19913.phase1);
               failhard = (uu___257_19913.failhard);
               nosynth = (uu___257_19913.nosynth);
               uvar_subtyping = (uu___257_19913.uvar_subtyping);
               tc_term = (uu___257_19913.tc_term);
               type_of = (uu___257_19913.type_of);
               universe_of = (uu___257_19913.universe_of);
               check_type_of = (uu___257_19913.check_type_of);
               use_bv_sorts = (uu___257_19913.use_bv_sorts);
               qtbl_name_and_index = (uu___257_19913.qtbl_name_and_index);
               normalized_eff_names = (uu___257_19913.normalized_eff_names);
               fv_delta_depths = (uu___257_19913.fv_delta_depths);
               proof_ns = (uu___257_19913.proof_ns);
               synth_hook = (uu___257_19913.synth_hook);
               splice = (uu___257_19913.splice);
               is_native_tactic = (uu___257_19913.is_native_tactic);
               identifier_info = (uu___257_19913.identifier_info);
               tc_hooks = (uu___257_19913.tc_hooks);
               dsenv = (uu___257_19913.dsenv);
               nbe = (uu___257_19913.nbe)
             }))
    | uu____19914 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env ->
    fun bs ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____19942 ->
             match uu____19942 with | (x, uu____19950) -> push_bv env1 x) env
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
            let uu___258_19984 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___258_19984.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___258_19984.FStar_Syntax_Syntax.index);
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
      (let uu___259_20024 = env in
       {
         solver = (uu___259_20024.solver);
         range = (uu___259_20024.range);
         curmodule = (uu___259_20024.curmodule);
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___259_20024.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___259_20024.sigtab);
         attrtab = (uu___259_20024.attrtab);
         is_pattern = (uu___259_20024.is_pattern);
         instantiate_imp = (uu___259_20024.instantiate_imp);
         effects = (uu___259_20024.effects);
         generalize = (uu___259_20024.generalize);
         letrecs = (uu___259_20024.letrecs);
         top_level = (uu___259_20024.top_level);
         check_uvars = (uu___259_20024.check_uvars);
         use_eq = (uu___259_20024.use_eq);
         is_iface = (uu___259_20024.is_iface);
         admit = (uu___259_20024.admit);
         lax = (uu___259_20024.lax);
         lax_universes = (uu___259_20024.lax_universes);
         phase1 = (uu___259_20024.phase1);
         failhard = (uu___259_20024.failhard);
         nosynth = (uu___259_20024.nosynth);
         uvar_subtyping = (uu___259_20024.uvar_subtyping);
         tc_term = (uu___259_20024.tc_term);
         type_of = (uu___259_20024.type_of);
         universe_of = (uu___259_20024.universe_of);
         check_type_of = (uu___259_20024.check_type_of);
         use_bv_sorts = (uu___259_20024.use_bv_sorts);
         qtbl_name_and_index = (uu___259_20024.qtbl_name_and_index);
         normalized_eff_names = (uu___259_20024.normalized_eff_names);
         fv_delta_depths = (uu___259_20024.fv_delta_depths);
         proof_ns = (uu___259_20024.proof_ns);
         synth_hook = (uu___259_20024.synth_hook);
         splice = (uu___259_20024.splice);
         is_native_tactic = (uu___259_20024.is_native_tactic);
         identifier_info = (uu___259_20024.identifier_info);
         tc_hooks = (uu___259_20024.tc_hooks);
         dsenv = (uu___259_20024.dsenv);
         nbe = (uu___259_20024.nbe)
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
        let uu____20066 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____20066 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____20094 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____20094)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env ->
    fun t ->
      let uu___260_20109 = env in
      {
        solver = (uu___260_20109.solver);
        range = (uu___260_20109.range);
        curmodule = (uu___260_20109.curmodule);
        gamma = (uu___260_20109.gamma);
        gamma_sig = (uu___260_20109.gamma_sig);
        gamma_cache = (uu___260_20109.gamma_cache);
        modules = (uu___260_20109.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___260_20109.sigtab);
        attrtab = (uu___260_20109.attrtab);
        is_pattern = (uu___260_20109.is_pattern);
        instantiate_imp = (uu___260_20109.instantiate_imp);
        effects = (uu___260_20109.effects);
        generalize = (uu___260_20109.generalize);
        letrecs = (uu___260_20109.letrecs);
        top_level = (uu___260_20109.top_level);
        check_uvars = (uu___260_20109.check_uvars);
        use_eq = false;
        is_iface = (uu___260_20109.is_iface);
        admit = (uu___260_20109.admit);
        lax = (uu___260_20109.lax);
        lax_universes = (uu___260_20109.lax_universes);
        phase1 = (uu___260_20109.phase1);
        failhard = (uu___260_20109.failhard);
        nosynth = (uu___260_20109.nosynth);
        uvar_subtyping = (uu___260_20109.uvar_subtyping);
        tc_term = (uu___260_20109.tc_term);
        type_of = (uu___260_20109.type_of);
        universe_of = (uu___260_20109.universe_of);
        check_type_of = (uu___260_20109.check_type_of);
        use_bv_sorts = (uu___260_20109.use_bv_sorts);
        qtbl_name_and_index = (uu___260_20109.qtbl_name_and_index);
        normalized_eff_names = (uu___260_20109.normalized_eff_names);
        fv_delta_depths = (uu___260_20109.fv_delta_depths);
        proof_ns = (uu___260_20109.proof_ns);
        synth_hook = (uu___260_20109.synth_hook);
        splice = (uu___260_20109.splice);
        is_native_tactic = (uu___260_20109.is_native_tactic);
        identifier_info = (uu___260_20109.identifier_info);
        tc_hooks = (uu___260_20109.tc_hooks);
        dsenv = (uu___260_20109.dsenv);
        nbe = (uu___260_20109.nbe)
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
    let uu____20137 = expected_typ env_ in
    ((let uu___261_20143 = env_ in
      {
        solver = (uu___261_20143.solver);
        range = (uu___261_20143.range);
        curmodule = (uu___261_20143.curmodule);
        gamma = (uu___261_20143.gamma);
        gamma_sig = (uu___261_20143.gamma_sig);
        gamma_cache = (uu___261_20143.gamma_cache);
        modules = (uu___261_20143.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___261_20143.sigtab);
        attrtab = (uu___261_20143.attrtab);
        is_pattern = (uu___261_20143.is_pattern);
        instantiate_imp = (uu___261_20143.instantiate_imp);
        effects = (uu___261_20143.effects);
        generalize = (uu___261_20143.generalize);
        letrecs = (uu___261_20143.letrecs);
        top_level = (uu___261_20143.top_level);
        check_uvars = (uu___261_20143.check_uvars);
        use_eq = false;
        is_iface = (uu___261_20143.is_iface);
        admit = (uu___261_20143.admit);
        lax = (uu___261_20143.lax);
        lax_universes = (uu___261_20143.lax_universes);
        phase1 = (uu___261_20143.phase1);
        failhard = (uu___261_20143.failhard);
        nosynth = (uu___261_20143.nosynth);
        uvar_subtyping = (uu___261_20143.uvar_subtyping);
        tc_term = (uu___261_20143.tc_term);
        type_of = (uu___261_20143.type_of);
        universe_of = (uu___261_20143.universe_of);
        check_type_of = (uu___261_20143.check_type_of);
        use_bv_sorts = (uu___261_20143.use_bv_sorts);
        qtbl_name_and_index = (uu___261_20143.qtbl_name_and_index);
        normalized_eff_names = (uu___261_20143.normalized_eff_names);
        fv_delta_depths = (uu___261_20143.fv_delta_depths);
        proof_ns = (uu___261_20143.proof_ns);
        synth_hook = (uu___261_20143.synth_hook);
        splice = (uu___261_20143.splice);
        is_native_tactic = (uu___261_20143.is_native_tactic);
        identifier_info = (uu___261_20143.identifier_info);
        tc_hooks = (uu___261_20143.tc_hooks);
        dsenv = (uu___261_20143.dsenv);
        nbe = (uu___261_20143.nbe)
      }), uu____20137)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____20153 =
      let uu____20156 = FStar_Ident.id_of_text "" in [uu____20156] in
    FStar_Ident.lid_of_ids uu____20153 in
  fun env ->
    fun m ->
      let sigs =
        let uu____20162 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____20162
        then
          let uu____20165 =
            FStar_All.pipe_right env.gamma_sig
              (FStar_List.map FStar_Pervasives_Native.snd) in
          FStar_All.pipe_right uu____20165 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___262_20192 = env in
       {
         solver = (uu___262_20192.solver);
         range = (uu___262_20192.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_sig = [];
         gamma_cache = (uu___262_20192.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___262_20192.expected_typ);
         sigtab = (uu___262_20192.sigtab);
         attrtab = (uu___262_20192.attrtab);
         is_pattern = (uu___262_20192.is_pattern);
         instantiate_imp = (uu___262_20192.instantiate_imp);
         effects = (uu___262_20192.effects);
         generalize = (uu___262_20192.generalize);
         letrecs = (uu___262_20192.letrecs);
         top_level = (uu___262_20192.top_level);
         check_uvars = (uu___262_20192.check_uvars);
         use_eq = (uu___262_20192.use_eq);
         is_iface = (uu___262_20192.is_iface);
         admit = (uu___262_20192.admit);
         lax = (uu___262_20192.lax);
         lax_universes = (uu___262_20192.lax_universes);
         phase1 = (uu___262_20192.phase1);
         failhard = (uu___262_20192.failhard);
         nosynth = (uu___262_20192.nosynth);
         uvar_subtyping = (uu___262_20192.uvar_subtyping);
         tc_term = (uu___262_20192.tc_term);
         type_of = (uu___262_20192.type_of);
         universe_of = (uu___262_20192.universe_of);
         check_type_of = (uu___262_20192.check_type_of);
         use_bv_sorts = (uu___262_20192.use_bv_sorts);
         qtbl_name_and_index = (uu___262_20192.qtbl_name_and_index);
         normalized_eff_names = (uu___262_20192.normalized_eff_names);
         fv_delta_depths = (uu___262_20192.fv_delta_depths);
         proof_ns = (uu___262_20192.proof_ns);
         synth_hook = (uu___262_20192.synth_hook);
         splice = (uu___262_20192.splice);
         is_native_tactic = (uu___262_20192.is_native_tactic);
         identifier_info = (uu___262_20192.identifier_info);
         tc_hooks = (uu___262_20192.tc_hooks);
         dsenv = (uu___262_20192.dsenv);
         nbe = (uu___262_20192.nbe)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20243)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid
          (uu____20247, (uu____20248, t)))::tl1 ->
          let uu____20269 =
            let uu____20272 = FStar_Syntax_Free.uvars t in
            ext out uu____20272 in
          aux uu____20269 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20275;
            FStar_Syntax_Syntax.index = uu____20276;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20283 =
            let uu____20286 = FStar_Syntax_Free.uvars t in
            ext out uu____20286 in
          aux uu____20283 tl1 in
    aux no_uvs env.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uu____20343)::tl1 -> aux out tl1
      | (FStar_Syntax_Syntax.Binding_lid
          (uu____20347, (uu____20348, t)))::tl1 ->
          let uu____20369 =
            let uu____20372 = FStar_Syntax_Free.univs t in
            ext out uu____20372 in
          aux uu____20369 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20375;
            FStar_Syntax_Syntax.index = uu____20376;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20383 =
            let uu____20386 = FStar_Syntax_Free.univs t in
            ext out uu____20386 in
          aux uu____20383 tl1 in
    aux no_univs env.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (FStar_Syntax_Syntax.Binding_univ uname)::tl1 ->
          let uu____20447 = FStar_Util.set_add uname out in
          aux uu____20447 tl1
      | (FStar_Syntax_Syntax.Binding_lid
          (uu____20450, (uu____20451, t)))::tl1 ->
          let uu____20472 =
            let uu____20475 = FStar_Syntax_Free.univnames t in
            ext out uu____20475 in
          aux uu____20472 tl1
      | (FStar_Syntax_Syntax.Binding_var
          { FStar_Syntax_Syntax.ppname = uu____20478;
            FStar_Syntax_Syntax.index = uu____20479;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____20486 =
            let uu____20489 = FStar_Syntax_Free.univnames t in
            ext out uu____20489 in
          aux uu____20486 tl1 in
    aux no_univ_names env.gamma
let (bound_vars_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list)
  =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___236_20509 ->
            match uu___236_20509 with
            | FStar_Syntax_Syntax.Binding_var x -> [x]
            | FStar_Syntax_Syntax.Binding_lid uu____20513 -> []
            | FStar_Syntax_Syntax.Binding_univ uu____20526 -> []))
let (binders_of_bindings :
  FStar_Syntax_Syntax.binding Prims.list -> FStar_Syntax_Syntax.binders) =
  fun bs ->
    let uu____20536 =
      let uu____20545 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____20545
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____20536 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env -> bound_vars_of_bindings env.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env -> binders_of_bindings env.gamma
let (print_gamma : FStar_Syntax_Syntax.gamma -> Prims.string) =
  fun gamma ->
    let uu____20589 =
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___237_20599 ->
              match uu___237_20599 with
              | FStar_Syntax_Syntax.Binding_var x ->
                  let uu____20601 = FStar_Syntax_Print.bv_to_string x in
                  Prims.strcat "Binding_var " uu____20601
              | FStar_Syntax_Syntax.Binding_univ u ->
                  Prims.strcat "Binding_univ " u.FStar_Ident.idText
              | FStar_Syntax_Syntax.Binding_lid (l, uu____20604) ->
                  let uu____20621 = FStar_Ident.string_of_lid l in
                  Prims.strcat "Binding_lid " uu____20621)) in
    FStar_All.pipe_right uu____20589 (FStar_String.concat "::\n")
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___238_20628 ->
    match uu___238_20628 with
    | NoDelta -> "NoDelta"
    | InliningDelta -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold d ->
        let uu____20630 = FStar_Syntax_Print.delta_depth_to_string d in
        Prims.strcat "Unfold " uu____20630
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env ->
    let keys = FStar_List.collect FStar_Pervasives_Native.fst env.gamma_sig in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____20650 ->
         fun v1 ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env ->
    fun path ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([], uu____20692) -> true
        | (x::xs1, y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____20711, uu____20712) -> false in
      let uu____20721 =
        FStar_List.tryFind
          (fun uu____20739 ->
             match uu____20739 with | (p, uu____20747) -> list_prefix p path)
          env.proof_ns in
      match uu____20721 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____20758, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____20780 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____20780
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___263_20798 = e in
        {
          solver = (uu___263_20798.solver);
          range = (uu___263_20798.range);
          curmodule = (uu___263_20798.curmodule);
          gamma = (uu___263_20798.gamma);
          gamma_sig = (uu___263_20798.gamma_sig);
          gamma_cache = (uu___263_20798.gamma_cache);
          modules = (uu___263_20798.modules);
          expected_typ = (uu___263_20798.expected_typ);
          sigtab = (uu___263_20798.sigtab);
          attrtab = (uu___263_20798.attrtab);
          is_pattern = (uu___263_20798.is_pattern);
          instantiate_imp = (uu___263_20798.instantiate_imp);
          effects = (uu___263_20798.effects);
          generalize = (uu___263_20798.generalize);
          letrecs = (uu___263_20798.letrecs);
          top_level = (uu___263_20798.top_level);
          check_uvars = (uu___263_20798.check_uvars);
          use_eq = (uu___263_20798.use_eq);
          is_iface = (uu___263_20798.is_iface);
          admit = (uu___263_20798.admit);
          lax = (uu___263_20798.lax);
          lax_universes = (uu___263_20798.lax_universes);
          phase1 = (uu___263_20798.phase1);
          failhard = (uu___263_20798.failhard);
          nosynth = (uu___263_20798.nosynth);
          uvar_subtyping = (uu___263_20798.uvar_subtyping);
          tc_term = (uu___263_20798.tc_term);
          type_of = (uu___263_20798.type_of);
          universe_of = (uu___263_20798.universe_of);
          check_type_of = (uu___263_20798.check_type_of);
          use_bv_sorts = (uu___263_20798.use_bv_sorts);
          qtbl_name_and_index = (uu___263_20798.qtbl_name_and_index);
          normalized_eff_names = (uu___263_20798.normalized_eff_names);
          fv_delta_depths = (uu___263_20798.fv_delta_depths);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___263_20798.synth_hook);
          splice = (uu___263_20798.splice);
          is_native_tactic = (uu___263_20798.is_native_tactic);
          identifier_info = (uu___263_20798.identifier_info);
          tc_hooks = (uu___263_20798.tc_hooks);
          dsenv = (uu___263_20798.dsenv);
          nbe = (uu___263_20798.nbe)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___264_20838 = e in
      {
        solver = (uu___264_20838.solver);
        range = (uu___264_20838.range);
        curmodule = (uu___264_20838.curmodule);
        gamma = (uu___264_20838.gamma);
        gamma_sig = (uu___264_20838.gamma_sig);
        gamma_cache = (uu___264_20838.gamma_cache);
        modules = (uu___264_20838.modules);
        expected_typ = (uu___264_20838.expected_typ);
        sigtab = (uu___264_20838.sigtab);
        attrtab = (uu___264_20838.attrtab);
        is_pattern = (uu___264_20838.is_pattern);
        instantiate_imp = (uu___264_20838.instantiate_imp);
        effects = (uu___264_20838.effects);
        generalize = (uu___264_20838.generalize);
        letrecs = (uu___264_20838.letrecs);
        top_level = (uu___264_20838.top_level);
        check_uvars = (uu___264_20838.check_uvars);
        use_eq = (uu___264_20838.use_eq);
        is_iface = (uu___264_20838.is_iface);
        admit = (uu___264_20838.admit);
        lax = (uu___264_20838.lax);
        lax_universes = (uu___264_20838.lax_universes);
        phase1 = (uu___264_20838.phase1);
        failhard = (uu___264_20838.failhard);
        nosynth = (uu___264_20838.nosynth);
        uvar_subtyping = (uu___264_20838.uvar_subtyping);
        tc_term = (uu___264_20838.tc_term);
        type_of = (uu___264_20838.type_of);
        universe_of = (uu___264_20838.universe_of);
        check_type_of = (uu___264_20838.check_type_of);
        use_bv_sorts = (uu___264_20838.use_bv_sorts);
        qtbl_name_and_index = (uu___264_20838.qtbl_name_and_index);
        normalized_eff_names = (uu___264_20838.normalized_eff_names);
        fv_delta_depths = (uu___264_20838.fv_delta_depths);
        proof_ns = ns;
        synth_hook = (uu___264_20838.synth_hook);
        splice = (uu___264_20838.splice);
        is_native_tactic = (uu___264_20838.is_native_tactic);
        identifier_info = (uu___264_20838.identifier_info);
        tc_hooks = (uu___264_20838.tc_hooks);
        dsenv = (uu___264_20838.dsenv);
        nbe = (uu___264_20838.nbe)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____20853 = FStar_Syntax_Free.names t in
      let uu____20856 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____20853 uu____20856
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____20877 = unbound_vars e t in
      FStar_Util.set_is_empty uu____20877
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____20885 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____20885
let (string_of_proof_ns : env -> Prims.string) =
  fun env ->
    let aux uu____20902 =
      match uu____20902 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____20912 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____20912) in
    let uu____20914 =
      let uu____20917 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____20917 FStar_List.rev in
    FStar_All.pipe_right uu____20914 (FStar_String.concat " ")
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
                  (let uu____20970 =
                     FStar_Syntax_Unionfind.find
                       (imp.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   match uu____20970 with
                   | FStar_Pervasives_Native.Some uu____20973 -> true
                   | FStar_Pervasives_Native.None -> false)))
    | uu____20974 -> false
let (is_trivial_guard_formula : guard_t -> Prims.bool) =
  fun g ->
    match g with
    | { guard_f = FStar_TypeChecker_Common.Trivial; deferred = uu____20980;
        univ_ineqs = uu____20981; implicits = uu____20982;_} -> true
    | uu____20993 -> false
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
          let uu___265_21020 = g in
          {
            guard_f = (FStar_TypeChecker_Common.NonTrivial f');
            deferred = (uu___265_21020.deferred);
            univ_ineqs = (uu___265_21020.univ_ineqs);
            implicits = (uu___265_21020.implicits)
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
          let uu____21055 = FStar_Options.defensive () in
          if uu____21055
          then
            let s = FStar_Syntax_Free.names t in
            let uu____21059 =
              let uu____21060 =
                let uu____21061 = FStar_Util.set_difference s vset in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____21061 in
              Prims.op_Negation uu____21060 in
            (if uu____21059
             then
               let uu____21066 =
                 let uu____21071 =
                   let uu____21072 = FStar_Syntax_Print.term_to_string t in
                   let uu____21073 =
                     let uu____21074 = FStar_Util.set_elements s in
                     FStar_All.pipe_right uu____21074
                       (FStar_Syntax_Print.bvs_to_string ",\n\t") in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____21072 uu____21073 in
                 (FStar_Errors.Warning_Defensive, uu____21071) in
               FStar_Errors.log_issue rng uu____21066
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
          let uu____21105 =
            let uu____21106 = FStar_Options.defensive () in
            Prims.op_Negation uu____21106 in
          if uu____21105
          then ()
          else
            (let uu____21108 =
               FStar_Util.as_set l FStar_Syntax_Syntax.order_bv in
             def_check_vars_in_set rng msg uu____21108 t)
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string -> env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng ->
    fun msg ->
      fun e ->
        fun t ->
          let uu____21131 =
            let uu____21132 = FStar_Options.defensive () in
            Prims.op_Negation uu____21132 in
          if uu____21131
          then ()
          else
            (let uu____21134 = bound_vars e in
             def_check_closed_in rng msg uu____21134 t)
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
          let uu___266_21169 = g in
          let uu____21170 =
            let uu____21171 =
              let uu____21172 =
                let uu____21179 =
                  let uu____21180 =
                    let uu____21197 =
                      let uu____21208 = FStar_Syntax_Syntax.as_arg e in
                      [uu____21208] in
                    (f, uu____21197) in
                  FStar_Syntax_Syntax.Tm_app uu____21180 in
                FStar_Syntax_Syntax.mk uu____21179 in
              uu____21172 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_17 -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____21171 in
          {
            guard_f = uu____21170;
            deferred = (uu___266_21169.deferred);
            univ_ineqs = (uu___266_21169.univ_ineqs);
            implicits = (uu___266_21169.implicits)
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
          let uu___267_21264 = g in
          let uu____21265 =
            let uu____21266 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____21266 in
          {
            guard_f = uu____21265;
            deferred = (uu___267_21264.deferred);
            univ_ineqs = (uu___267_21264.univ_ineqs);
            implicits = (uu___267_21264.implicits)
          }
let (always_map_guard :
  guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) -> guard_t)
  =
  fun g ->
    fun map1 ->
      match g.guard_f with
      | FStar_TypeChecker_Common.Trivial ->
          let uu___268_21282 = g in
          let uu____21283 =
            let uu____21284 = map1 FStar_Syntax_Util.t_true in
            FStar_TypeChecker_Common.NonTrivial uu____21284 in
          {
            guard_f = uu____21283;
            deferred = (uu___268_21282.deferred);
            univ_ineqs = (uu___268_21282.univ_ineqs);
            implicits = (uu___268_21282.implicits)
          }
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___269_21286 = g in
          let uu____21287 =
            let uu____21288 = map1 f in
            FStar_TypeChecker_Common.NonTrivial uu____21288 in
          {
            guard_f = uu____21287;
            deferred = (uu___269_21286.deferred);
            univ_ineqs = (uu___269_21286.univ_ineqs);
            implicits = (uu___269_21286.implicits)
          }
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t ->
    match t with
    | FStar_TypeChecker_Common.Trivial -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____21294 ->
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
          let uu____21309 = FStar_Syntax_Util.mk_conj f1 f2 in
          FStar_TypeChecker_Common.NonTrivial uu____21309
let (check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula) =
  fun t ->
    let uu____21315 =
      let uu____21316 = FStar_Syntax_Util.unmeta t in
      uu____21316.FStar_Syntax_Syntax.n in
    match uu____21315 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____21320 -> FStar_TypeChecker_Common.NonTrivial t
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
        let uu____21361 = f g1.guard_f g2.guard_f in
        {
          guard_f = uu____21361;
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
                       let uu____21451 = FStar_Syntax_Syntax.is_null_binder b in
                       if uu____21451
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f in
            let uu___270_21455 = g in
            {
              guard_f = (FStar_TypeChecker_Common.NonTrivial f1);
              deferred = (uu___270_21455.deferred);
              univ_ineqs = (uu___270_21455.univ_ineqs);
              implicits = (uu___270_21455.implicits)
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
               let uu____21488 = FStar_Syntax_Syntax.is_null_binder b in
               if uu____21488
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
            let uu___271_21511 = g in
            let uu____21512 =
              let uu____21513 = close_forall env binders f in
              FStar_TypeChecker_Common.NonTrivial uu____21513 in
            {
              guard_f = uu____21512;
              deferred = (uu___271_21511.deferred);
              univ_ineqs = (uu___271_21511.univ_ineqs);
              implicits = (uu___271_21511.implicits)
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
            let uu____21551 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid in
            match uu____21551 with
            | FStar_Pervasives_Native.Some
                (uu____21576::(tm, uu____21578)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos in
                (t, [], trivial_guard)
            | uu____21642 ->
                let binders = all_binders env in
                let gamma = env.gamma in
                let ctx_uvar =
                  let uu____21660 = FStar_Syntax_Unionfind.fresh () in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____21660;
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
                    let uu___272_21695 = trivial_guard in
                    {
                      guard_f = (uu___272_21695.guard_f);
                      deferred = (uu___272_21695.deferred);
                      univ_ineqs = (uu___272_21695.univ_ineqs);
                      implicits = [imp]
                    } in
                  (t, [(ctx_uvar, r)], g)))
let (dummy_solver : solver_t) =
  {
    init = (fun uu____21712 -> ());
    push = (fun uu____21714 -> ());
    pop = (fun uu____21716 -> ());
    snapshot =
      (fun uu____21718 ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____21727 -> fun uu____21728 -> ());
    encode_modul = (fun uu____21739 -> fun uu____21740 -> ());
    encode_sig = (fun uu____21743 -> fun uu____21744 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____21750 =
             let uu____21757 = FStar_Options.peek () in (e, g, uu____21757) in
           [uu____21750]);
    solve = (fun uu____21773 -> fun uu____21774 -> fun uu____21775 -> ());
    finish = (fun uu____21781 -> ());
    refresh = (fun uu____21783 -> ())
  }