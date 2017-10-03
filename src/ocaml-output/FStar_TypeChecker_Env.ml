open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2
  | Binding_sig of (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
  FStar_Pervasives_Native.tuple2
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3[@@deriving show]
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____44 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____62 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____94 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____126 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____148 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
  | UnfoldTac[@@deriving show]
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____189 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____194 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____199 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____205 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____218 -> false
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkmlift__item__mlift_wp:
  mlift ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let __proj__Mkmlift__item__mlift_term:
  mlift ->
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
type edge =
  {
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}[@@deriving show]
let __proj__Mkedge__item__msource: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
let __proj__Mkedge__item__mtarget: edge -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
let __proj__Mkedge__item__mlift: edge -> mlift =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list;}[@@deriving show]
let __proj__Mkeffects__item__decls:
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
let __proj__Mkeffects__item__order: effects -> edge Prims.list =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
let __proj__Mkeffects__item__joins:
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
type name_prefix = Prims.string Prims.list[@@deriving show]
type flat_proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list[@@deriving
                                                                    show]
type proof_namespace = flat_proof_namespace Prims.list[@@deriving show]
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2[@@deriving show]
type goal = FStar_Syntax_Syntax.term[@@deriving show]
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  top_level: Prims.bool;
  check_uvars: Prims.bool;
  use_eq: Prims.bool;
  is_iface: Prims.bool;
  admit: Prims.bool;
  lax: Prims.bool;
  lax_universes: Prims.bool;
  failhard: Prims.bool;
  nosynth: Prims.bool;
  tc_term:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index:
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option;
  proof_ns: proof_namespace;
  synth:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term;
  is_native_tactic: FStar_Ident.lid -> Prims.bool;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref;
  tc_hooks: tcenv_hooks;}[@@deriving show]
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit;
  preprocess:
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}[@@deriving show]
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2;
  implicits:
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list;}[@@deriving show]
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> Prims.unit;}[@@deriving show]
let __proj__Mkenv__item__solver: env -> solver_t =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__solver
let __proj__Mkenv__item__range: env -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__range
let __proj__Mkenv__item__curmodule: env -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__curmodule
let __proj__Mkenv__item__gamma: env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__gamma
let __proj__Mkenv__item__gamma_cache: env -> cached_elt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__gamma_cache
let __proj__Mkenv__item__modules: env -> FStar_Syntax_Syntax.modul Prims.list
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__modules
let __proj__Mkenv__item__expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__expected_typ
let __proj__Mkenv__item__sigtab:
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__sigtab
let __proj__Mkenv__item__is_pattern: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_pattern
let __proj__Mkenv__item__instantiate_imp: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__instantiate_imp
let __proj__Mkenv__item__effects: env -> effects =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__effects
let __proj__Mkenv__item__generalize: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__generalize
let __proj__Mkenv__item__letrecs:
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__letrecs
let __proj__Mkenv__item__top_level: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__top_level
let __proj__Mkenv__item__check_uvars: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__check_uvars
let __proj__Mkenv__item__use_eq: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__use_eq
let __proj__Mkenv__item__is_iface: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_iface
let __proj__Mkenv__item__admit: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__admit
let __proj__Mkenv__item__lax: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__lax
let __proj__Mkenv__item__lax_universes: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__lax_universes
let __proj__Mkenv__item__failhard: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__failhard
let __proj__Mkenv__item__nosynth: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__nosynth
let __proj__Mkenv__item__tc_term:
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__tc_term
let __proj__Mkenv__item__type_of:
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__type_of
let __proj__Mkenv__item__universe_of:
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__universe_of
let __proj__Mkenv__item__use_bv_sorts: env -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__use_bv_sorts
let __proj__Mkenv__item__qname_and_index:
  env ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__qname_and_index
let __proj__Mkenv__item__proof_ns: env -> proof_namespace =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__proof_ns
let __proj__Mkenv__item__synth:
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__synth
let __proj__Mkenv__item__is_native_tactic:
  env -> FStar_Ident.lid -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__is_native_tactic
let __proj__Mkenv__item__identifier_info:
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__identifier_info
let __proj__Mkenv__item__tc_hooks: env -> tcenv_hooks =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
        gamma_cache = __fname__gamma_cache; modules = __fname__modules;
        expected_typ = __fname__expected_typ; sigtab = __fname__sigtab;
        is_pattern = __fname__is_pattern;
        instantiate_imp = __fname__instantiate_imp;
        effects = __fname__effects; generalize = __fname__generalize;
        letrecs = __fname__letrecs; top_level = __fname__top_level;
        check_uvars = __fname__check_uvars; use_eq = __fname__use_eq;
        is_iface = __fname__is_iface; admit = __fname__admit;
        lax = __fname__lax; lax_universes = __fname__lax_universes;
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks;_} -> __fname__tc_hooks
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__init
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__push
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__pop
let __proj__Mksolver_t__item__encode_modul:
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_modul
let __proj__Mksolver_t__item__encode_sig:
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__encode_sig
let __proj__Mksolver_t__item__preprocess:
  solver_t ->
    env ->
      goal ->
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__preprocess
let __proj__Mksolver_t__item__solve:
  solver_t ->
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__solve
let __proj__Mksolver_t__item__is_trivial:
  solver_t -> env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__is_trivial
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__finish
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__refresh
let __proj__Mkguard_t__item__guard_f:
  guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
let __proj__Mkguard_t__item__deferred:
  guard_t -> FStar_TypeChecker_Common.deferred =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
let __proj__Mkguard_t__item__univ_ineqs:
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
let __proj__Mkguard_t__item__implicits:
  guard_t ->
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook:
  tcenv_hooks -> env -> binding -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4907  -> fun uu____4908  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___126_4921 = env in
      {
        solver = (uu___126_4921.solver);
        range = (uu___126_4921.range);
        curmodule = (uu___126_4921.curmodule);
        gamma = (uu___126_4921.gamma);
        gamma_cache = (uu___126_4921.gamma_cache);
        modules = (uu___126_4921.modules);
        expected_typ = (uu___126_4921.expected_typ);
        sigtab = (uu___126_4921.sigtab);
        is_pattern = (uu___126_4921.is_pattern);
        instantiate_imp = (uu___126_4921.instantiate_imp);
        effects = (uu___126_4921.effects);
        generalize = (uu___126_4921.generalize);
        letrecs = (uu___126_4921.letrecs);
        top_level = (uu___126_4921.top_level);
        check_uvars = (uu___126_4921.check_uvars);
        use_eq = (uu___126_4921.use_eq);
        is_iface = (uu___126_4921.is_iface);
        admit = (uu___126_4921.admit);
        lax = (uu___126_4921.lax);
        lax_universes = (uu___126_4921.lax_universes);
        failhard = (uu___126_4921.failhard);
        nosynth = (uu___126_4921.nosynth);
        tc_term = (uu___126_4921.tc_term);
        type_of = (uu___126_4921.type_of);
        universe_of = (uu___126_4921.universe_of);
        use_bv_sorts = (uu___126_4921.use_bv_sorts);
        qname_and_index = (uu___126_4921.qname_and_index);
        proof_ns = (uu___126_4921.proof_ns);
        synth = (uu___126_4921.synth);
        is_native_tactic = (uu___126_4921.is_native_tactic);
        identifier_info = (uu___126_4921.identifier_info);
        tc_hooks = hooks
      }
type env_t = env[@@deriving show]
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap[@@deriving show]
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____4936) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4937,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4938,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4939 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4948 . Prims.unit -> 'Auu____4948 FStar_Util.smap =
  fun uu____4954  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4959 . Prims.unit -> 'Auu____4959 FStar_Util.smap =
  fun uu____4965  -> FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
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
        solver_t -> FStar_Ident.lident -> env
  =
  fun tc_term  ->
    fun type_of  ->
      fun universe_of  ->
        fun solver  ->
          fun module_lid  ->
            let uu____5040 = new_gamma_cache () in
            let uu____5043 = new_sigtab () in
            let uu____5046 =
              let uu____5047 = FStar_Options.using_facts_from () in
              match uu____5047 with
              | FStar_Pervasives_Native.Some ns ->
                  let uu____5057 =
                    let uu____5066 =
                      FStar_List.map
                        (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                    FStar_List.append uu____5066 [([], false)] in
                  [uu____5057]
              | FStar_Pervasives_Native.None  -> [[]] in
            let uu____5139 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____5040;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____5043;
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
              failhard = false;
              nosynth = false;
              tc_term;
              type_of;
              universe_of;
              use_bv_sorts = false;
              qname_and_index = FStar_Pervasives_Native.None;
              proof_ns = uu____5046;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5173  -> false);
              identifier_info = uu____5139;
              tc_hooks = default_tc_hooks
            }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____5244  ->
    let uu____5245 = FStar_ST.op_Bang query_indices in
    match uu____5245 with
    | [] -> failwith "Empty query indices!"
    | uu____5322 ->
        let uu____5331 =
          let uu____5340 =
            let uu____5347 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5347 in
          let uu____5424 = FStar_ST.op_Bang query_indices in uu____5340 ::
            uu____5424 in
        FStar_ST.op_Colon_Equals query_indices uu____5331
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5566  ->
    let uu____5567 = FStar_ST.op_Bang query_indices in
    match uu____5567 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5735  ->
    match uu____5735 with
    | (l,n1) ->
        let uu____5742 = FStar_ST.op_Bang query_indices in
        (match uu____5742 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5907 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5925  ->
    let uu____5926 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5926
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6021 =
       let uu____6024 = FStar_ST.op_Bang stack in env :: uu____6024 in
     FStar_ST.op_Colon_Equals stack uu____6021);
    (let uu___127_6127 = env in
     let uu____6128 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6131 = FStar_Util.smap_copy (sigtab env) in
     let uu____6134 =
       let uu____6137 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6137 in
     {
       solver = (uu___127_6127.solver);
       range = (uu___127_6127.range);
       curmodule = (uu___127_6127.curmodule);
       gamma = (uu___127_6127.gamma);
       gamma_cache = uu____6128;
       modules = (uu___127_6127.modules);
       expected_typ = (uu___127_6127.expected_typ);
       sigtab = uu____6131;
       is_pattern = (uu___127_6127.is_pattern);
       instantiate_imp = (uu___127_6127.instantiate_imp);
       effects = (uu___127_6127.effects);
       generalize = (uu___127_6127.generalize);
       letrecs = (uu___127_6127.letrecs);
       top_level = (uu___127_6127.top_level);
       check_uvars = (uu___127_6127.check_uvars);
       use_eq = (uu___127_6127.use_eq);
       is_iface = (uu___127_6127.is_iface);
       admit = (uu___127_6127.admit);
       lax = (uu___127_6127.lax);
       lax_universes = (uu___127_6127.lax_universes);
       failhard = (uu___127_6127.failhard);
       nosynth = (uu___127_6127.nosynth);
       tc_term = (uu___127_6127.tc_term);
       type_of = (uu___127_6127.type_of);
       universe_of = (uu___127_6127.universe_of);
       use_bv_sorts = (uu___127_6127.use_bv_sorts);
       qname_and_index = (uu___127_6127.qname_and_index);
       proof_ns = (uu___127_6127.proof_ns);
       synth = (uu___127_6127.synth);
       is_native_tactic = (uu___127_6127.is_native_tactic);
       identifier_info = uu____6134;
       tc_hooks = (uu___127_6127.tc_hooks)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6201  ->
    let uu____6202 = FStar_ST.op_Bang stack in
    match uu____6202 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6310 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____6358 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6384  ->
                  match uu____6384 with
                  | (m,uu____6390) -> FStar_Ident.lid_equals l m)) in
        (match uu____6358 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___128_6397 = env in
               {
                 solver = (uu___128_6397.solver);
                 range = (uu___128_6397.range);
                 curmodule = (uu___128_6397.curmodule);
                 gamma = (uu___128_6397.gamma);
                 gamma_cache = (uu___128_6397.gamma_cache);
                 modules = (uu___128_6397.modules);
                 expected_typ = (uu___128_6397.expected_typ);
                 sigtab = (uu___128_6397.sigtab);
                 is_pattern = (uu___128_6397.is_pattern);
                 instantiate_imp = (uu___128_6397.instantiate_imp);
                 effects = (uu___128_6397.effects);
                 generalize = (uu___128_6397.generalize);
                 letrecs = (uu___128_6397.letrecs);
                 top_level = (uu___128_6397.top_level);
                 check_uvars = (uu___128_6397.check_uvars);
                 use_eq = (uu___128_6397.use_eq);
                 is_iface = (uu___128_6397.is_iface);
                 admit = (uu___128_6397.admit);
                 lax = (uu___128_6397.lax);
                 lax_universes = (uu___128_6397.lax_universes);
                 failhard = (uu___128_6397.failhard);
                 nosynth = (uu___128_6397.nosynth);
                 tc_term = (uu___128_6397.tc_term);
                 type_of = (uu___128_6397.type_of);
                 universe_of = (uu___128_6397.universe_of);
                 use_bv_sorts = (uu___128_6397.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___128_6397.proof_ns);
                 synth = (uu___128_6397.synth);
                 is_native_tactic = (uu___128_6397.is_native_tactic);
                 identifier_info = (uu___128_6397.identifier_info);
                 tc_hooks = (uu___128_6397.tc_hooks)
               }))
         | FStar_Pervasives_Native.Some (uu____6402,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___129_6410 = env in
               {
                 solver = (uu___129_6410.solver);
                 range = (uu___129_6410.range);
                 curmodule = (uu___129_6410.curmodule);
                 gamma = (uu___129_6410.gamma);
                 gamma_cache = (uu___129_6410.gamma_cache);
                 modules = (uu___129_6410.modules);
                 expected_typ = (uu___129_6410.expected_typ);
                 sigtab = (uu___129_6410.sigtab);
                 is_pattern = (uu___129_6410.is_pattern);
                 instantiate_imp = (uu___129_6410.instantiate_imp);
                 effects = (uu___129_6410.effects);
                 generalize = (uu___129_6410.generalize);
                 letrecs = (uu___129_6410.letrecs);
                 top_level = (uu___129_6410.top_level);
                 check_uvars = (uu___129_6410.check_uvars);
                 use_eq = (uu___129_6410.use_eq);
                 is_iface = (uu___129_6410.is_iface);
                 admit = (uu___129_6410.admit);
                 lax = (uu___129_6410.lax);
                 lax_universes = (uu___129_6410.lax_universes);
                 failhard = (uu___129_6410.failhard);
                 nosynth = (uu___129_6410.nosynth);
                 tc_term = (uu___129_6410.tc_term);
                 type_of = (uu___129_6410.type_of);
                 universe_of = (uu___129_6410.universe_of);
                 use_bv_sorts = (uu___129_6410.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___129_6410.proof_ns);
                 synth = (uu___129_6410.synth);
                 is_native_tactic = (uu___129_6410.is_native_tactic);
                 identifier_info = (uu___129_6410.identifier_info);
                 tc_hooks = (uu___129_6410.tc_hooks)
               })))
let debug: env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let set_range: env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___130_6432 = e in
         {
           solver = (uu___130_6432.solver);
           range = r;
           curmodule = (uu___130_6432.curmodule);
           gamma = (uu___130_6432.gamma);
           gamma_cache = (uu___130_6432.gamma_cache);
           modules = (uu___130_6432.modules);
           expected_typ = (uu___130_6432.expected_typ);
           sigtab = (uu___130_6432.sigtab);
           is_pattern = (uu___130_6432.is_pattern);
           instantiate_imp = (uu___130_6432.instantiate_imp);
           effects = (uu___130_6432.effects);
           generalize = (uu___130_6432.generalize);
           letrecs = (uu___130_6432.letrecs);
           top_level = (uu___130_6432.top_level);
           check_uvars = (uu___130_6432.check_uvars);
           use_eq = (uu___130_6432.use_eq);
           is_iface = (uu___130_6432.is_iface);
           admit = (uu___130_6432.admit);
           lax = (uu___130_6432.lax);
           lax_universes = (uu___130_6432.lax_universes);
           failhard = (uu___130_6432.failhard);
           nosynth = (uu___130_6432.nosynth);
           tc_term = (uu___130_6432.tc_term);
           type_of = (uu___130_6432.type_of);
           universe_of = (uu___130_6432.universe_of);
           use_bv_sorts = (uu___130_6432.use_bv_sorts);
           qname_and_index = (uu___130_6432.qname_and_index);
           proof_ns = (uu___130_6432.proof_ns);
           synth = (uu___130_6432.synth);
           is_native_tactic = (uu___130_6432.is_native_tactic);
           identifier_info = (uu___130_6432.identifier_info);
           tc_hooks = (uu___130_6432.tc_hooks)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6445 =
        let uu____6446 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6446 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6445
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6551 =
          let uu____6552 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6552 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6551
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6657 =
          let uu____6658 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6658 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6657
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6764 =
        let uu____6765 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6765 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6764
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___131_6876 = env in
      {
        solver = (uu___131_6876.solver);
        range = (uu___131_6876.range);
        curmodule = lid;
        gamma = (uu___131_6876.gamma);
        gamma_cache = (uu___131_6876.gamma_cache);
        modules = (uu___131_6876.modules);
        expected_typ = (uu___131_6876.expected_typ);
        sigtab = (uu___131_6876.sigtab);
        is_pattern = (uu___131_6876.is_pattern);
        instantiate_imp = (uu___131_6876.instantiate_imp);
        effects = (uu___131_6876.effects);
        generalize = (uu___131_6876.generalize);
        letrecs = (uu___131_6876.letrecs);
        top_level = (uu___131_6876.top_level);
        check_uvars = (uu___131_6876.check_uvars);
        use_eq = (uu___131_6876.use_eq);
        is_iface = (uu___131_6876.is_iface);
        admit = (uu___131_6876.admit);
        lax = (uu___131_6876.lax);
        lax_universes = (uu___131_6876.lax_universes);
        failhard = (uu___131_6876.failhard);
        nosynth = (uu___131_6876.nosynth);
        tc_term = (uu___131_6876.tc_term);
        type_of = (uu___131_6876.type_of);
        universe_of = (uu___131_6876.universe_of);
        use_bv_sorts = (uu___131_6876.use_bv_sorts);
        qname_and_index = (uu___131_6876.qname_and_index);
        proof_ns = (uu___131_6876.proof_ns);
        synth = (uu___131_6876.synth);
        is_native_tactic = (uu___131_6876.is_native_tactic);
        identifier_info = (uu___131_6876.identifier_info);
        tc_hooks = (uu___131_6876.tc_hooks)
      }
let has_interface: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let find_in_sigtab:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____6907 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6907
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6911  ->
    let uu____6912 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6912
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____6952) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6976 = FStar_Syntax_Subst.subst vs t in (us, uu____6976)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___113_6990  ->
    match uu___113_6990 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7014  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7029 = inst_tscheme t in
      match uu____7029 with
      | (us,t1) ->
          let uu____7040 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7040)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7056  ->
          match uu____7056 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7071 =
                         let uu____7072 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7073 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7074 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7075 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7072 uu____7073 uu____7074 uu____7075 in
                       failwith uu____7071)
                    else ();
                    (let uu____7077 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7077))
               | uu____7084 ->
                   let uu____7085 =
                     let uu____7086 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7086 in
                   failwith uu____7085)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7091 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7096 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7101 -> false
let in_cur_mod: env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
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
             | ([],uu____7137) -> Maybe
             | (uu____7144,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7163 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____7270 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7270 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___114_7315  ->
                   match uu___114_7315 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7358 =
                           let uu____7377 =
                             let uu____7392 = inst_tscheme t in
                             FStar_Util.Inl uu____7392 in
                           (uu____7377, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7358
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7458,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7460);
                                     FStar_Syntax_Syntax.sigrng = uu____7461;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7462;
                                     FStar_Syntax_Syntax.sigmeta = uu____7463;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7464;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7484 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7484
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7530 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7537 -> cache t in
                       let uu____7538 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7538 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7613 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7613 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7699 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7779 = find_in_sigtab env lid in
         match uu____7779 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7878) ->
          add_sigelts env ses
      | uu____7887 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____7901 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___115_7930  ->
           match uu___115_7930 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7948 -> FStar_Pervasives_Native.None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let ((uu____7983,lb::[]),uu____7985) ->
          let uu____7998 =
            let uu____8007 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8016 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8007, uu____8016) in
          FStar_Pervasives_Native.Some uu____7998
      | FStar_Syntax_Syntax.Sig_let ((uu____8029,lbs),uu____8031) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8067 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8079 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8079
                   then
                     let uu____8090 =
                       let uu____8099 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8108 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8099, uu____8108) in
                     FStar_Pervasives_Native.Some uu____8090
                   else FStar_Pervasives_Native.None)
      | uu____8130 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8164 =
          let uu____8173 =
            let uu____8178 =
              let uu____8179 =
                let uu____8182 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8182 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8179) in
            inst_tscheme uu____8178 in
          (uu____8173, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8164
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8202,uu____8203) ->
        let uu____8208 =
          let uu____8217 =
            let uu____8222 =
              let uu____8223 =
                let uu____8226 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8226 in
              (us, uu____8223) in
            inst_tscheme uu____8222 in
          (uu____8217, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8208
    | uu____8243 -> FStar_Pervasives_Native.None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____8303 =
        match uu____8303 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8399,uvs,t,uu____8402,uu____8403,uu____8404);
                    FStar_Syntax_Syntax.sigrng = uu____8405;
                    FStar_Syntax_Syntax.sigquals = uu____8406;
                    FStar_Syntax_Syntax.sigmeta = uu____8407;
                    FStar_Syntax_Syntax.sigattrs = uu____8408;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8429 =
                   let uu____8438 = inst_tscheme (uvs, t) in
                   (uu____8438, rng) in
                 FStar_Pervasives_Native.Some uu____8429
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8458;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8460;
                    FStar_Syntax_Syntax.sigattrs = uu____8461;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8478 =
                   let uu____8479 = in_cur_mod env l in uu____8479 = Yes in
                 if uu____8478
                 then
                   let uu____8490 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8490
                    then
                      let uu____8503 =
                        let uu____8512 = inst_tscheme (uvs, t) in
                        (uu____8512, rng) in
                      FStar_Pervasives_Native.Some uu____8503
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8539 =
                      let uu____8548 = inst_tscheme (uvs, t) in
                      (uu____8548, rng) in
                    FStar_Pervasives_Native.Some uu____8539)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8569,uu____8570);
                    FStar_Syntax_Syntax.sigrng = uu____8571;
                    FStar_Syntax_Syntax.sigquals = uu____8572;
                    FStar_Syntax_Syntax.sigmeta = uu____8573;
                    FStar_Syntax_Syntax.sigattrs = uu____8574;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8613 =
                        let uu____8622 = inst_tscheme (uvs, k) in
                        (uu____8622, rng) in
                      FStar_Pervasives_Native.Some uu____8613
                  | uu____8639 ->
                      let uu____8640 =
                        let uu____8649 =
                          let uu____8654 =
                            let uu____8655 =
                              let uu____8658 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8658 in
                            (uvs, uu____8655) in
                          inst_tscheme uu____8654 in
                        (uu____8649, rng) in
                      FStar_Pervasives_Native.Some uu____8640)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8679,uu____8680);
                    FStar_Syntax_Syntax.sigrng = uu____8681;
                    FStar_Syntax_Syntax.sigquals = uu____8682;
                    FStar_Syntax_Syntax.sigmeta = uu____8683;
                    FStar_Syntax_Syntax.sigattrs = uu____8684;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8724 =
                        let uu____8733 = inst_tscheme_with (uvs, k) us in
                        (uu____8733, rng) in
                      FStar_Pervasives_Native.Some uu____8724
                  | uu____8750 ->
                      let uu____8751 =
                        let uu____8760 =
                          let uu____8765 =
                            let uu____8766 =
                              let uu____8769 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8769 in
                            (uvs, uu____8766) in
                          inst_tscheme_with uu____8765 us in
                        (uu____8760, rng) in
                      FStar_Pervasives_Native.Some uu____8751)
             | FStar_Util.Inr se ->
                 let uu____8803 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8824;
                        FStar_Syntax_Syntax.sigrng = uu____8825;
                        FStar_Syntax_Syntax.sigquals = uu____8826;
                        FStar_Syntax_Syntax.sigmeta = uu____8827;
                        FStar_Syntax_Syntax.sigattrs = uu____8828;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8843 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8803
                   (FStar_Util.map_option
                      (fun uu____8891  ->
                         match uu____8891 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8922 =
        let uu____8933 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8933 mapper in
      match uu____8922 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___132_9026 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___132_9026.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___132_9026.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9053 = lookup_qname env l in
      match uu____9053 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9092 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9142 = try_lookup_bv env bv in
      match uu____9142 with
      | FStar_Pervasives_Native.None  ->
          let uu____9157 =
            let uu____9158 =
              let uu____9163 = variable_not_found bv in (uu____9163, bvr) in
            FStar_Errors.Error uu____9158 in
          FStar_Exn.raise uu____9157
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9174 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9175 = FStar_Range.set_use_range r bvr in
          (uu____9174, uu____9175)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9194 = try_lookup_lid_aux env l in
      match uu____9194 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____9260 =
            let uu____9269 =
              let uu____9274 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____9274) in
            (uu____9269, r1) in
          FStar_Pervasives_Native.Some uu____9260
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9303 = try_lookup_lid env l in
      match uu____9303 with
      | FStar_Pervasives_Native.None  ->
          let uu____9330 =
            let uu____9331 =
              let uu____9336 = name_not_found l in
              (uu____9336, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9331 in
          FStar_Exn.raise uu____9330
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___116_9374  ->
              match uu___116_9374 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9376 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9393 = lookup_qname env lid in
      match uu____9393 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9422,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9425;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9427;
              FStar_Syntax_Syntax.sigattrs = uu____9428;_},FStar_Pervasives_Native.None
            ),uu____9429)
          ->
          let uu____9478 =
            let uu____9489 =
              let uu____9494 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9494) in
            (uu____9489, q) in
          FStar_Pervasives_Native.Some uu____9478
      | uu____9511 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9550 = lookup_qname env lid in
      match uu____9550 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9575,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9578;
              FStar_Syntax_Syntax.sigquals = uu____9579;
              FStar_Syntax_Syntax.sigmeta = uu____9580;
              FStar_Syntax_Syntax.sigattrs = uu____9581;_},FStar_Pervasives_Native.None
            ),uu____9582)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9631 ->
          let uu____9652 =
            let uu____9653 =
              let uu____9658 = name_not_found lid in
              (uu____9658, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9653 in
          FStar_Exn.raise uu____9652
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9675 = lookup_qname env lid in
      match uu____9675 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9700,uvs,t,uu____9703,uu____9704,uu____9705);
              FStar_Syntax_Syntax.sigrng = uu____9706;
              FStar_Syntax_Syntax.sigquals = uu____9707;
              FStar_Syntax_Syntax.sigmeta = uu____9708;
              FStar_Syntax_Syntax.sigattrs = uu____9709;_},FStar_Pervasives_Native.None
            ),uu____9710)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9763 ->
          let uu____9784 =
            let uu____9785 =
              let uu____9790 = name_not_found lid in
              (uu____9790, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9785 in
          FStar_Exn.raise uu____9784
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9809 = lookup_qname env lid in
      match uu____9809 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9836,uu____9837,uu____9838,uu____9839,uu____9840,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9842;
              FStar_Syntax_Syntax.sigquals = uu____9843;
              FStar_Syntax_Syntax.sigmeta = uu____9844;
              FStar_Syntax_Syntax.sigattrs = uu____9845;_},uu____9846),uu____9847)
          -> (true, dcs)
      | uu____9908 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9939 = lookup_qname env lid in
      match uu____9939 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9960,uu____9961,uu____9962,l,uu____9964,uu____9965);
              FStar_Syntax_Syntax.sigrng = uu____9966;
              FStar_Syntax_Syntax.sigquals = uu____9967;
              FStar_Syntax_Syntax.sigmeta = uu____9968;
              FStar_Syntax_Syntax.sigattrs = uu____9969;_},uu____9970),uu____9971)
          -> l
      | uu____10026 ->
          let uu____10047 =
            let uu____10048 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10048 in
          failwith uu____10047
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        let uu____10085 = lookup_qname env lid in
        match uu____10085 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10113)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10164,lbs),uu____10166)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10194 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10194
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10226 -> FStar_Pervasives_Native.None)
        | uu____10231 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10268 = lookup_qname env ftv in
      match uu____10268 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10292) ->
          let uu____10337 = effect_signature se in
          (match uu____10337 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10358,t),r) ->
               let uu____10373 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10373)
      | uu____10374 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10403 = try_lookup_effect_lid env ftv in
      match uu____10403 with
      | FStar_Pervasives_Native.None  ->
          let uu____10406 =
            let uu____10407 =
              let uu____10412 = name_not_found ftv in
              (uu____10412, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10407 in
          FStar_Exn.raise uu____10406
      | FStar_Pervasives_Native.Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____10432 = lookup_qname env lid0 in
        match uu____10432 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10463);
                FStar_Syntax_Syntax.sigrng = uu____10464;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10466;
                FStar_Syntax_Syntax.sigattrs = uu____10467;_},FStar_Pervasives_Native.None
              ),uu____10468)
            ->
            let lid1 =
              let uu____10522 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____10522 in
            let uu____10523 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_10527  ->
                      match uu___117_10527 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10528 -> false)) in
            if uu____10523
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10542 =
                      let uu____10543 =
                        let uu____10544 = get_range env in
                        FStar_Range.string_of_range uu____10544 in
                      let uu____10545 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10546 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10543 uu____10545 uu____10546 in
                    failwith uu____10542) in
               match (binders, univs1) with
               | ([],uu____10553) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10570,uu____10571::uu____10572::uu____10573) ->
                   let uu____10578 =
                     let uu____10579 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10580 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10579 uu____10580 in
                   failwith uu____10578
               | uu____10587 ->
                   let uu____10592 =
                     let uu____10597 =
                       let uu____10598 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10598) in
                     inst_tscheme_with uu____10597 insts in
                   (match uu____10592 with
                    | (uu____10609,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10612 =
                          let uu____10613 = FStar_Syntax_Subst.compress t1 in
                          uu____10613.FStar_Syntax_Syntax.n in
                        (match uu____10612 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10660 -> failwith "Impossible")))
        | uu____10667 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10709 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10709 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10722,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10729 = find1 l2 in
            (match uu____10729 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10736 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10736 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10740 = find1 l in
            (match uu____10740 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10756 = lookup_qname env l1 in
      match uu____10756 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10779;
              FStar_Syntax_Syntax.sigrng = uu____10780;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10782;
              FStar_Syntax_Syntax.sigattrs = uu____10783;_},uu____10784),uu____10785)
          -> q
      | uu____10836 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10872 =
          let uu____10873 =
            let uu____10874 = FStar_Util.string_of_int i in
            let uu____10875 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10874 uu____10875 in
          failwith uu____10873 in
        let uu____10876 = lookup_datacon env lid in
        match uu____10876 with
        | (uu____10881,t) ->
            let uu____10883 =
              let uu____10884 = FStar_Syntax_Subst.compress t in
              uu____10884.FStar_Syntax_Syntax.n in
            (match uu____10883 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10888) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10919 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10919
                      FStar_Pervasives_Native.fst)
             | uu____10928 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10937 = lookup_qname env l in
      match uu____10937 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10958,uu____10959,uu____10960);
              FStar_Syntax_Syntax.sigrng = uu____10961;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10963;
              FStar_Syntax_Syntax.sigattrs = uu____10964;_},uu____10965),uu____10966)
          ->
          FStar_Util.for_some
            (fun uu___118_11019  ->
               match uu___118_11019 with
               | FStar_Syntax_Syntax.Projector uu____11020 -> true
               | uu____11025 -> false) quals
      | uu____11026 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11055 = lookup_qname env lid in
      match uu____11055 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11076,uu____11077,uu____11078,uu____11079,uu____11080,uu____11081);
              FStar_Syntax_Syntax.sigrng = uu____11082;
              FStar_Syntax_Syntax.sigquals = uu____11083;
              FStar_Syntax_Syntax.sigmeta = uu____11084;
              FStar_Syntax_Syntax.sigattrs = uu____11085;_},uu____11086),uu____11087)
          -> true
      | uu____11142 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11171 = lookup_qname env lid in
      match uu____11171 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11192,uu____11193,uu____11194,uu____11195,uu____11196,uu____11197);
              FStar_Syntax_Syntax.sigrng = uu____11198;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11200;
              FStar_Syntax_Syntax.sigattrs = uu____11201;_},uu____11202),uu____11203)
          ->
          FStar_Util.for_some
            (fun uu___119_11264  ->
               match uu___119_11264 with
               | FStar_Syntax_Syntax.RecordType uu____11265 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11274 -> true
               | uu____11283 -> false) quals
      | uu____11284 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11313 = lookup_qname env lid in
      match uu____11313 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11334,uu____11335);
              FStar_Syntax_Syntax.sigrng = uu____11336;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11338;
              FStar_Syntax_Syntax.sigattrs = uu____11339;_},uu____11340),uu____11341)
          ->
          FStar_Util.for_some
            (fun uu___120_11398  ->
               match uu___120_11398 with
               | FStar_Syntax_Syntax.Action uu____11399 -> true
               | uu____11400 -> false) quals
      | uu____11401 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
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
  fun env  ->
    fun head1  ->
      let uu____11433 =
        let uu____11434 = FStar_Syntax_Util.un_uinst head1 in
        uu____11434.FStar_Syntax_Syntax.n in
      match uu____11433 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11438 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11505 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11521) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11538 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11545 ->
                 FStar_Pervasives_Native.Some true
             | uu____11562 -> FStar_Pervasives_Native.Some false) in
      let uu____11563 =
        let uu____11566 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11566 mapper in
      match uu____11563 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11614 = lookup_qname env lid in
      match uu____11614 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11635,uu____11636,tps,uu____11638,uu____11639,uu____11640);
              FStar_Syntax_Syntax.sigrng = uu____11641;
              FStar_Syntax_Syntax.sigquals = uu____11642;
              FStar_Syntax_Syntax.sigmeta = uu____11643;
              FStar_Syntax_Syntax.sigattrs = uu____11644;_},uu____11645),uu____11646)
          -> FStar_List.length tps
      | uu____11709 ->
          let uu____11730 =
            let uu____11731 =
              let uu____11736 = name_not_found lid in
              (uu____11736, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11731 in
          FStar_Exn.raise uu____11730
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____11778  ->
              match uu____11778 with
              | (d,uu____11786) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11799 = effect_decl_opt env l in
      match uu____11799 with
      | FStar_Pervasives_Native.None  ->
          let uu____11814 =
            let uu____11815 =
              let uu____11820 = name_not_found l in
              (uu____11820, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11815 in
          FStar_Exn.raise uu____11814
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid))
          then
            (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____11886 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11939  ->
                       match uu____11939 with
                       | (m1,m2,uu____11952,uu____11953,uu____11954) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11886 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11971 =
                   let uu____11972 =
                     let uu____11977 =
                       let uu____11978 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11979 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11978
                         uu____11979 in
                     (uu____11977, (env.range)) in
                   FStar_Errors.Error uu____11972 in
                 FStar_Exn.raise uu____11971
             | FStar_Pervasives_Native.Some
                 (uu____11986,uu____11987,m3,j1,j2) -> (m3, j1, j2))
let monad_leq:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux:
  'Auu____12030 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12030)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12057 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12083  ->
                match uu____12083 with
                | (d,uu____12089) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12057 with
      | FStar_Pervasives_Native.None  ->
          let uu____12100 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12100
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12113 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12113 with
           | (uu____12124,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12134)::(wp,uu____12136)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12172 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m
let null_wp_for_eff:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          if
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Parser_Const.effect_GTot_lid
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
                 let uu____12221 = get_range env in
                 let uu____12222 =
                   let uu____12225 =
                     let uu____12226 =
                       let uu____12241 =
                         let uu____12244 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12244] in
                       (null_wp, uu____12241) in
                     FStar_Syntax_Syntax.Tm_app uu____12226 in
                   FStar_Syntax_Syntax.mk uu____12225 in
                 uu____12222 FStar_Pervasives_Native.None uu____12221 in
               let uu____12250 =
                 let uu____12251 =
                   let uu____12260 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12260] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12251;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12250)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___133_12271 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___133_12271.order);
              joins = (uu___133_12271.joins)
            } in
          let uu___134_12280 = env in
          {
            solver = (uu___134_12280.solver);
            range = (uu___134_12280.range);
            curmodule = (uu___134_12280.curmodule);
            gamma = (uu___134_12280.gamma);
            gamma_cache = (uu___134_12280.gamma_cache);
            modules = (uu___134_12280.modules);
            expected_typ = (uu___134_12280.expected_typ);
            sigtab = (uu___134_12280.sigtab);
            is_pattern = (uu___134_12280.is_pattern);
            instantiate_imp = (uu___134_12280.instantiate_imp);
            effects;
            generalize = (uu___134_12280.generalize);
            letrecs = (uu___134_12280.letrecs);
            top_level = (uu___134_12280.top_level);
            check_uvars = (uu___134_12280.check_uvars);
            use_eq = (uu___134_12280.use_eq);
            is_iface = (uu___134_12280.is_iface);
            admit = (uu___134_12280.admit);
            lax = (uu___134_12280.lax);
            lax_universes = (uu___134_12280.lax_universes);
            failhard = (uu___134_12280.failhard);
            nosynth = (uu___134_12280.nosynth);
            tc_term = (uu___134_12280.tc_term);
            type_of = (uu___134_12280.type_of);
            universe_of = (uu___134_12280.universe_of);
            use_bv_sorts = (uu___134_12280.use_bv_sorts);
            qname_and_index = (uu___134_12280.qname_and_index);
            proof_ns = (uu___134_12280.proof_ns);
            synth = (uu___134_12280.synth);
            is_native_tactic = (uu___134_12280.is_native_tactic);
            identifier_info = (uu___134_12280.identifier_info);
            tc_hooks = (uu___134_12280.tc_hooks)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12297 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12297 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12387 = (e1.mlift).mlift_wp t wp in
                              let uu____12388 = l1 t wp e in
                              l2 t uu____12387 uu____12388))
                | uu____12389 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12428 = inst_tscheme lift_t in
            match uu____12428 with
            | (uu____12435,lift_t1) ->
                let uu____12437 =
                  let uu____12440 =
                    let uu____12441 =
                      let uu____12456 =
                        let uu____12459 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12460 =
                          let uu____12463 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12463] in
                        uu____12459 :: uu____12460 in
                      (lift_t1, uu____12456) in
                    FStar_Syntax_Syntax.Tm_app uu____12441 in
                  FStar_Syntax_Syntax.mk uu____12440 in
                uu____12437 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12504 = inst_tscheme lift_t in
            match uu____12504 with
            | (uu____12511,lift_t1) ->
                let uu____12513 =
                  let uu____12516 =
                    let uu____12517 =
                      let uu____12532 =
                        let uu____12535 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12536 =
                          let uu____12539 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12540 =
                            let uu____12543 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12543] in
                          uu____12539 :: uu____12540 in
                        uu____12535 :: uu____12536 in
                      (lift_t1, uu____12532) in
                    FStar_Syntax_Syntax.Tm_app uu____12517 in
                  FStar_Syntax_Syntax.mk uu____12516 in
                uu____12513 FStar_Pervasives_Native.None
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
              let uu____12581 =
                let uu____12582 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12582
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12581 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12586 =
              let uu____12587 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12587 in
            let uu____12588 =
              let uu____12589 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12607 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12607) in
              FStar_Util.dflt "none" uu____12589 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12586
              uu____12588 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12633  ->
                    match uu____12633 with
                    | (e,uu____12641) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12660 =
            match uu____12660 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____12698 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____12719 =
                                       let uu____12728 =
                                         find_edge order1 (i, k) in
                                       let uu____12731 =
                                         find_edge order1 (k, j) in
                                       (uu____12728, uu____12731) in
                                     match uu____12719 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12746 =
                                           compose_edges e1 e2 in
                                         [uu____12746]
                                     | uu____12747 -> []))))) in
              FStar_List.append order1 uu____12698 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____12776 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12778 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12778
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12776
                   then
                     let uu____12783 =
                       let uu____12784 =
                         let uu____12789 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12790 = get_range env in
                         (uu____12789, uu____12790) in
                       FStar_Errors.Error uu____12784 in
                     FStar_Exn.raise uu____12783
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____12915 =
                                              let uu____12924 =
                                                find_edge order2 (i, k) in
                                              let uu____12927 =
                                                find_edge order2 (j, k) in
                                              (uu____12924, uu____12927) in
                                            match uu____12915 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12969,uu____12970)
                                                     ->
                                                     let uu____12977 =
                                                       let uu____12982 =
                                                         let uu____12983 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12983 in
                                                       let uu____12986 =
                                                         let uu____12987 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12987 in
                                                       (uu____12982,
                                                         uu____12986) in
                                                     (match uu____12977 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate";
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
                                            | uu____13022 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___135_13095 = env.effects in
              { decls = (uu___135_13095.decls); order = order2; joins } in
            let uu___136_13096 = env in
            {
              solver = (uu___136_13096.solver);
              range = (uu___136_13096.range);
              curmodule = (uu___136_13096.curmodule);
              gamma = (uu___136_13096.gamma);
              gamma_cache = (uu___136_13096.gamma_cache);
              modules = (uu___136_13096.modules);
              expected_typ = (uu___136_13096.expected_typ);
              sigtab = (uu___136_13096.sigtab);
              is_pattern = (uu___136_13096.is_pattern);
              instantiate_imp = (uu___136_13096.instantiate_imp);
              effects;
              generalize = (uu___136_13096.generalize);
              letrecs = (uu___136_13096.letrecs);
              top_level = (uu___136_13096.top_level);
              check_uvars = (uu___136_13096.check_uvars);
              use_eq = (uu___136_13096.use_eq);
              is_iface = (uu___136_13096.is_iface);
              admit = (uu___136_13096.admit);
              lax = (uu___136_13096.lax);
              lax_universes = (uu___136_13096.lax_universes);
              failhard = (uu___136_13096.failhard);
              nosynth = (uu___136_13096.nosynth);
              tc_term = (uu___136_13096.tc_term);
              type_of = (uu___136_13096.type_of);
              universe_of = (uu___136_13096.universe_of);
              use_bv_sorts = (uu___136_13096.use_bv_sorts);
              qname_and_index = (uu___136_13096.qname_and_index);
              proof_ns = (uu___136_13096.proof_ns);
              synth = (uu___136_13096.synth);
              is_native_tactic = (uu___136_13096.is_native_tactic);
              identifier_info = (uu___136_13096.identifier_info);
              tc_hooks = (uu___136_13096.tc_hooks)
            }))
      | uu____13097 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____13123 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13133 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13133 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13150 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13150 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13168 =
                     let uu____13169 =
                       let uu____13174 =
                         let uu____13175 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13180 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13187 =
                           let uu____13188 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13188 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13175 uu____13180 uu____13187 in
                       (uu____13174, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13169 in
                   FStar_Exn.raise uu____13168)
                else ();
                (let inst1 =
                   let uu____13193 =
                     let uu____13202 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13202 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13219  ->
                        fun uu____13220  ->
                          match (uu____13219, uu____13220) with
                          | ((x,uu____13242),(t,uu____13244)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13193 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13263 =
                     let uu___137_13264 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___137_13264.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___137_13264.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___137_13264.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___137_13264.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13263
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux:
  Prims.bool ->
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
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
          let uu____13290 = effect_decl_opt env effect_name in
          match uu____13290 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13323 =
                only_reifiable &&
                  (let uu____13325 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13325) in
              if uu____13323
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13341 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13360 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13389 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13389
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13390 =
                             let uu____13391 =
                               let uu____13396 = get_range env in
                               (message, uu____13396) in
                             FStar_Errors.Error uu____13391 in
                           FStar_Exn.raise uu____13390 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13406 =
                       let uu____13409 = get_range env in
                       let uu____13410 =
                         let uu____13413 =
                           let uu____13414 =
                             let uu____13429 =
                               let uu____13432 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13432; wp] in
                             (repr, uu____13429) in
                           FStar_Syntax_Syntax.Tm_app uu____13414 in
                         FStar_Syntax_Syntax.mk uu____13413 in
                       uu____13410 FStar_Pervasives_Native.None uu____13409 in
                     FStar_Pervasives_Native.Some uu____13406)
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____13484 =
            let uu____13485 =
              let uu____13490 =
                let uu____13491 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13491 in
              let uu____13492 = get_range env in (uu____13490, uu____13492) in
            FStar_Errors.Error uu____13485 in
          FStar_Exn.raise uu____13484 in
        let uu____13493 = effect_repr_aux true env c u_c in
        match uu____13493 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable: env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____13533 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13542 =
        let uu____13543 = FStar_Syntax_Subst.compress t in
        uu____13543.FStar_Syntax_Syntax.n in
      match uu____13542 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13546,c) ->
          is_reifiable_comp env c
      | uu____13564 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13588)::uu____13589 -> x :: rest
        | (Binding_sig_inst uu____13598)::uu____13599 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13614 = push1 x rest1 in local :: uu____13614 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___138_13618 = env in
       let uu____13619 = push1 s env.gamma in
       {
         solver = (uu___138_13618.solver);
         range = (uu___138_13618.range);
         curmodule = (uu___138_13618.curmodule);
         gamma = uu____13619;
         gamma_cache = (uu___138_13618.gamma_cache);
         modules = (uu___138_13618.modules);
         expected_typ = (uu___138_13618.expected_typ);
         sigtab = (uu___138_13618.sigtab);
         is_pattern = (uu___138_13618.is_pattern);
         instantiate_imp = (uu___138_13618.instantiate_imp);
         effects = (uu___138_13618.effects);
         generalize = (uu___138_13618.generalize);
         letrecs = (uu___138_13618.letrecs);
         top_level = (uu___138_13618.top_level);
         check_uvars = (uu___138_13618.check_uvars);
         use_eq = (uu___138_13618.use_eq);
         is_iface = (uu___138_13618.is_iface);
         admit = (uu___138_13618.admit);
         lax = (uu___138_13618.lax);
         lax_universes = (uu___138_13618.lax_universes);
         failhard = (uu___138_13618.failhard);
         nosynth = (uu___138_13618.nosynth);
         tc_term = (uu___138_13618.tc_term);
         type_of = (uu___138_13618.type_of);
         universe_of = (uu___138_13618.universe_of);
         use_bv_sorts = (uu___138_13618.use_bv_sorts);
         qname_and_index = (uu___138_13618.qname_and_index);
         proof_ns = (uu___138_13618.proof_ns);
         synth = (uu___138_13618.synth);
         is_native_tactic = (uu___138_13618.is_native_tactic);
         identifier_info = (uu___138_13618.identifier_info);
         tc_hooks = (uu___138_13618.tc_hooks)
       })
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let push_sigelt_inst:
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let push_local_binding: env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___139_13656 = env in
      {
        solver = (uu___139_13656.solver);
        range = (uu___139_13656.range);
        curmodule = (uu___139_13656.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___139_13656.gamma_cache);
        modules = (uu___139_13656.modules);
        expected_typ = (uu___139_13656.expected_typ);
        sigtab = (uu___139_13656.sigtab);
        is_pattern = (uu___139_13656.is_pattern);
        instantiate_imp = (uu___139_13656.instantiate_imp);
        effects = (uu___139_13656.effects);
        generalize = (uu___139_13656.generalize);
        letrecs = (uu___139_13656.letrecs);
        top_level = (uu___139_13656.top_level);
        check_uvars = (uu___139_13656.check_uvars);
        use_eq = (uu___139_13656.use_eq);
        is_iface = (uu___139_13656.is_iface);
        admit = (uu___139_13656.admit);
        lax = (uu___139_13656.lax);
        lax_universes = (uu___139_13656.lax_universes);
        failhard = (uu___139_13656.failhard);
        nosynth = (uu___139_13656.nosynth);
        tc_term = (uu___139_13656.tc_term);
        type_of = (uu___139_13656.type_of);
        universe_of = (uu___139_13656.universe_of);
        use_bv_sorts = (uu___139_13656.use_bv_sorts);
        qname_and_index = (uu___139_13656.qname_and_index);
        proof_ns = (uu___139_13656.proof_ns);
        synth = (uu___139_13656.synth);
        is_native_tactic = (uu___139_13656.is_native_tactic);
        identifier_info = (uu___139_13656.identifier_info);
        tc_hooks = (uu___139_13656.tc_hooks)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv:
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___140_13690 = env in
             {
               solver = (uu___140_13690.solver);
               range = (uu___140_13690.range);
               curmodule = (uu___140_13690.curmodule);
               gamma = rest;
               gamma_cache = (uu___140_13690.gamma_cache);
               modules = (uu___140_13690.modules);
               expected_typ = (uu___140_13690.expected_typ);
               sigtab = (uu___140_13690.sigtab);
               is_pattern = (uu___140_13690.is_pattern);
               instantiate_imp = (uu___140_13690.instantiate_imp);
               effects = (uu___140_13690.effects);
               generalize = (uu___140_13690.generalize);
               letrecs = (uu___140_13690.letrecs);
               top_level = (uu___140_13690.top_level);
               check_uvars = (uu___140_13690.check_uvars);
               use_eq = (uu___140_13690.use_eq);
               is_iface = (uu___140_13690.is_iface);
               admit = (uu___140_13690.admit);
               lax = (uu___140_13690.lax);
               lax_universes = (uu___140_13690.lax_universes);
               failhard = (uu___140_13690.failhard);
               nosynth = (uu___140_13690.nosynth);
               tc_term = (uu___140_13690.tc_term);
               type_of = (uu___140_13690.type_of);
               universe_of = (uu___140_13690.universe_of);
               use_bv_sorts = (uu___140_13690.use_bv_sorts);
               qname_and_index = (uu___140_13690.qname_and_index);
               proof_ns = (uu___140_13690.proof_ns);
               synth = (uu___140_13690.synth);
               is_native_tactic = (uu___140_13690.is_native_tactic);
               identifier_info = (uu___140_13690.identifier_info);
               tc_hooks = (uu___140_13690.tc_hooks)
             }))
    | uu____13691 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13715  ->
             match uu____13715 with | (x,uu____13721) -> push_bv env1 x) env
        bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___141_13751 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_13751.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_13751.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let push_let_binding:
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
let push_module: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___142_13786 = env in
       {
         solver = (uu___142_13786.solver);
         range = (uu___142_13786.range);
         curmodule = (uu___142_13786.curmodule);
         gamma = [];
         gamma_cache = (uu___142_13786.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___142_13786.sigtab);
         is_pattern = (uu___142_13786.is_pattern);
         instantiate_imp = (uu___142_13786.instantiate_imp);
         effects = (uu___142_13786.effects);
         generalize = (uu___142_13786.generalize);
         letrecs = (uu___142_13786.letrecs);
         top_level = (uu___142_13786.top_level);
         check_uvars = (uu___142_13786.check_uvars);
         use_eq = (uu___142_13786.use_eq);
         is_iface = (uu___142_13786.is_iface);
         admit = (uu___142_13786.admit);
         lax = (uu___142_13786.lax);
         lax_universes = (uu___142_13786.lax_universes);
         failhard = (uu___142_13786.failhard);
         nosynth = (uu___142_13786.nosynth);
         tc_term = (uu___142_13786.tc_term);
         type_of = (uu___142_13786.type_of);
         universe_of = (uu___142_13786.universe_of);
         use_bv_sorts = (uu___142_13786.use_bv_sorts);
         qname_and_index = (uu___142_13786.qname_and_index);
         proof_ns = (uu___142_13786.proof_ns);
         synth = (uu___142_13786.synth);
         is_native_tactic = (uu___142_13786.is_native_tactic);
         identifier_info = (uu___142_13786.identifier_info);
         tc_hooks = (uu___142_13786.tc_hooks)
       })
let push_univ_vars: env -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let open_universes_in:
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____13823 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13823 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13851 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13851)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___143_13866 = env in
      {
        solver = (uu___143_13866.solver);
        range = (uu___143_13866.range);
        curmodule = (uu___143_13866.curmodule);
        gamma = (uu___143_13866.gamma);
        gamma_cache = (uu___143_13866.gamma_cache);
        modules = (uu___143_13866.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___143_13866.sigtab);
        is_pattern = (uu___143_13866.is_pattern);
        instantiate_imp = (uu___143_13866.instantiate_imp);
        effects = (uu___143_13866.effects);
        generalize = (uu___143_13866.generalize);
        letrecs = (uu___143_13866.letrecs);
        top_level = (uu___143_13866.top_level);
        check_uvars = (uu___143_13866.check_uvars);
        use_eq = false;
        is_iface = (uu___143_13866.is_iface);
        admit = (uu___143_13866.admit);
        lax = (uu___143_13866.lax);
        lax_universes = (uu___143_13866.lax_universes);
        failhard = (uu___143_13866.failhard);
        nosynth = (uu___143_13866.nosynth);
        tc_term = (uu___143_13866.tc_term);
        type_of = (uu___143_13866.type_of);
        universe_of = (uu___143_13866.universe_of);
        use_bv_sorts = (uu___143_13866.use_bv_sorts);
        qname_and_index = (uu___143_13866.qname_and_index);
        proof_ns = (uu___143_13866.proof_ns);
        synth = (uu___143_13866.synth);
        is_native_tactic = (uu___143_13866.is_native_tactic);
        identifier_info = (uu___143_13866.identifier_info);
        tc_hooks = (uu___143_13866.tc_hooks)
      }
let expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let clear_expected_typ:
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun env_  ->
    let uu____13892 = expected_typ env_ in
    ((let uu___144_13898 = env_ in
      {
        solver = (uu___144_13898.solver);
        range = (uu___144_13898.range);
        curmodule = (uu___144_13898.curmodule);
        gamma = (uu___144_13898.gamma);
        gamma_cache = (uu___144_13898.gamma_cache);
        modules = (uu___144_13898.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___144_13898.sigtab);
        is_pattern = (uu___144_13898.is_pattern);
        instantiate_imp = (uu___144_13898.instantiate_imp);
        effects = (uu___144_13898.effects);
        generalize = (uu___144_13898.generalize);
        letrecs = (uu___144_13898.letrecs);
        top_level = (uu___144_13898.top_level);
        check_uvars = (uu___144_13898.check_uvars);
        use_eq = false;
        is_iface = (uu___144_13898.is_iface);
        admit = (uu___144_13898.admit);
        lax = (uu___144_13898.lax);
        lax_universes = (uu___144_13898.lax_universes);
        failhard = (uu___144_13898.failhard);
        nosynth = (uu___144_13898.nosynth);
        tc_term = (uu___144_13898.tc_term);
        type_of = (uu___144_13898.type_of);
        universe_of = (uu___144_13898.universe_of);
        use_bv_sorts = (uu___144_13898.use_bv_sorts);
        qname_and_index = (uu___144_13898.qname_and_index);
        proof_ns = (uu___144_13898.proof_ns);
        synth = (uu___144_13898.synth);
        is_native_tactic = (uu___144_13898.is_native_tactic);
        identifier_info = (uu___144_13898.identifier_info);
        tc_hooks = (uu___144_13898.tc_hooks)
      }), uu____13892)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13913 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___121_13923  ->
                    match uu___121_13923 with
                    | Binding_sig (uu____13926,se) -> [se]
                    | uu____13932 -> [])) in
          FStar_All.pipe_right uu____13913 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___145_13939 = env in
       {
         solver = (uu___145_13939.solver);
         range = (uu___145_13939.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___145_13939.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___145_13939.expected_typ);
         sigtab = (uu___145_13939.sigtab);
         is_pattern = (uu___145_13939.is_pattern);
         instantiate_imp = (uu___145_13939.instantiate_imp);
         effects = (uu___145_13939.effects);
         generalize = (uu___145_13939.generalize);
         letrecs = (uu___145_13939.letrecs);
         top_level = (uu___145_13939.top_level);
         check_uvars = (uu___145_13939.check_uvars);
         use_eq = (uu___145_13939.use_eq);
         is_iface = (uu___145_13939.is_iface);
         admit = (uu___145_13939.admit);
         lax = (uu___145_13939.lax);
         lax_universes = (uu___145_13939.lax_universes);
         failhard = (uu___145_13939.failhard);
         nosynth = (uu___145_13939.nosynth);
         tc_term = (uu___145_13939.tc_term);
         type_of = (uu___145_13939.type_of);
         universe_of = (uu___145_13939.universe_of);
         use_bv_sorts = (uu___145_13939.use_bv_sorts);
         qname_and_index = (uu___145_13939.qname_and_index);
         proof_ns = (uu___145_13939.proof_ns);
         synth = (uu___145_13939.synth);
         is_native_tactic = (uu___145_13939.is_native_tactic);
         identifier_info = (uu___145_13939.identifier_info);
         tc_hooks = (uu___145_13939.tc_hooks)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14021)::tl1 -> aux out tl1
      | (Binding_lid (uu____14025,(uu____14026,t)))::tl1 ->
          let uu____14041 =
            let uu____14048 = FStar_Syntax_Free.uvars t in
            ext out uu____14048 in
          aux uu____14041 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14055;
            FStar_Syntax_Syntax.index = uu____14056;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14063 =
            let uu____14070 = FStar_Syntax_Free.uvars t in
            ext out uu____14070 in
          aux uu____14063 tl1
      | (Binding_sig uu____14077)::uu____14078 -> out
      | (Binding_sig_inst uu____14087)::uu____14088 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14144)::tl1 -> aux out tl1
      | (Binding_univ uu____14156)::tl1 -> aux out tl1
      | (Binding_lid (uu____14160,(uu____14161,t)))::tl1 ->
          let uu____14176 =
            let uu____14179 = FStar_Syntax_Free.univs t in
            ext out uu____14179 in
          aux uu____14176 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14182;
            FStar_Syntax_Syntax.index = uu____14183;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14190 =
            let uu____14193 = FStar_Syntax_Free.univs t in
            ext out uu____14193 in
          aux uu____14190 tl1
      | (Binding_sig uu____14196)::uu____14197 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14251)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14267 = FStar_Util.fifo_set_add uname out in
          aux uu____14267 tl1
      | (Binding_lid (uu____14270,(uu____14271,t)))::tl1 ->
          let uu____14286 =
            let uu____14289 = FStar_Syntax_Free.univnames t in
            ext out uu____14289 in
          aux uu____14286 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14292;
            FStar_Syntax_Syntax.index = uu____14293;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14300 =
            let uu____14303 = FStar_Syntax_Free.univnames t in
            ext out uu____14303 in
          aux uu____14300 tl1
      | (Binding_sig uu____14306)::uu____14307 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___122_14332  ->
            match uu___122_14332 with
            | Binding_var x -> [x]
            | Binding_lid uu____14336 -> []
            | Binding_sig uu____14341 -> []
            | Binding_univ uu____14348 -> []
            | Binding_sig_inst uu____14349 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14366 =
      let uu____14369 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14369
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14366 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14394 =
      let uu____14395 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___123_14405  ->
                match uu___123_14405 with
                | Binding_var x ->
                    let uu____14407 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14407
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14410) ->
                    let uu____14411 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14411
                | Binding_sig (ls,uu____14413) ->
                    let uu____14418 =
                      let uu____14419 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14419
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14418
                | Binding_sig_inst (ls,uu____14429,uu____14430) ->
                    let uu____14435 =
                      let uu____14436 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14436
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14435)) in
      FStar_All.pipe_right uu____14395 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14394 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14455 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14455
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14483  ->
                 fun uu____14484  ->
                   match (uu____14483, uu____14484) with
                   | ((b1,uu____14502),(b2,uu____14504)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___124_14551  ->
    match uu___124_14551 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14552 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___125_14571  ->
             match uu___125_14571 with
             | Binding_sig (lids,uu____14577) -> FStar_List.append lids keys
             | uu____14582 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14588  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14624) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14643,uu____14644) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____14681 = list_prefix p path1 in
            if uu____14681 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14695 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14695
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___146_14725 = e in
            {
              solver = (uu___146_14725.solver);
              range = (uu___146_14725.range);
              curmodule = (uu___146_14725.curmodule);
              gamma = (uu___146_14725.gamma);
              gamma_cache = (uu___146_14725.gamma_cache);
              modules = (uu___146_14725.modules);
              expected_typ = (uu___146_14725.expected_typ);
              sigtab = (uu___146_14725.sigtab);
              is_pattern = (uu___146_14725.is_pattern);
              instantiate_imp = (uu___146_14725.instantiate_imp);
              effects = (uu___146_14725.effects);
              generalize = (uu___146_14725.generalize);
              letrecs = (uu___146_14725.letrecs);
              top_level = (uu___146_14725.top_level);
              check_uvars = (uu___146_14725.check_uvars);
              use_eq = (uu___146_14725.use_eq);
              is_iface = (uu___146_14725.is_iface);
              admit = (uu___146_14725.admit);
              lax = (uu___146_14725.lax);
              lax_universes = (uu___146_14725.lax_universes);
              failhard = (uu___146_14725.failhard);
              nosynth = (uu___146_14725.nosynth);
              tc_term = (uu___146_14725.tc_term);
              type_of = (uu___146_14725.type_of);
              universe_of = (uu___146_14725.universe_of);
              use_bv_sorts = (uu___146_14725.use_bv_sorts);
              qname_and_index = (uu___146_14725.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___146_14725.synth);
              is_native_tactic = (uu___146_14725.is_native_tactic);
              identifier_info = (uu___146_14725.identifier_info);
              tc_hooks = (uu___146_14725.tc_hooks)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___147_14752 = e in
    {
      solver = (uu___147_14752.solver);
      range = (uu___147_14752.range);
      curmodule = (uu___147_14752.curmodule);
      gamma = (uu___147_14752.gamma);
      gamma_cache = (uu___147_14752.gamma_cache);
      modules = (uu___147_14752.modules);
      expected_typ = (uu___147_14752.expected_typ);
      sigtab = (uu___147_14752.sigtab);
      is_pattern = (uu___147_14752.is_pattern);
      instantiate_imp = (uu___147_14752.instantiate_imp);
      effects = (uu___147_14752.effects);
      generalize = (uu___147_14752.generalize);
      letrecs = (uu___147_14752.letrecs);
      top_level = (uu___147_14752.top_level);
      check_uvars = (uu___147_14752.check_uvars);
      use_eq = (uu___147_14752.use_eq);
      is_iface = (uu___147_14752.is_iface);
      admit = (uu___147_14752.admit);
      lax = (uu___147_14752.lax);
      lax_universes = (uu___147_14752.lax_universes);
      failhard = (uu___147_14752.failhard);
      nosynth = (uu___147_14752.nosynth);
      tc_term = (uu___147_14752.tc_term);
      type_of = (uu___147_14752.type_of);
      universe_of = (uu___147_14752.universe_of);
      use_bv_sorts = (uu___147_14752.use_bv_sorts);
      qname_and_index = (uu___147_14752.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___147_14752.synth);
      is_native_tactic = (uu___147_14752.is_native_tactic);
      identifier_info = (uu___147_14752.identifier_info);
      tc_hooks = (uu___147_14752.tc_hooks)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14767::rest ->
        let uu___148_14771 = e in
        {
          solver = (uu___148_14771.solver);
          range = (uu___148_14771.range);
          curmodule = (uu___148_14771.curmodule);
          gamma = (uu___148_14771.gamma);
          gamma_cache = (uu___148_14771.gamma_cache);
          modules = (uu___148_14771.modules);
          expected_typ = (uu___148_14771.expected_typ);
          sigtab = (uu___148_14771.sigtab);
          is_pattern = (uu___148_14771.is_pattern);
          instantiate_imp = (uu___148_14771.instantiate_imp);
          effects = (uu___148_14771.effects);
          generalize = (uu___148_14771.generalize);
          letrecs = (uu___148_14771.letrecs);
          top_level = (uu___148_14771.top_level);
          check_uvars = (uu___148_14771.check_uvars);
          use_eq = (uu___148_14771.use_eq);
          is_iface = (uu___148_14771.is_iface);
          admit = (uu___148_14771.admit);
          lax = (uu___148_14771.lax);
          lax_universes = (uu___148_14771.lax_universes);
          failhard = (uu___148_14771.failhard);
          nosynth = (uu___148_14771.nosynth);
          tc_term = (uu___148_14771.tc_term);
          type_of = (uu___148_14771.type_of);
          universe_of = (uu___148_14771.universe_of);
          use_bv_sorts = (uu___148_14771.use_bv_sorts);
          qname_and_index = (uu___148_14771.qname_and_index);
          proof_ns = rest;
          synth = (uu___148_14771.synth);
          is_native_tactic = (uu___148_14771.is_native_tactic);
          identifier_info = (uu___148_14771.identifier_info);
          tc_hooks = (uu___148_14771.tc_hooks)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___149_14784 = e in
      {
        solver = (uu___149_14784.solver);
        range = (uu___149_14784.range);
        curmodule = (uu___149_14784.curmodule);
        gamma = (uu___149_14784.gamma);
        gamma_cache = (uu___149_14784.gamma_cache);
        modules = (uu___149_14784.modules);
        expected_typ = (uu___149_14784.expected_typ);
        sigtab = (uu___149_14784.sigtab);
        is_pattern = (uu___149_14784.is_pattern);
        instantiate_imp = (uu___149_14784.instantiate_imp);
        effects = (uu___149_14784.effects);
        generalize = (uu___149_14784.generalize);
        letrecs = (uu___149_14784.letrecs);
        top_level = (uu___149_14784.top_level);
        check_uvars = (uu___149_14784.check_uvars);
        use_eq = (uu___149_14784.use_eq);
        is_iface = (uu___149_14784.is_iface);
        admit = (uu___149_14784.admit);
        lax = (uu___149_14784.lax);
        lax_universes = (uu___149_14784.lax_universes);
        failhard = (uu___149_14784.failhard);
        nosynth = (uu___149_14784.nosynth);
        tc_term = (uu___149_14784.tc_term);
        type_of = (uu___149_14784.type_of);
        universe_of = (uu___149_14784.universe_of);
        use_bv_sorts = (uu___149_14784.use_bv_sorts);
        qname_and_index = (uu___149_14784.qname_and_index);
        proof_ns = ns;
        synth = (uu___149_14784.synth);
        is_native_tactic = (uu___149_14784.is_native_tactic);
        identifier_info = (uu___149_14784.identifier_info);
        tc_hooks = (uu___149_14784.tc_hooks)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14813 =
        FStar_List.map
          (fun fpns  ->
             let uu____14835 =
               let uu____14836 =
                 let uu____14837 =
                   FStar_List.map
                     (fun uu____14849  ->
                        match uu____14849 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14837 in
               Prims.strcat uu____14836 "]" in
             Prims.strcat "[" uu____14835) pns in
      FStar_String.concat ";" uu____14813 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14865  -> ());
    push = (fun uu____14867  -> ());
    pop = (fun uu____14869  -> ());
    encode_modul = (fun uu____14872  -> fun uu____14873  -> ());
    encode_sig = (fun uu____14876  -> fun uu____14877  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14883 =
             let uu____14890 = FStar_Options.peek () in (e, g, uu____14890) in
           [uu____14883]);
    solve = (fun uu____14906  -> fun uu____14907  -> fun uu____14908  -> ());
    is_trivial = (fun uu____14915  -> fun uu____14916  -> false);
    finish = (fun uu____14918  -> ());
    refresh = (fun uu____14920  -> ())
  }