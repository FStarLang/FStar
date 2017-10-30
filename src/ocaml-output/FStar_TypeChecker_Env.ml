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
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list[@@deriving
                                                                    show]
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
  tc_hooks: tcenv_hooks;
  dsenv: FStar_ToSyntax_Env.env;
  dep_graph: FStar_Parser_Dep.deps;}[@@deriving show]
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__solver
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__range
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma_cache
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__modules
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__expected_typ
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__sigtab
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_pattern
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__instantiate_imp
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__effects
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__generalize
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__letrecs
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__top_level
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_uvars
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_eq
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_iface
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__admit
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax_universes
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__failhard
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__nosynth
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_term
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__type_of
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__universe_of
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_bv_sorts
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qname_and_index
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__proof_ns
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_native_tactic
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__identifier_info
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
let __proj__Mkenv__item__dsenv: env -> FStar_ToSyntax_Env.env =
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dsenv
let __proj__Mkenv__item__dep_graph: env -> FStar_Parser_Dep.deps =
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
let __proj__Mksolver_t__item__encode_modul:
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
let __proj__Mksolver_t__item__encode_sig:
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
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
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
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
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
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
let rename_gamma:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___140_5063  ->
              match uu___140_5063 with
              | Binding_var x ->
                  let y =
                    let uu____5066 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____5066 in
                  let uu____5067 =
                    let uu____5068 = FStar_Syntax_Subst.compress y in
                    uu____5068.FStar_Syntax_Syntax.n in
                  (match uu____5067 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5072 =
                         let uu___154_5073 = y1 in
                         let uu____5074 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___154_5073.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___154_5073.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5074
                         } in
                       Binding_var uu____5072
                   | uu____5077 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___155_5087 = env in
      let uu____5088 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___155_5087.solver);
        range = (uu___155_5087.range);
        curmodule = (uu___155_5087.curmodule);
        gamma = uu____5088;
        gamma_cache = (uu___155_5087.gamma_cache);
        modules = (uu___155_5087.modules);
        expected_typ = (uu___155_5087.expected_typ);
        sigtab = (uu___155_5087.sigtab);
        is_pattern = (uu___155_5087.is_pattern);
        instantiate_imp = (uu___155_5087.instantiate_imp);
        effects = (uu___155_5087.effects);
        generalize = (uu___155_5087.generalize);
        letrecs = (uu___155_5087.letrecs);
        top_level = (uu___155_5087.top_level);
        check_uvars = (uu___155_5087.check_uvars);
        use_eq = (uu___155_5087.use_eq);
        is_iface = (uu___155_5087.is_iface);
        admit = (uu___155_5087.admit);
        lax = (uu___155_5087.lax);
        lax_universes = (uu___155_5087.lax_universes);
        failhard = (uu___155_5087.failhard);
        nosynth = (uu___155_5087.nosynth);
        tc_term = (uu___155_5087.tc_term);
        type_of = (uu___155_5087.type_of);
        universe_of = (uu___155_5087.universe_of);
        use_bv_sorts = (uu___155_5087.use_bv_sorts);
        qname_and_index = (uu___155_5087.qname_and_index);
        proof_ns = (uu___155_5087.proof_ns);
        synth = (uu___155_5087.synth);
        is_native_tactic = (uu___155_5087.is_native_tactic);
        identifier_info = (uu___155_5087.identifier_info);
        tc_hooks = (uu___155_5087.tc_hooks);
        dsenv = (uu___155_5087.dsenv);
        dep_graph = (uu___155_5087.dep_graph)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5095  -> fun uu____5096  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___156_5109 = env in
      {
        solver = (uu___156_5109.solver);
        range = (uu___156_5109.range);
        curmodule = (uu___156_5109.curmodule);
        gamma = (uu___156_5109.gamma);
        gamma_cache = (uu___156_5109.gamma_cache);
        modules = (uu___156_5109.modules);
        expected_typ = (uu___156_5109.expected_typ);
        sigtab = (uu___156_5109.sigtab);
        is_pattern = (uu___156_5109.is_pattern);
        instantiate_imp = (uu___156_5109.instantiate_imp);
        effects = (uu___156_5109.effects);
        generalize = (uu___156_5109.generalize);
        letrecs = (uu___156_5109.letrecs);
        top_level = (uu___156_5109.top_level);
        check_uvars = (uu___156_5109.check_uvars);
        use_eq = (uu___156_5109.use_eq);
        is_iface = (uu___156_5109.is_iface);
        admit = (uu___156_5109.admit);
        lax = (uu___156_5109.lax);
        lax_universes = (uu___156_5109.lax_universes);
        failhard = (uu___156_5109.failhard);
        nosynth = (uu___156_5109.nosynth);
        tc_term = (uu___156_5109.tc_term);
        type_of = (uu___156_5109.type_of);
        universe_of = (uu___156_5109.universe_of);
        use_bv_sorts = (uu___156_5109.use_bv_sorts);
        qname_and_index = (uu___156_5109.qname_and_index);
        proof_ns = (uu___156_5109.proof_ns);
        synth = (uu___156_5109.synth);
        is_native_tactic = (uu___156_5109.is_native_tactic);
        identifier_info = (uu___156_5109.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___156_5109.dsenv);
        dep_graph = (uu___156_5109.dep_graph)
      }
let set_dep_graph: env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___157_5118 = e in
      {
        solver = (uu___157_5118.solver);
        range = (uu___157_5118.range);
        curmodule = (uu___157_5118.curmodule);
        gamma = (uu___157_5118.gamma);
        gamma_cache = (uu___157_5118.gamma_cache);
        modules = (uu___157_5118.modules);
        expected_typ = (uu___157_5118.expected_typ);
        sigtab = (uu___157_5118.sigtab);
        is_pattern = (uu___157_5118.is_pattern);
        instantiate_imp = (uu___157_5118.instantiate_imp);
        effects = (uu___157_5118.effects);
        generalize = (uu___157_5118.generalize);
        letrecs = (uu___157_5118.letrecs);
        top_level = (uu___157_5118.top_level);
        check_uvars = (uu___157_5118.check_uvars);
        use_eq = (uu___157_5118.use_eq);
        is_iface = (uu___157_5118.is_iface);
        admit = (uu___157_5118.admit);
        lax = (uu___157_5118.lax);
        lax_universes = (uu___157_5118.lax_universes);
        failhard = (uu___157_5118.failhard);
        nosynth = (uu___157_5118.nosynth);
        tc_term = (uu___157_5118.tc_term);
        type_of = (uu___157_5118.type_of);
        universe_of = (uu___157_5118.universe_of);
        use_bv_sorts = (uu___157_5118.use_bv_sorts);
        qname_and_index = (uu___157_5118.qname_and_index);
        proof_ns = (uu___157_5118.proof_ns);
        synth = (uu___157_5118.synth);
        is_native_tactic = (uu___157_5118.is_native_tactic);
        identifier_info = (uu___157_5118.identifier_info);
        tc_hooks = (uu___157_5118.tc_hooks);
        dsenv = (uu___157_5118.dsenv);
        dep_graph = g
      }
let dep_graph: env -> FStar_Parser_Dep.deps = fun e  -> e.dep_graph
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
      | (NoDelta ,uu____5137) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5138,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5139,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5140 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5149 . Prims.unit -> 'Auu____5149 FStar_Util.smap =
  fun uu____5155  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5160 . Prims.unit -> 'Auu____5160 FStar_Util.smap =
  fun uu____5166  -> FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
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
          solver_t -> FStar_Ident.lident -> env
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun solver  ->
            fun module_lid  ->
              let uu____5245 = new_gamma_cache () in
              let uu____5248 = new_sigtab () in
              let uu____5251 = FStar_Options.using_facts_from () in
              let uu____5252 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty in
              let uu____5255 = FStar_ToSyntax_Env.empty_env () in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5245;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5248;
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
                proof_ns = uu____5251;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5287  -> false);
                identifier_info = uu____5252;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5255;
                dep_graph = deps
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
  fun uu____5358  ->
    let uu____5359 = FStar_ST.op_Bang query_indices in
    match uu____5359 with
    | [] -> failwith "Empty query indices!"
    | uu____5436 ->
        let uu____5445 =
          let uu____5454 =
            let uu____5461 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5461 in
          let uu____5538 = FStar_ST.op_Bang query_indices in uu____5454 ::
            uu____5538 in
        FStar_ST.op_Colon_Equals query_indices uu____5445
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5680  ->
    let uu____5681 = FStar_ST.op_Bang query_indices in
    match uu____5681 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5849  ->
    match uu____5849 with
    | (l,n1) ->
        let uu____5856 = FStar_ST.op_Bang query_indices in
        (match uu____5856 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6021 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6039  ->
    let uu____6040 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____6040
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6135 =
       let uu____6138 = FStar_ST.op_Bang stack in env :: uu____6138 in
     FStar_ST.op_Colon_Equals stack uu____6135);
    (let uu___158_6241 = env in
     let uu____6242 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6245 = FStar_Util.smap_copy (sigtab env) in
     let uu____6248 =
       let uu____6251 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6251 in
     {
       solver = (uu___158_6241.solver);
       range = (uu___158_6241.range);
       curmodule = (uu___158_6241.curmodule);
       gamma = (uu___158_6241.gamma);
       gamma_cache = uu____6242;
       modules = (uu___158_6241.modules);
       expected_typ = (uu___158_6241.expected_typ);
       sigtab = uu____6245;
       is_pattern = (uu___158_6241.is_pattern);
       instantiate_imp = (uu___158_6241.instantiate_imp);
       effects = (uu___158_6241.effects);
       generalize = (uu___158_6241.generalize);
       letrecs = (uu___158_6241.letrecs);
       top_level = (uu___158_6241.top_level);
       check_uvars = (uu___158_6241.check_uvars);
       use_eq = (uu___158_6241.use_eq);
       is_iface = (uu___158_6241.is_iface);
       admit = (uu___158_6241.admit);
       lax = (uu___158_6241.lax);
       lax_universes = (uu___158_6241.lax_universes);
       failhard = (uu___158_6241.failhard);
       nosynth = (uu___158_6241.nosynth);
       tc_term = (uu___158_6241.tc_term);
       type_of = (uu___158_6241.type_of);
       universe_of = (uu___158_6241.universe_of);
       use_bv_sorts = (uu___158_6241.use_bv_sorts);
       qname_and_index = (uu___158_6241.qname_and_index);
       proof_ns = (uu___158_6241.proof_ns);
       synth = (uu___158_6241.synth);
       is_native_tactic = (uu___158_6241.is_native_tactic);
       identifier_info = uu____6248;
       tc_hooks = (uu___158_6241.tc_hooks);
       dsenv = (uu___158_6241.dsenv);
       dep_graph = (uu___158_6241.dep_graph)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6315  ->
    let uu____6316 = FStar_ST.op_Bang stack in
    match uu____6316 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6424 -> failwith "Impossible: Too many pops"
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
        let uu____6468 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6494  ->
                  match uu____6494 with
                  | (m,uu____6500) -> FStar_Ident.lid_equals l m)) in
        (match uu____6468 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___159_6507 = env in
               {
                 solver = (uu___159_6507.solver);
                 range = (uu___159_6507.range);
                 curmodule = (uu___159_6507.curmodule);
                 gamma = (uu___159_6507.gamma);
                 gamma_cache = (uu___159_6507.gamma_cache);
                 modules = (uu___159_6507.modules);
                 expected_typ = (uu___159_6507.expected_typ);
                 sigtab = (uu___159_6507.sigtab);
                 is_pattern = (uu___159_6507.is_pattern);
                 instantiate_imp = (uu___159_6507.instantiate_imp);
                 effects = (uu___159_6507.effects);
                 generalize = (uu___159_6507.generalize);
                 letrecs = (uu___159_6507.letrecs);
                 top_level = (uu___159_6507.top_level);
                 check_uvars = (uu___159_6507.check_uvars);
                 use_eq = (uu___159_6507.use_eq);
                 is_iface = (uu___159_6507.is_iface);
                 admit = (uu___159_6507.admit);
                 lax = (uu___159_6507.lax);
                 lax_universes = (uu___159_6507.lax_universes);
                 failhard = (uu___159_6507.failhard);
                 nosynth = (uu___159_6507.nosynth);
                 tc_term = (uu___159_6507.tc_term);
                 type_of = (uu___159_6507.type_of);
                 universe_of = (uu___159_6507.universe_of);
                 use_bv_sorts = (uu___159_6507.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___159_6507.proof_ns);
                 synth = (uu___159_6507.synth);
                 is_native_tactic = (uu___159_6507.is_native_tactic);
                 identifier_info = (uu___159_6507.identifier_info);
                 tc_hooks = (uu___159_6507.tc_hooks);
                 dsenv = (uu___159_6507.dsenv);
                 dep_graph = (uu___159_6507.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6512,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___160_6520 = env in
               {
                 solver = (uu___160_6520.solver);
                 range = (uu___160_6520.range);
                 curmodule = (uu___160_6520.curmodule);
                 gamma = (uu___160_6520.gamma);
                 gamma_cache = (uu___160_6520.gamma_cache);
                 modules = (uu___160_6520.modules);
                 expected_typ = (uu___160_6520.expected_typ);
                 sigtab = (uu___160_6520.sigtab);
                 is_pattern = (uu___160_6520.is_pattern);
                 instantiate_imp = (uu___160_6520.instantiate_imp);
                 effects = (uu___160_6520.effects);
                 generalize = (uu___160_6520.generalize);
                 letrecs = (uu___160_6520.letrecs);
                 top_level = (uu___160_6520.top_level);
                 check_uvars = (uu___160_6520.check_uvars);
                 use_eq = (uu___160_6520.use_eq);
                 is_iface = (uu___160_6520.is_iface);
                 admit = (uu___160_6520.admit);
                 lax = (uu___160_6520.lax);
                 lax_universes = (uu___160_6520.lax_universes);
                 failhard = (uu___160_6520.failhard);
                 nosynth = (uu___160_6520.nosynth);
                 tc_term = (uu___160_6520.tc_term);
                 type_of = (uu___160_6520.type_of);
                 universe_of = (uu___160_6520.universe_of);
                 use_bv_sorts = (uu___160_6520.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___160_6520.proof_ns);
                 synth = (uu___160_6520.synth);
                 is_native_tactic = (uu___160_6520.is_native_tactic);
                 identifier_info = (uu___160_6520.identifier_info);
                 tc_hooks = (uu___160_6520.tc_hooks);
                 dsenv = (uu___160_6520.dsenv);
                 dep_graph = (uu___160_6520.dep_graph)
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
        (let uu___161_6542 = e in
         {
           solver = (uu___161_6542.solver);
           range = r;
           curmodule = (uu___161_6542.curmodule);
           gamma = (uu___161_6542.gamma);
           gamma_cache = (uu___161_6542.gamma_cache);
           modules = (uu___161_6542.modules);
           expected_typ = (uu___161_6542.expected_typ);
           sigtab = (uu___161_6542.sigtab);
           is_pattern = (uu___161_6542.is_pattern);
           instantiate_imp = (uu___161_6542.instantiate_imp);
           effects = (uu___161_6542.effects);
           generalize = (uu___161_6542.generalize);
           letrecs = (uu___161_6542.letrecs);
           top_level = (uu___161_6542.top_level);
           check_uvars = (uu___161_6542.check_uvars);
           use_eq = (uu___161_6542.use_eq);
           is_iface = (uu___161_6542.is_iface);
           admit = (uu___161_6542.admit);
           lax = (uu___161_6542.lax);
           lax_universes = (uu___161_6542.lax_universes);
           failhard = (uu___161_6542.failhard);
           nosynth = (uu___161_6542.nosynth);
           tc_term = (uu___161_6542.tc_term);
           type_of = (uu___161_6542.type_of);
           universe_of = (uu___161_6542.universe_of);
           use_bv_sorts = (uu___161_6542.use_bv_sorts);
           qname_and_index = (uu___161_6542.qname_and_index);
           proof_ns = (uu___161_6542.proof_ns);
           synth = (uu___161_6542.synth);
           is_native_tactic = (uu___161_6542.is_native_tactic);
           identifier_info = (uu___161_6542.identifier_info);
           tc_hooks = (uu___161_6542.tc_hooks);
           dsenv = (uu___161_6542.dsenv);
           dep_graph = (uu___161_6542.dep_graph)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6555 =
        let uu____6556 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6556 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6555
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6661 =
          let uu____6662 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6662 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6661
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6767 =
          let uu____6768 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6768 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6767
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6874 =
        let uu____6875 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6875 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6874
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___162_6986 = env in
      {
        solver = (uu___162_6986.solver);
        range = (uu___162_6986.range);
        curmodule = lid;
        gamma = (uu___162_6986.gamma);
        gamma_cache = (uu___162_6986.gamma_cache);
        modules = (uu___162_6986.modules);
        expected_typ = (uu___162_6986.expected_typ);
        sigtab = (uu___162_6986.sigtab);
        is_pattern = (uu___162_6986.is_pattern);
        instantiate_imp = (uu___162_6986.instantiate_imp);
        effects = (uu___162_6986.effects);
        generalize = (uu___162_6986.generalize);
        letrecs = (uu___162_6986.letrecs);
        top_level = (uu___162_6986.top_level);
        check_uvars = (uu___162_6986.check_uvars);
        use_eq = (uu___162_6986.use_eq);
        is_iface = (uu___162_6986.is_iface);
        admit = (uu___162_6986.admit);
        lax = (uu___162_6986.lax);
        lax_universes = (uu___162_6986.lax_universes);
        failhard = (uu___162_6986.failhard);
        nosynth = (uu___162_6986.nosynth);
        tc_term = (uu___162_6986.tc_term);
        type_of = (uu___162_6986.type_of);
        universe_of = (uu___162_6986.universe_of);
        use_bv_sorts = (uu___162_6986.use_bv_sorts);
        qname_and_index = (uu___162_6986.qname_and_index);
        proof_ns = (uu___162_6986.proof_ns);
        synth = (uu___162_6986.synth);
        is_native_tactic = (uu___162_6986.is_native_tactic);
        identifier_info = (uu___162_6986.identifier_info);
        tc_hooks = (uu___162_6986.tc_hooks);
        dsenv = (uu___162_6986.dsenv);
        dep_graph = (uu___162_6986.dep_graph)
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
    let uu____7017 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____7017
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7021  ->
    let uu____7022 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____7022
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
      | ((formals,t),uu____7062) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____7086 = FStar_Syntax_Subst.subst vs t in (us, uu____7086)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___141_7100  ->
    match uu___141_7100 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7124  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7139 = inst_tscheme t in
      match uu____7139 with
      | (us,t1) ->
          let uu____7150 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7150)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7166  ->
          match uu____7166 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7181 =
                         let uu____7182 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7183 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7184 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7185 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7182 uu____7183 uu____7184 uu____7185 in
                       failwith uu____7181)
                    else ();
                    (let uu____7187 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7187))
               | uu____7194 ->
                   let uu____7195 =
                     let uu____7196 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7196 in
                   failwith uu____7195)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7201 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7206 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7211 -> false
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
             | ([],uu____7247) -> Maybe
             | (uu____7254,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7273 -> No in
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
          let uu____7380 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7380 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___142_7425  ->
                   match uu___142_7425 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7468 =
                           let uu____7487 =
                             let uu____7502 = inst_tscheme t in
                             FStar_Util.Inl uu____7502 in
                           (uu____7487, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7468
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7568,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7570);
                                     FStar_Syntax_Syntax.sigrng = uu____7571;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7572;
                                     FStar_Syntax_Syntax.sigmeta = uu____7573;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7574;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7594 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7594
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7640 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7647 -> cache t in
                       let uu____7648 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7648 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7723 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7723 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7809 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7889 = find_in_sigtab env lid in
         match uu____7889 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7988) ->
          add_sigelts env ses
      | uu____7997 ->
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
            | uu____8011 -> ()))
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
        (fun uu___143_8040  ->
           match uu___143_8040 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8058 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____8093,lb::[]),uu____8095) ->
          let uu____8108 =
            let uu____8117 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8126 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8117, uu____8126) in
          FStar_Pervasives_Native.Some uu____8108
      | FStar_Syntax_Syntax.Sig_let ((uu____8139,lbs),uu____8141) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8177 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8189 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8189
                   then
                     let uu____8200 =
                       let uu____8209 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8218 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8209, uu____8218) in
                     FStar_Pervasives_Native.Some uu____8200
                   else FStar_Pervasives_Native.None)
      | uu____8240 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8274 =
          let uu____8283 =
            let uu____8288 =
              let uu____8289 =
                let uu____8292 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8292 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8289) in
            inst_tscheme uu____8288 in
          (uu____8283, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8274
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8312,uu____8313) ->
        let uu____8318 =
          let uu____8327 =
            let uu____8332 =
              let uu____8333 =
                let uu____8336 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8336 in
              (us, uu____8333) in
            inst_tscheme uu____8332 in
          (uu____8327, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8318
    | uu____8353 -> FStar_Pervasives_Native.None
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
      let mapper uu____8413 =
        match uu____8413 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8509,uvs,t,uu____8512,uu____8513,uu____8514);
                    FStar_Syntax_Syntax.sigrng = uu____8515;
                    FStar_Syntax_Syntax.sigquals = uu____8516;
                    FStar_Syntax_Syntax.sigmeta = uu____8517;
                    FStar_Syntax_Syntax.sigattrs = uu____8518;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8539 =
                   let uu____8548 = inst_tscheme (uvs, t) in
                   (uu____8548, rng) in
                 FStar_Pervasives_Native.Some uu____8539
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8568;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8570;
                    FStar_Syntax_Syntax.sigattrs = uu____8571;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8588 =
                   let uu____8589 = in_cur_mod env l in uu____8589 = Yes in
                 if uu____8588
                 then
                   let uu____8600 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8600
                    then
                      let uu____8613 =
                        let uu____8622 = inst_tscheme (uvs, t) in
                        (uu____8622, rng) in
                      FStar_Pervasives_Native.Some uu____8613
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8649 =
                      let uu____8658 = inst_tscheme (uvs, t) in
                      (uu____8658, rng) in
                    FStar_Pervasives_Native.Some uu____8649)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8679,uu____8680);
                    FStar_Syntax_Syntax.sigrng = uu____8681;
                    FStar_Syntax_Syntax.sigquals = uu____8682;
                    FStar_Syntax_Syntax.sigmeta = uu____8683;
                    FStar_Syntax_Syntax.sigattrs = uu____8684;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8723 =
                        let uu____8732 = inst_tscheme (uvs, k) in
                        (uu____8732, rng) in
                      FStar_Pervasives_Native.Some uu____8723
                  | uu____8749 ->
                      let uu____8750 =
                        let uu____8759 =
                          let uu____8764 =
                            let uu____8765 =
                              let uu____8768 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8768 in
                            (uvs, uu____8765) in
                          inst_tscheme uu____8764 in
                        (uu____8759, rng) in
                      FStar_Pervasives_Native.Some uu____8750)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8789,uu____8790);
                    FStar_Syntax_Syntax.sigrng = uu____8791;
                    FStar_Syntax_Syntax.sigquals = uu____8792;
                    FStar_Syntax_Syntax.sigmeta = uu____8793;
                    FStar_Syntax_Syntax.sigattrs = uu____8794;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8834 =
                        let uu____8843 = inst_tscheme_with (uvs, k) us in
                        (uu____8843, rng) in
                      FStar_Pervasives_Native.Some uu____8834
                  | uu____8860 ->
                      let uu____8861 =
                        let uu____8870 =
                          let uu____8875 =
                            let uu____8876 =
                              let uu____8879 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8879 in
                            (uvs, uu____8876) in
                          inst_tscheme_with uu____8875 us in
                        (uu____8870, rng) in
                      FStar_Pervasives_Native.Some uu____8861)
             | FStar_Util.Inr se ->
                 let uu____8913 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8934;
                        FStar_Syntax_Syntax.sigrng = uu____8935;
                        FStar_Syntax_Syntax.sigquals = uu____8936;
                        FStar_Syntax_Syntax.sigmeta = uu____8937;
                        FStar_Syntax_Syntax.sigattrs = uu____8938;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8953 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8913
                   (FStar_Util.map_option
                      (fun uu____9001  ->
                         match uu____9001 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____9032 =
        let uu____9043 = lookup_qname env lid in
        FStar_Util.bind_opt uu____9043 mapper in
      match uu____9032 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___163_9136 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___163_9136.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___163_9136.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9163 = lookup_qname env l in
      match uu____9163 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9202 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9252 = try_lookup_bv env bv in
      match uu____9252 with
      | FStar_Pervasives_Native.None  ->
          let uu____9267 =
            let uu____9268 =
              let uu____9273 = variable_not_found bv in (uu____9273, bvr) in
            FStar_Errors.Error uu____9268 in
          FStar_Exn.raise uu____9267
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9284 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9285 =
            let uu____9286 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9286 in
          (uu____9284, uu____9285)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9305 = try_lookup_lid_aux env l in
      match uu____9305 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9371 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9371 in
          let uu____9372 =
            let uu____9381 =
              let uu____9386 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9386) in
            (uu____9381, r1) in
          FStar_Pervasives_Native.Some uu____9372
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9415 = try_lookup_lid env l in
      match uu____9415 with
      | FStar_Pervasives_Native.None  ->
          let uu____9442 =
            let uu____9443 =
              let uu____9448 = name_not_found l in
              (uu____9448, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9443 in
          FStar_Exn.raise uu____9442
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___144_9486  ->
              match uu___144_9486 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9488 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9505 = lookup_qname env lid in
      match uu____9505 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9534,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9537;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9539;
              FStar_Syntax_Syntax.sigattrs = uu____9540;_},FStar_Pervasives_Native.None
            ),uu____9541)
          ->
          let uu____9590 =
            let uu____9601 =
              let uu____9606 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9606) in
            (uu____9601, q) in
          FStar_Pervasives_Native.Some uu____9590
      | uu____9623 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9662 = lookup_qname env lid in
      match uu____9662 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9687,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9690;
              FStar_Syntax_Syntax.sigquals = uu____9691;
              FStar_Syntax_Syntax.sigmeta = uu____9692;
              FStar_Syntax_Syntax.sigattrs = uu____9693;_},FStar_Pervasives_Native.None
            ),uu____9694)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9743 ->
          let uu____9764 =
            let uu____9765 =
              let uu____9770 = name_not_found lid in
              (uu____9770, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9765 in
          FStar_Exn.raise uu____9764
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9787 = lookup_qname env lid in
      match uu____9787 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9812,uvs,t,uu____9815,uu____9816,uu____9817);
              FStar_Syntax_Syntax.sigrng = uu____9818;
              FStar_Syntax_Syntax.sigquals = uu____9819;
              FStar_Syntax_Syntax.sigmeta = uu____9820;
              FStar_Syntax_Syntax.sigattrs = uu____9821;_},FStar_Pervasives_Native.None
            ),uu____9822)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9875 ->
          let uu____9896 =
            let uu____9897 =
              let uu____9902 = name_not_found lid in
              (uu____9902, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9897 in
          FStar_Exn.raise uu____9896
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9921 = lookup_qname env lid in
      match uu____9921 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9948,uu____9949,uu____9950,uu____9951,uu____9952,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9954;
              FStar_Syntax_Syntax.sigquals = uu____9955;
              FStar_Syntax_Syntax.sigmeta = uu____9956;
              FStar_Syntax_Syntax.sigattrs = uu____9957;_},uu____9958),uu____9959)
          -> (true, dcs)
      | uu____10020 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____10051 = lookup_qname env lid in
      match uu____10051 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10072,uu____10073,uu____10074,l,uu____10076,uu____10077);
              FStar_Syntax_Syntax.sigrng = uu____10078;
              FStar_Syntax_Syntax.sigquals = uu____10079;
              FStar_Syntax_Syntax.sigmeta = uu____10080;
              FStar_Syntax_Syntax.sigattrs = uu____10081;_},uu____10082),uu____10083)
          -> l
      | uu____10138 ->
          let uu____10159 =
            let uu____10160 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10160 in
          failwith uu____10159
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
        let uu____10197 = lookup_qname env lid in
        match uu____10197 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10225)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10276,lbs),uu____10278)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10306 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10306
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10338 -> FStar_Pervasives_Native.None)
        | uu____10343 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10380 = lookup_qname env ftv in
      match uu____10380 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10404) ->
          let uu____10449 = effect_signature se in
          (match uu____10449 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10470,t),r) ->
               let uu____10485 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10485)
      | uu____10486 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10515 = try_lookup_effect_lid env ftv in
      match uu____10515 with
      | FStar_Pervasives_Native.None  ->
          let uu____10518 =
            let uu____10519 =
              let uu____10524 = name_not_found ftv in
              (uu____10524, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10519 in
          FStar_Exn.raise uu____10518
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
        let uu____10544 = lookup_qname env lid0 in
        match uu____10544 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10575);
                FStar_Syntax_Syntax.sigrng = uu____10576;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10578;
                FStar_Syntax_Syntax.sigattrs = uu____10579;_},FStar_Pervasives_Native.None
              ),uu____10580)
            ->
            let lid1 =
              let uu____10634 =
                let uu____10635 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10635 in
              FStar_Ident.set_lid_range lid uu____10634 in
            let uu____10636 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___145_10640  ->
                      match uu___145_10640 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10641 -> false)) in
            if uu____10636
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10655 =
                      let uu____10656 =
                        let uu____10657 = get_range env in
                        FStar_Range.string_of_range uu____10657 in
                      let uu____10658 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10659 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10656 uu____10658 uu____10659 in
                    failwith uu____10655) in
               match (binders, univs1) with
               | ([],uu____10666) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10683,uu____10684::uu____10685::uu____10686) ->
                   let uu____10691 =
                     let uu____10692 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10693 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10692 uu____10693 in
                   failwith uu____10691
               | uu____10700 ->
                   let uu____10705 =
                     let uu____10710 =
                       let uu____10711 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10711) in
                     inst_tscheme_with uu____10710 insts in
                   (match uu____10705 with
                    | (uu____10722,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10725 =
                          let uu____10726 = FStar_Syntax_Subst.compress t1 in
                          uu____10726.FStar_Syntax_Syntax.n in
                        (match uu____10725 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10773 -> failwith "Impossible")))
        | uu____10780 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10822 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10822 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10835,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10842 = find1 l2 in
            (match uu____10842 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10849 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10849 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10853 = find1 l in
            (match uu____10853 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10869 = lookup_qname env l1 in
      match uu____10869 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10892;
              FStar_Syntax_Syntax.sigrng = uu____10893;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10895;
              FStar_Syntax_Syntax.sigattrs = uu____10896;_},uu____10897),uu____10898)
          -> q
      | uu____10949 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10985 =
          let uu____10986 =
            let uu____10987 = FStar_Util.string_of_int i in
            let uu____10988 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10987 uu____10988 in
          failwith uu____10986 in
        let uu____10989 = lookup_datacon env lid in
        match uu____10989 with
        | (uu____10994,t) ->
            let uu____10996 =
              let uu____10997 = FStar_Syntax_Subst.compress t in
              uu____10997.FStar_Syntax_Syntax.n in
            (match uu____10996 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11001) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____11032 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____11032
                      FStar_Pervasives_Native.fst)
             | uu____11041 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11050 = lookup_qname env l in
      match uu____11050 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11071,uu____11072,uu____11073);
              FStar_Syntax_Syntax.sigrng = uu____11074;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11076;
              FStar_Syntax_Syntax.sigattrs = uu____11077;_},uu____11078),uu____11079)
          ->
          FStar_Util.for_some
            (fun uu___146_11132  ->
               match uu___146_11132 with
               | FStar_Syntax_Syntax.Projector uu____11133 -> true
               | uu____11138 -> false) quals
      | uu____11139 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11168 = lookup_qname env lid in
      match uu____11168 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11189,uu____11190,uu____11191,uu____11192,uu____11193,uu____11194);
              FStar_Syntax_Syntax.sigrng = uu____11195;
              FStar_Syntax_Syntax.sigquals = uu____11196;
              FStar_Syntax_Syntax.sigmeta = uu____11197;
              FStar_Syntax_Syntax.sigattrs = uu____11198;_},uu____11199),uu____11200)
          -> true
      | uu____11255 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11284 = lookup_qname env lid in
      match uu____11284 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11305,uu____11306,uu____11307,uu____11308,uu____11309,uu____11310);
              FStar_Syntax_Syntax.sigrng = uu____11311;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11313;
              FStar_Syntax_Syntax.sigattrs = uu____11314;_},uu____11315),uu____11316)
          ->
          FStar_Util.for_some
            (fun uu___147_11377  ->
               match uu___147_11377 with
               | FStar_Syntax_Syntax.RecordType uu____11378 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11387 -> true
               | uu____11396 -> false) quals
      | uu____11397 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11426 = lookup_qname env lid in
      match uu____11426 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11447,uu____11448);
              FStar_Syntax_Syntax.sigrng = uu____11449;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11451;
              FStar_Syntax_Syntax.sigattrs = uu____11452;_},uu____11453),uu____11454)
          ->
          FStar_Util.for_some
            (fun uu___148_11511  ->
               match uu___148_11511 with
               | FStar_Syntax_Syntax.Action uu____11512 -> true
               | uu____11513 -> false) quals
      | uu____11514 -> false
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
      let uu____11546 =
        let uu____11547 = FStar_Syntax_Util.un_uinst head1 in
        uu____11547.FStar_Syntax_Syntax.n in
      match uu____11546 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11551 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11618 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11634) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11651 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11658 ->
                 FStar_Pervasives_Native.Some true
             | uu____11675 -> FStar_Pervasives_Native.Some false) in
      let uu____11676 =
        let uu____11679 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11679 mapper in
      match uu____11676 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11727 = lookup_qname env lid in
      match uu____11727 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11748,uu____11749,tps,uu____11751,uu____11752,uu____11753);
              FStar_Syntax_Syntax.sigrng = uu____11754;
              FStar_Syntax_Syntax.sigquals = uu____11755;
              FStar_Syntax_Syntax.sigmeta = uu____11756;
              FStar_Syntax_Syntax.sigattrs = uu____11757;_},uu____11758),uu____11759)
          -> FStar_List.length tps
      | uu____11822 ->
          let uu____11843 =
            let uu____11844 =
              let uu____11849 = name_not_found lid in
              (uu____11849, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11844 in
          FStar_Exn.raise uu____11843
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
           (fun uu____11891  ->
              match uu____11891 with
              | (d,uu____11899) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11912 = effect_decl_opt env l in
      match uu____11912 with
      | FStar_Pervasives_Native.None  ->
          let uu____11927 =
            let uu____11928 =
              let uu____11933 = name_not_found l in
              (uu____11933, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11928 in
          FStar_Exn.raise uu____11927
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
            (let uu____11999 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____12052  ->
                       match uu____12052 with
                       | (m1,m2,uu____12065,uu____12066,uu____12067) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11999 with
             | FStar_Pervasives_Native.None  ->
                 let uu____12084 =
                   let uu____12085 =
                     let uu____12090 =
                       let uu____12091 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____12092 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____12091
                         uu____12092 in
                     (uu____12090, (env.range)) in
                   FStar_Errors.Error uu____12085 in
                 FStar_Exn.raise uu____12084
             | FStar_Pervasives_Native.Some
                 (uu____12099,uu____12100,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____12143 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12143)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12170 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12196  ->
                match uu____12196 with
                | (d,uu____12202) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12170 with
      | FStar_Pervasives_Native.None  ->
          let uu____12213 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12213
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12226 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12226 with
           | (uu____12237,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12247)::(wp,uu____12249)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12285 -> failwith "Impossible"))
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
                 let uu____12334 = get_range env in
                 let uu____12335 =
                   let uu____12338 =
                     let uu____12339 =
                       let uu____12354 =
                         let uu____12357 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12357] in
                       (null_wp, uu____12354) in
                     FStar_Syntax_Syntax.Tm_app uu____12339 in
                   FStar_Syntax_Syntax.mk uu____12338 in
                 uu____12335 FStar_Pervasives_Native.None uu____12334 in
               let uu____12363 =
                 let uu____12364 =
                   let uu____12373 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12373] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12364;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12363)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___164_12384 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___164_12384.order);
              joins = (uu___164_12384.joins)
            } in
          let uu___165_12393 = env in
          {
            solver = (uu___165_12393.solver);
            range = (uu___165_12393.range);
            curmodule = (uu___165_12393.curmodule);
            gamma = (uu___165_12393.gamma);
            gamma_cache = (uu___165_12393.gamma_cache);
            modules = (uu___165_12393.modules);
            expected_typ = (uu___165_12393.expected_typ);
            sigtab = (uu___165_12393.sigtab);
            is_pattern = (uu___165_12393.is_pattern);
            instantiate_imp = (uu___165_12393.instantiate_imp);
            effects;
            generalize = (uu___165_12393.generalize);
            letrecs = (uu___165_12393.letrecs);
            top_level = (uu___165_12393.top_level);
            check_uvars = (uu___165_12393.check_uvars);
            use_eq = (uu___165_12393.use_eq);
            is_iface = (uu___165_12393.is_iface);
            admit = (uu___165_12393.admit);
            lax = (uu___165_12393.lax);
            lax_universes = (uu___165_12393.lax_universes);
            failhard = (uu___165_12393.failhard);
            nosynth = (uu___165_12393.nosynth);
            tc_term = (uu___165_12393.tc_term);
            type_of = (uu___165_12393.type_of);
            universe_of = (uu___165_12393.universe_of);
            use_bv_sorts = (uu___165_12393.use_bv_sorts);
            qname_and_index = (uu___165_12393.qname_and_index);
            proof_ns = (uu___165_12393.proof_ns);
            synth = (uu___165_12393.synth);
            is_native_tactic = (uu___165_12393.is_native_tactic);
            identifier_info = (uu___165_12393.identifier_info);
            tc_hooks = (uu___165_12393.tc_hooks);
            dsenv = (uu___165_12393.dsenv);
            dep_graph = (uu___165_12393.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12410 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12410 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12500 = (e1.mlift).mlift_wp t wp in
                              let uu____12501 = l1 t wp e in
                              l2 t uu____12500 uu____12501))
                | uu____12502 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12541 = inst_tscheme lift_t in
            match uu____12541 with
            | (uu____12548,lift_t1) ->
                let uu____12550 =
                  let uu____12553 =
                    let uu____12554 =
                      let uu____12569 =
                        let uu____12572 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12573 =
                          let uu____12576 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12576] in
                        uu____12572 :: uu____12573 in
                      (lift_t1, uu____12569) in
                    FStar_Syntax_Syntax.Tm_app uu____12554 in
                  FStar_Syntax_Syntax.mk uu____12553 in
                uu____12550 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12617 = inst_tscheme lift_t in
            match uu____12617 with
            | (uu____12624,lift_t1) ->
                let uu____12626 =
                  let uu____12629 =
                    let uu____12630 =
                      let uu____12645 =
                        let uu____12648 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12649 =
                          let uu____12652 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12653 =
                            let uu____12656 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12656] in
                          uu____12652 :: uu____12653 in
                        uu____12648 :: uu____12649 in
                      (lift_t1, uu____12645) in
                    FStar_Syntax_Syntax.Tm_app uu____12630 in
                  FStar_Syntax_Syntax.mk uu____12629 in
                uu____12626 FStar_Pervasives_Native.None
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
              let uu____12694 =
                let uu____12695 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12695
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12694 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12699 =
              let uu____12700 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12700 in
            let uu____12701 =
              let uu____12702 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12720 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12720) in
              FStar_Util.dflt "none" uu____12702 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12699
              uu____12701 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12746  ->
                    match uu____12746 with
                    | (e,uu____12754) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12773 =
            match uu____12773 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____12811 =
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
                                    (let uu____12832 =
                                       let uu____12841 =
                                         find_edge order1 (i, k) in
                                       let uu____12844 =
                                         find_edge order1 (k, j) in
                                       (uu____12841, uu____12844) in
                                     match uu____12832 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12859 =
                                           compose_edges e1 e2 in
                                         [uu____12859]
                                     | uu____12860 -> []))))) in
              FStar_List.append order1 uu____12811 in
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
                   let uu____12889 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12891 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12891
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12889
                   then
                     let uu____12896 =
                       let uu____12897 =
                         let uu____12902 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12903 = get_range env in
                         (uu____12902, uu____12903) in
                       FStar_Errors.Error uu____12897 in
                     FStar_Exn.raise uu____12896
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
                                            let uu____13028 =
                                              let uu____13037 =
                                                find_edge order2 (i, k) in
                                              let uu____13040 =
                                                find_edge order2 (j, k) in
                                              (uu____13037, uu____13040) in
                                            match uu____13028 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13082,uu____13083)
                                                     ->
                                                     let uu____13090 =
                                                       let uu____13095 =
                                                         let uu____13096 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____13096 in
                                                       let uu____13099 =
                                                         let uu____13100 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____13100 in
                                                       (uu____13095,
                                                         uu____13099) in
                                                     (match uu____13090 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate\n";
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
                                            | uu____13135 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___166_13208 = env.effects in
              { decls = (uu___166_13208.decls); order = order2; joins } in
            let uu___167_13209 = env in
            {
              solver = (uu___167_13209.solver);
              range = (uu___167_13209.range);
              curmodule = (uu___167_13209.curmodule);
              gamma = (uu___167_13209.gamma);
              gamma_cache = (uu___167_13209.gamma_cache);
              modules = (uu___167_13209.modules);
              expected_typ = (uu___167_13209.expected_typ);
              sigtab = (uu___167_13209.sigtab);
              is_pattern = (uu___167_13209.is_pattern);
              instantiate_imp = (uu___167_13209.instantiate_imp);
              effects;
              generalize = (uu___167_13209.generalize);
              letrecs = (uu___167_13209.letrecs);
              top_level = (uu___167_13209.top_level);
              check_uvars = (uu___167_13209.check_uvars);
              use_eq = (uu___167_13209.use_eq);
              is_iface = (uu___167_13209.is_iface);
              admit = (uu___167_13209.admit);
              lax = (uu___167_13209.lax);
              lax_universes = (uu___167_13209.lax_universes);
              failhard = (uu___167_13209.failhard);
              nosynth = (uu___167_13209.nosynth);
              tc_term = (uu___167_13209.tc_term);
              type_of = (uu___167_13209.type_of);
              universe_of = (uu___167_13209.universe_of);
              use_bv_sorts = (uu___167_13209.use_bv_sorts);
              qname_and_index = (uu___167_13209.qname_and_index);
              proof_ns = (uu___167_13209.proof_ns);
              synth = (uu___167_13209.synth);
              is_native_tactic = (uu___167_13209.is_native_tactic);
              identifier_info = (uu___167_13209.identifier_info);
              tc_hooks = (uu___167_13209.tc_hooks);
              dsenv = (uu___167_13209.dsenv);
              dep_graph = (uu___167_13209.dep_graph)
            }))
      | uu____13210 -> env
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
        | uu____13236 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13246 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13246 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13263 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13263 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13281 =
                     let uu____13282 =
                       let uu____13287 =
                         let uu____13288 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13293 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13300 =
                           let uu____13301 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13301 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13288 uu____13293 uu____13300 in
                       (uu____13287, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13282 in
                   FStar_Exn.raise uu____13281)
                else ();
                (let inst1 =
                   let uu____13306 =
                     let uu____13315 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13315 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13332  ->
                        fun uu____13333  ->
                          match (uu____13332, uu____13333) with
                          | ((x,uu____13355),(t,uu____13357)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13306 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13376 =
                     let uu___168_13377 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___168_13377.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___168_13377.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___168_13377.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___168_13377.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13376
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
          let uu____13403 = effect_decl_opt env effect_name in
          match uu____13403 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13436 =
                only_reifiable &&
                  (let uu____13438 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13438) in
              if uu____13436
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13454 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13473 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13502 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13502
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13503 =
                             let uu____13504 =
                               let uu____13509 = get_range env in
                               (message, uu____13509) in
                             FStar_Errors.Error uu____13504 in
                           FStar_Exn.raise uu____13503 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13519 =
                       let uu____13522 = get_range env in
                       let uu____13523 =
                         let uu____13526 =
                           let uu____13527 =
                             let uu____13542 =
                               let uu____13545 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13545; wp] in
                             (repr, uu____13542) in
                           FStar_Syntax_Syntax.Tm_app uu____13527 in
                         FStar_Syntax_Syntax.mk uu____13526 in
                       uu____13523 FStar_Pervasives_Native.None uu____13522 in
                     FStar_Pervasives_Native.Some uu____13519)
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
          let uu____13597 =
            let uu____13598 =
              let uu____13603 =
                let uu____13604 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13604 in
              let uu____13605 = get_range env in (uu____13603, uu____13605) in
            FStar_Errors.Error uu____13598 in
          FStar_Exn.raise uu____13597 in
        let uu____13606 = effect_repr_aux true env c u_c in
        match uu____13606 with
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
      | uu____13646 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13655 =
        let uu____13656 = FStar_Syntax_Subst.compress t in
        uu____13656.FStar_Syntax_Syntax.n in
      match uu____13655 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13659,c) ->
          is_reifiable_comp env c
      | uu____13677 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13701)::uu____13702 -> x :: rest
        | (Binding_sig_inst uu____13711)::uu____13712 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13727 = push1 x rest1 in local :: uu____13727 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___169_13731 = env in
       let uu____13732 = push1 s env.gamma in
       {
         solver = (uu___169_13731.solver);
         range = (uu___169_13731.range);
         curmodule = (uu___169_13731.curmodule);
         gamma = uu____13732;
         gamma_cache = (uu___169_13731.gamma_cache);
         modules = (uu___169_13731.modules);
         expected_typ = (uu___169_13731.expected_typ);
         sigtab = (uu___169_13731.sigtab);
         is_pattern = (uu___169_13731.is_pattern);
         instantiate_imp = (uu___169_13731.instantiate_imp);
         effects = (uu___169_13731.effects);
         generalize = (uu___169_13731.generalize);
         letrecs = (uu___169_13731.letrecs);
         top_level = (uu___169_13731.top_level);
         check_uvars = (uu___169_13731.check_uvars);
         use_eq = (uu___169_13731.use_eq);
         is_iface = (uu___169_13731.is_iface);
         admit = (uu___169_13731.admit);
         lax = (uu___169_13731.lax);
         lax_universes = (uu___169_13731.lax_universes);
         failhard = (uu___169_13731.failhard);
         nosynth = (uu___169_13731.nosynth);
         tc_term = (uu___169_13731.tc_term);
         type_of = (uu___169_13731.type_of);
         universe_of = (uu___169_13731.universe_of);
         use_bv_sorts = (uu___169_13731.use_bv_sorts);
         qname_and_index = (uu___169_13731.qname_and_index);
         proof_ns = (uu___169_13731.proof_ns);
         synth = (uu___169_13731.synth);
         is_native_tactic = (uu___169_13731.is_native_tactic);
         identifier_info = (uu___169_13731.identifier_info);
         tc_hooks = (uu___169_13731.tc_hooks);
         dsenv = (uu___169_13731.dsenv);
         dep_graph = (uu___169_13731.dep_graph)
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
      let uu___170_13769 = env in
      {
        solver = (uu___170_13769.solver);
        range = (uu___170_13769.range);
        curmodule = (uu___170_13769.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___170_13769.gamma_cache);
        modules = (uu___170_13769.modules);
        expected_typ = (uu___170_13769.expected_typ);
        sigtab = (uu___170_13769.sigtab);
        is_pattern = (uu___170_13769.is_pattern);
        instantiate_imp = (uu___170_13769.instantiate_imp);
        effects = (uu___170_13769.effects);
        generalize = (uu___170_13769.generalize);
        letrecs = (uu___170_13769.letrecs);
        top_level = (uu___170_13769.top_level);
        check_uvars = (uu___170_13769.check_uvars);
        use_eq = (uu___170_13769.use_eq);
        is_iface = (uu___170_13769.is_iface);
        admit = (uu___170_13769.admit);
        lax = (uu___170_13769.lax);
        lax_universes = (uu___170_13769.lax_universes);
        failhard = (uu___170_13769.failhard);
        nosynth = (uu___170_13769.nosynth);
        tc_term = (uu___170_13769.tc_term);
        type_of = (uu___170_13769.type_of);
        universe_of = (uu___170_13769.universe_of);
        use_bv_sorts = (uu___170_13769.use_bv_sorts);
        qname_and_index = (uu___170_13769.qname_and_index);
        proof_ns = (uu___170_13769.proof_ns);
        synth = (uu___170_13769.synth);
        is_native_tactic = (uu___170_13769.is_native_tactic);
        identifier_info = (uu___170_13769.identifier_info);
        tc_hooks = (uu___170_13769.tc_hooks);
        dsenv = (uu___170_13769.dsenv);
        dep_graph = (uu___170_13769.dep_graph)
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
            (let uu___171_13803 = env in
             {
               solver = (uu___171_13803.solver);
               range = (uu___171_13803.range);
               curmodule = (uu___171_13803.curmodule);
               gamma = rest;
               gamma_cache = (uu___171_13803.gamma_cache);
               modules = (uu___171_13803.modules);
               expected_typ = (uu___171_13803.expected_typ);
               sigtab = (uu___171_13803.sigtab);
               is_pattern = (uu___171_13803.is_pattern);
               instantiate_imp = (uu___171_13803.instantiate_imp);
               effects = (uu___171_13803.effects);
               generalize = (uu___171_13803.generalize);
               letrecs = (uu___171_13803.letrecs);
               top_level = (uu___171_13803.top_level);
               check_uvars = (uu___171_13803.check_uvars);
               use_eq = (uu___171_13803.use_eq);
               is_iface = (uu___171_13803.is_iface);
               admit = (uu___171_13803.admit);
               lax = (uu___171_13803.lax);
               lax_universes = (uu___171_13803.lax_universes);
               failhard = (uu___171_13803.failhard);
               nosynth = (uu___171_13803.nosynth);
               tc_term = (uu___171_13803.tc_term);
               type_of = (uu___171_13803.type_of);
               universe_of = (uu___171_13803.universe_of);
               use_bv_sorts = (uu___171_13803.use_bv_sorts);
               qname_and_index = (uu___171_13803.qname_and_index);
               proof_ns = (uu___171_13803.proof_ns);
               synth = (uu___171_13803.synth);
               is_native_tactic = (uu___171_13803.is_native_tactic);
               identifier_info = (uu___171_13803.identifier_info);
               tc_hooks = (uu___171_13803.tc_hooks);
               dsenv = (uu___171_13803.dsenv);
               dep_graph = (uu___171_13803.dep_graph)
             }))
    | uu____13804 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13828  ->
             match uu____13828 with | (x,uu____13834) -> push_bv env1 x) env
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
            let uu___172_13864 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___172_13864.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___172_13864.FStar_Syntax_Syntax.index);
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
      (let uu___173_13899 = env in
       {
         solver = (uu___173_13899.solver);
         range = (uu___173_13899.range);
         curmodule = (uu___173_13899.curmodule);
         gamma = [];
         gamma_cache = (uu___173_13899.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___173_13899.sigtab);
         is_pattern = (uu___173_13899.is_pattern);
         instantiate_imp = (uu___173_13899.instantiate_imp);
         effects = (uu___173_13899.effects);
         generalize = (uu___173_13899.generalize);
         letrecs = (uu___173_13899.letrecs);
         top_level = (uu___173_13899.top_level);
         check_uvars = (uu___173_13899.check_uvars);
         use_eq = (uu___173_13899.use_eq);
         is_iface = (uu___173_13899.is_iface);
         admit = (uu___173_13899.admit);
         lax = (uu___173_13899.lax);
         lax_universes = (uu___173_13899.lax_universes);
         failhard = (uu___173_13899.failhard);
         nosynth = (uu___173_13899.nosynth);
         tc_term = (uu___173_13899.tc_term);
         type_of = (uu___173_13899.type_of);
         universe_of = (uu___173_13899.universe_of);
         use_bv_sorts = (uu___173_13899.use_bv_sorts);
         qname_and_index = (uu___173_13899.qname_and_index);
         proof_ns = (uu___173_13899.proof_ns);
         synth = (uu___173_13899.synth);
         is_native_tactic = (uu___173_13899.is_native_tactic);
         identifier_info = (uu___173_13899.identifier_info);
         tc_hooks = (uu___173_13899.tc_hooks);
         dsenv = (uu___173_13899.dsenv);
         dep_graph = (uu___173_13899.dep_graph)
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
        let uu____13936 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13936 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13964 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13964)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___174_13979 = env in
      {
        solver = (uu___174_13979.solver);
        range = (uu___174_13979.range);
        curmodule = (uu___174_13979.curmodule);
        gamma = (uu___174_13979.gamma);
        gamma_cache = (uu___174_13979.gamma_cache);
        modules = (uu___174_13979.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___174_13979.sigtab);
        is_pattern = (uu___174_13979.is_pattern);
        instantiate_imp = (uu___174_13979.instantiate_imp);
        effects = (uu___174_13979.effects);
        generalize = (uu___174_13979.generalize);
        letrecs = (uu___174_13979.letrecs);
        top_level = (uu___174_13979.top_level);
        check_uvars = (uu___174_13979.check_uvars);
        use_eq = false;
        is_iface = (uu___174_13979.is_iface);
        admit = (uu___174_13979.admit);
        lax = (uu___174_13979.lax);
        lax_universes = (uu___174_13979.lax_universes);
        failhard = (uu___174_13979.failhard);
        nosynth = (uu___174_13979.nosynth);
        tc_term = (uu___174_13979.tc_term);
        type_of = (uu___174_13979.type_of);
        universe_of = (uu___174_13979.universe_of);
        use_bv_sorts = (uu___174_13979.use_bv_sorts);
        qname_and_index = (uu___174_13979.qname_and_index);
        proof_ns = (uu___174_13979.proof_ns);
        synth = (uu___174_13979.synth);
        is_native_tactic = (uu___174_13979.is_native_tactic);
        identifier_info = (uu___174_13979.identifier_info);
        tc_hooks = (uu___174_13979.tc_hooks);
        dsenv = (uu___174_13979.dsenv);
        dep_graph = (uu___174_13979.dep_graph)
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
    let uu____14005 = expected_typ env_ in
    ((let uu___175_14011 = env_ in
      {
        solver = (uu___175_14011.solver);
        range = (uu___175_14011.range);
        curmodule = (uu___175_14011.curmodule);
        gamma = (uu___175_14011.gamma);
        gamma_cache = (uu___175_14011.gamma_cache);
        modules = (uu___175_14011.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___175_14011.sigtab);
        is_pattern = (uu___175_14011.is_pattern);
        instantiate_imp = (uu___175_14011.instantiate_imp);
        effects = (uu___175_14011.effects);
        generalize = (uu___175_14011.generalize);
        letrecs = (uu___175_14011.letrecs);
        top_level = (uu___175_14011.top_level);
        check_uvars = (uu___175_14011.check_uvars);
        use_eq = false;
        is_iface = (uu___175_14011.is_iface);
        admit = (uu___175_14011.admit);
        lax = (uu___175_14011.lax);
        lax_universes = (uu___175_14011.lax_universes);
        failhard = (uu___175_14011.failhard);
        nosynth = (uu___175_14011.nosynth);
        tc_term = (uu___175_14011.tc_term);
        type_of = (uu___175_14011.type_of);
        universe_of = (uu___175_14011.universe_of);
        use_bv_sorts = (uu___175_14011.use_bv_sorts);
        qname_and_index = (uu___175_14011.qname_and_index);
        proof_ns = (uu___175_14011.proof_ns);
        synth = (uu___175_14011.synth);
        is_native_tactic = (uu___175_14011.is_native_tactic);
        identifier_info = (uu___175_14011.identifier_info);
        tc_hooks = (uu___175_14011.tc_hooks);
        dsenv = (uu___175_14011.dsenv);
        dep_graph = (uu___175_14011.dep_graph)
      }), uu____14005)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____14026 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___149_14036  ->
                    match uu___149_14036 with
                    | Binding_sig (uu____14039,se) -> [se]
                    | uu____14045 -> [])) in
          FStar_All.pipe_right uu____14026 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___176_14052 = env in
       {
         solver = (uu___176_14052.solver);
         range = (uu___176_14052.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___176_14052.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___176_14052.expected_typ);
         sigtab = (uu___176_14052.sigtab);
         is_pattern = (uu___176_14052.is_pattern);
         instantiate_imp = (uu___176_14052.instantiate_imp);
         effects = (uu___176_14052.effects);
         generalize = (uu___176_14052.generalize);
         letrecs = (uu___176_14052.letrecs);
         top_level = (uu___176_14052.top_level);
         check_uvars = (uu___176_14052.check_uvars);
         use_eq = (uu___176_14052.use_eq);
         is_iface = (uu___176_14052.is_iface);
         admit = (uu___176_14052.admit);
         lax = (uu___176_14052.lax);
         lax_universes = (uu___176_14052.lax_universes);
         failhard = (uu___176_14052.failhard);
         nosynth = (uu___176_14052.nosynth);
         tc_term = (uu___176_14052.tc_term);
         type_of = (uu___176_14052.type_of);
         universe_of = (uu___176_14052.universe_of);
         use_bv_sorts = (uu___176_14052.use_bv_sorts);
         qname_and_index = (uu___176_14052.qname_and_index);
         proof_ns = (uu___176_14052.proof_ns);
         synth = (uu___176_14052.synth);
         is_native_tactic = (uu___176_14052.is_native_tactic);
         identifier_info = (uu___176_14052.identifier_info);
         tc_hooks = (uu___176_14052.tc_hooks);
         dsenv = (uu___176_14052.dsenv);
         dep_graph = (uu___176_14052.dep_graph)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14134)::tl1 -> aux out tl1
      | (Binding_lid (uu____14138,(uu____14139,t)))::tl1 ->
          let uu____14154 =
            let uu____14161 = FStar_Syntax_Free.uvars t in
            ext out uu____14161 in
          aux uu____14154 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14168;
            FStar_Syntax_Syntax.index = uu____14169;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14176 =
            let uu____14183 = FStar_Syntax_Free.uvars t in
            ext out uu____14183 in
          aux uu____14176 tl1
      | (Binding_sig uu____14190)::uu____14191 -> out
      | (Binding_sig_inst uu____14200)::uu____14201 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14257)::tl1 -> aux out tl1
      | (Binding_univ uu____14269)::tl1 -> aux out tl1
      | (Binding_lid (uu____14273,(uu____14274,t)))::tl1 ->
          let uu____14289 =
            let uu____14292 = FStar_Syntax_Free.univs t in
            ext out uu____14292 in
          aux uu____14289 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14295;
            FStar_Syntax_Syntax.index = uu____14296;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14303 =
            let uu____14306 = FStar_Syntax_Free.univs t in
            ext out uu____14306 in
          aux uu____14303 tl1
      | (Binding_sig uu____14309)::uu____14310 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14364)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14380 = FStar_Util.fifo_set_add uname out in
          aux uu____14380 tl1
      | (Binding_lid (uu____14383,(uu____14384,t)))::tl1 ->
          let uu____14399 =
            let uu____14402 = FStar_Syntax_Free.univnames t in
            ext out uu____14402 in
          aux uu____14399 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14405;
            FStar_Syntax_Syntax.index = uu____14406;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14413 =
            let uu____14416 = FStar_Syntax_Free.univnames t in
            ext out uu____14416 in
          aux uu____14413 tl1
      | (Binding_sig uu____14419)::uu____14420 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___150_14445  ->
            match uu___150_14445 with
            | Binding_var x -> [x]
            | Binding_lid uu____14449 -> []
            | Binding_sig uu____14454 -> []
            | Binding_univ uu____14461 -> []
            | Binding_sig_inst uu____14462 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14479 =
      let uu____14482 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14482
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14479 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14507 =
      let uu____14508 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___151_14518  ->
                match uu___151_14518 with
                | Binding_var x ->
                    let uu____14520 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14520
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14523) ->
                    let uu____14524 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14524
                | Binding_sig (ls,uu____14526) ->
                    let uu____14531 =
                      let uu____14532 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14532
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14531
                | Binding_sig_inst (ls,uu____14542,uu____14543) ->
                    let uu____14548 =
                      let uu____14549 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14549
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14548)) in
      FStar_All.pipe_right uu____14508 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14507 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14568 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14568
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14596  ->
                 fun uu____14597  ->
                   match (uu____14596, uu____14597) with
                   | ((b1,uu____14615),(b2,uu____14617)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___152_14664  ->
    match uu___152_14664 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14665 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___153_14684  ->
             match uu___153_14684 with
             | Binding_sig (lids,uu____14690) -> FStar_List.append lids keys
             | uu____14695 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14701  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14737) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14756,uu____14757) -> false in
      let uu____14766 =
        FStar_List.tryFind
          (fun uu____14784  ->
             match uu____14784 with | (p,uu____14792) -> list_prefix p path)
          env.proof_ns in
      match uu____14766 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14803,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14823 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14823
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___177_14838 = e in
        {
          solver = (uu___177_14838.solver);
          range = (uu___177_14838.range);
          curmodule = (uu___177_14838.curmodule);
          gamma = (uu___177_14838.gamma);
          gamma_cache = (uu___177_14838.gamma_cache);
          modules = (uu___177_14838.modules);
          expected_typ = (uu___177_14838.expected_typ);
          sigtab = (uu___177_14838.sigtab);
          is_pattern = (uu___177_14838.is_pattern);
          instantiate_imp = (uu___177_14838.instantiate_imp);
          effects = (uu___177_14838.effects);
          generalize = (uu___177_14838.generalize);
          letrecs = (uu___177_14838.letrecs);
          top_level = (uu___177_14838.top_level);
          check_uvars = (uu___177_14838.check_uvars);
          use_eq = (uu___177_14838.use_eq);
          is_iface = (uu___177_14838.is_iface);
          admit = (uu___177_14838.admit);
          lax = (uu___177_14838.lax);
          lax_universes = (uu___177_14838.lax_universes);
          failhard = (uu___177_14838.failhard);
          nosynth = (uu___177_14838.nosynth);
          tc_term = (uu___177_14838.tc_term);
          type_of = (uu___177_14838.type_of);
          universe_of = (uu___177_14838.universe_of);
          use_bv_sorts = (uu___177_14838.use_bv_sorts);
          qname_and_index = (uu___177_14838.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___177_14838.synth);
          is_native_tactic = (uu___177_14838.is_native_tactic);
          identifier_info = (uu___177_14838.identifier_info);
          tc_hooks = (uu___177_14838.tc_hooks);
          dsenv = (uu___177_14838.dsenv);
          dep_graph = (uu___177_14838.dep_graph)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___178_14871 = e in
      {
        solver = (uu___178_14871.solver);
        range = (uu___178_14871.range);
        curmodule = (uu___178_14871.curmodule);
        gamma = (uu___178_14871.gamma);
        gamma_cache = (uu___178_14871.gamma_cache);
        modules = (uu___178_14871.modules);
        expected_typ = (uu___178_14871.expected_typ);
        sigtab = (uu___178_14871.sigtab);
        is_pattern = (uu___178_14871.is_pattern);
        instantiate_imp = (uu___178_14871.instantiate_imp);
        effects = (uu___178_14871.effects);
        generalize = (uu___178_14871.generalize);
        letrecs = (uu___178_14871.letrecs);
        top_level = (uu___178_14871.top_level);
        check_uvars = (uu___178_14871.check_uvars);
        use_eq = (uu___178_14871.use_eq);
        is_iface = (uu___178_14871.is_iface);
        admit = (uu___178_14871.admit);
        lax = (uu___178_14871.lax);
        lax_universes = (uu___178_14871.lax_universes);
        failhard = (uu___178_14871.failhard);
        nosynth = (uu___178_14871.nosynth);
        tc_term = (uu___178_14871.tc_term);
        type_of = (uu___178_14871.type_of);
        universe_of = (uu___178_14871.universe_of);
        use_bv_sorts = (uu___178_14871.use_bv_sorts);
        qname_and_index = (uu___178_14871.qname_and_index);
        proof_ns = ns;
        synth = (uu___178_14871.synth);
        is_native_tactic = (uu___178_14871.is_native_tactic);
        identifier_info = (uu___178_14871.identifier_info);
        tc_hooks = (uu___178_14871.tc_hooks);
        dsenv = (uu___178_14871.dsenv);
        dep_graph = (uu___178_14871.dep_graph)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14884 = FStar_Syntax_Free.names t in
      let uu____14887 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14884 uu____14887
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14906 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14906
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14913 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14913
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14929 =
      match uu____14929 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14945 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14945) in
    let uu____14947 =
      let uu____14950 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14950 FStar_List.rev in
    FStar_All.pipe_right uu____14947 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14967  -> ());
    push = (fun uu____14969  -> ());
    pop = (fun uu____14971  -> ());
    encode_modul = (fun uu____14974  -> fun uu____14975  -> ());
    encode_sig = (fun uu____14978  -> fun uu____14979  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14985 =
             let uu____14992 = FStar_Options.peek () in (e, g, uu____14992) in
           [uu____14985]);
    solve = (fun uu____15008  -> fun uu____15009  -> fun uu____15010  -> ());
    finish = (fun uu____15016  -> ());
    refresh = (fun uu____15018  -> ())
  }