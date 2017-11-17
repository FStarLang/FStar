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
    match projectee with | Binding_var _0 -> true | uu____43 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____59 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____89 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____119 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____139 -> false
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
    match projectee with | NoDelta  -> true | uu____178 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____182 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____186 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____191 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____202 -> false
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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list;
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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
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
           (fun uu___172_5035  ->
              match uu___172_5035 with
              | Binding_var x ->
                  let y =
                    let uu____5038 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____5038 in
                  let uu____5039 =
                    let uu____5040 = FStar_Syntax_Subst.compress y in
                    uu____5040.FStar_Syntax_Syntax.n in
                  (match uu____5039 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5044 =
                         let uu___186_5045 = y1 in
                         let uu____5046 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___186_5045.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___186_5045.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5046
                         } in
                       Binding_var uu____5044
                   | uu____5049 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___187_5057 = env in
      let uu____5058 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___187_5057.solver);
        range = (uu___187_5057.range);
        curmodule = (uu___187_5057.curmodule);
        gamma = uu____5058;
        gamma_cache = (uu___187_5057.gamma_cache);
        modules = (uu___187_5057.modules);
        expected_typ = (uu___187_5057.expected_typ);
        sigtab = (uu___187_5057.sigtab);
        is_pattern = (uu___187_5057.is_pattern);
        instantiate_imp = (uu___187_5057.instantiate_imp);
        effects = (uu___187_5057.effects);
        generalize = (uu___187_5057.generalize);
        letrecs = (uu___187_5057.letrecs);
        top_level = (uu___187_5057.top_level);
        check_uvars = (uu___187_5057.check_uvars);
        use_eq = (uu___187_5057.use_eq);
        is_iface = (uu___187_5057.is_iface);
        admit = (uu___187_5057.admit);
        lax = (uu___187_5057.lax);
        lax_universes = (uu___187_5057.lax_universes);
        failhard = (uu___187_5057.failhard);
        nosynth = (uu___187_5057.nosynth);
        tc_term = (uu___187_5057.tc_term);
        type_of = (uu___187_5057.type_of);
        universe_of = (uu___187_5057.universe_of);
        use_bv_sorts = (uu___187_5057.use_bv_sorts);
        qname_and_index = (uu___187_5057.qname_and_index);
        proof_ns = (uu___187_5057.proof_ns);
        synth = (uu___187_5057.synth);
        is_native_tactic = (uu___187_5057.is_native_tactic);
        identifier_info = (uu___187_5057.identifier_info);
        tc_hooks = (uu___187_5057.tc_hooks);
        dsenv = (uu___187_5057.dsenv);
        dep_graph = (uu___187_5057.dep_graph)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5065  -> fun uu____5066  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___188_5076 = env in
      {
        solver = (uu___188_5076.solver);
        range = (uu___188_5076.range);
        curmodule = (uu___188_5076.curmodule);
        gamma = (uu___188_5076.gamma);
        gamma_cache = (uu___188_5076.gamma_cache);
        modules = (uu___188_5076.modules);
        expected_typ = (uu___188_5076.expected_typ);
        sigtab = (uu___188_5076.sigtab);
        is_pattern = (uu___188_5076.is_pattern);
        instantiate_imp = (uu___188_5076.instantiate_imp);
        effects = (uu___188_5076.effects);
        generalize = (uu___188_5076.generalize);
        letrecs = (uu___188_5076.letrecs);
        top_level = (uu___188_5076.top_level);
        check_uvars = (uu___188_5076.check_uvars);
        use_eq = (uu___188_5076.use_eq);
        is_iface = (uu___188_5076.is_iface);
        admit = (uu___188_5076.admit);
        lax = (uu___188_5076.lax);
        lax_universes = (uu___188_5076.lax_universes);
        failhard = (uu___188_5076.failhard);
        nosynth = (uu___188_5076.nosynth);
        tc_term = (uu___188_5076.tc_term);
        type_of = (uu___188_5076.type_of);
        universe_of = (uu___188_5076.universe_of);
        use_bv_sorts = (uu___188_5076.use_bv_sorts);
        qname_and_index = (uu___188_5076.qname_and_index);
        proof_ns = (uu___188_5076.proof_ns);
        synth = (uu___188_5076.synth);
        is_native_tactic = (uu___188_5076.is_native_tactic);
        identifier_info = (uu___188_5076.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___188_5076.dsenv);
        dep_graph = (uu___188_5076.dep_graph)
      }
let set_dep_graph: env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___189_5083 = e in
      {
        solver = (uu___189_5083.solver);
        range = (uu___189_5083.range);
        curmodule = (uu___189_5083.curmodule);
        gamma = (uu___189_5083.gamma);
        gamma_cache = (uu___189_5083.gamma_cache);
        modules = (uu___189_5083.modules);
        expected_typ = (uu___189_5083.expected_typ);
        sigtab = (uu___189_5083.sigtab);
        is_pattern = (uu___189_5083.is_pattern);
        instantiate_imp = (uu___189_5083.instantiate_imp);
        effects = (uu___189_5083.effects);
        generalize = (uu___189_5083.generalize);
        letrecs = (uu___189_5083.letrecs);
        top_level = (uu___189_5083.top_level);
        check_uvars = (uu___189_5083.check_uvars);
        use_eq = (uu___189_5083.use_eq);
        is_iface = (uu___189_5083.is_iface);
        admit = (uu___189_5083.admit);
        lax = (uu___189_5083.lax);
        lax_universes = (uu___189_5083.lax_universes);
        failhard = (uu___189_5083.failhard);
        nosynth = (uu___189_5083.nosynth);
        tc_term = (uu___189_5083.tc_term);
        type_of = (uu___189_5083.type_of);
        universe_of = (uu___189_5083.universe_of);
        use_bv_sorts = (uu___189_5083.use_bv_sorts);
        qname_and_index = (uu___189_5083.qname_and_index);
        proof_ns = (uu___189_5083.proof_ns);
        synth = (uu___189_5083.synth);
        is_native_tactic = (uu___189_5083.is_native_tactic);
        identifier_info = (uu___189_5083.identifier_info);
        tc_hooks = (uu___189_5083.tc_hooks);
        dsenv = (uu___189_5083.dsenv);
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
      | (NoDelta ,uu____5098) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5099,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5100,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5101 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5108 . Prims.unit -> 'Auu____5108 FStar_Util.smap =
  fun uu____5114  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5117 . Prims.unit -> 'Auu____5117 FStar_Util.smap =
  fun uu____5123  -> FStar_Util.smap_create (Prims.parse_int "100")
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
              let uu____5196 = new_gamma_cache () in
              let uu____5199 = new_sigtab () in
              let uu____5202 = FStar_Options.using_facts_from () in
              let uu____5203 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty in
              let uu____5206 = FStar_ToSyntax_Env.empty_env () in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5196;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5199;
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
                proof_ns = uu____5202;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5240  -> false);
                identifier_info = uu____5203;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5206;
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
  fun uu____5308  ->
    let uu____5309 = FStar_ST.op_Bang query_indices in
    match uu____5309 with
    | [] -> failwith "Empty query indices!"
    | uu____5386 ->
        let uu____5395 =
          let uu____5404 =
            let uu____5411 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5411 in
          let uu____5488 = FStar_ST.op_Bang query_indices in uu____5404 ::
            uu____5488 in
        FStar_ST.op_Colon_Equals query_indices uu____5395
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5629  ->
    let uu____5630 = FStar_ST.op_Bang query_indices in
    match uu____5630 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5797  ->
    match uu____5797 with
    | (l,n1) ->
        let uu____5804 = FStar_ST.op_Bang query_indices in
        (match uu____5804 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5969 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5986  ->
    let uu____5987 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5987
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6081 =
       let uu____6084 = FStar_ST.op_Bang stack in env :: uu____6084 in
     FStar_ST.op_Colon_Equals stack uu____6081);
    (let uu___190_6187 = env in
     let uu____6188 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6191 = FStar_Util.smap_copy (sigtab env) in
     let uu____6194 =
       let uu____6197 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6197 in
     {
       solver = (uu___190_6187.solver);
       range = (uu___190_6187.range);
       curmodule = (uu___190_6187.curmodule);
       gamma = (uu___190_6187.gamma);
       gamma_cache = uu____6188;
       modules = (uu___190_6187.modules);
       expected_typ = (uu___190_6187.expected_typ);
       sigtab = uu____6191;
       is_pattern = (uu___190_6187.is_pattern);
       instantiate_imp = (uu___190_6187.instantiate_imp);
       effects = (uu___190_6187.effects);
       generalize = (uu___190_6187.generalize);
       letrecs = (uu___190_6187.letrecs);
       top_level = (uu___190_6187.top_level);
       check_uvars = (uu___190_6187.check_uvars);
       use_eq = (uu___190_6187.use_eq);
       is_iface = (uu___190_6187.is_iface);
       admit = (uu___190_6187.admit);
       lax = (uu___190_6187.lax);
       lax_universes = (uu___190_6187.lax_universes);
       failhard = (uu___190_6187.failhard);
       nosynth = (uu___190_6187.nosynth);
       tc_term = (uu___190_6187.tc_term);
       type_of = (uu___190_6187.type_of);
       universe_of = (uu___190_6187.universe_of);
       use_bv_sorts = (uu___190_6187.use_bv_sorts);
       qname_and_index = (uu___190_6187.qname_and_index);
       proof_ns = (uu___190_6187.proof_ns);
       synth = (uu___190_6187.synth);
       is_native_tactic = (uu___190_6187.is_native_tactic);
       identifier_info = uu____6194;
       tc_hooks = (uu___190_6187.tc_hooks);
       dsenv = (uu___190_6187.dsenv);
       dep_graph = (uu___190_6187.dep_graph)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6260  ->
    let uu____6261 = FStar_ST.op_Bang stack in
    match uu____6261 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6369 -> failwith "Impossible: Too many pops"
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
        let uu____6408 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6434  ->
                  match uu____6434 with
                  | (m,uu____6440) -> FStar_Ident.lid_equals l m)) in
        (match uu____6408 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___191_6447 = env in
               {
                 solver = (uu___191_6447.solver);
                 range = (uu___191_6447.range);
                 curmodule = (uu___191_6447.curmodule);
                 gamma = (uu___191_6447.gamma);
                 gamma_cache = (uu___191_6447.gamma_cache);
                 modules = (uu___191_6447.modules);
                 expected_typ = (uu___191_6447.expected_typ);
                 sigtab = (uu___191_6447.sigtab);
                 is_pattern = (uu___191_6447.is_pattern);
                 instantiate_imp = (uu___191_6447.instantiate_imp);
                 effects = (uu___191_6447.effects);
                 generalize = (uu___191_6447.generalize);
                 letrecs = (uu___191_6447.letrecs);
                 top_level = (uu___191_6447.top_level);
                 check_uvars = (uu___191_6447.check_uvars);
                 use_eq = (uu___191_6447.use_eq);
                 is_iface = (uu___191_6447.is_iface);
                 admit = (uu___191_6447.admit);
                 lax = (uu___191_6447.lax);
                 lax_universes = (uu___191_6447.lax_universes);
                 failhard = (uu___191_6447.failhard);
                 nosynth = (uu___191_6447.nosynth);
                 tc_term = (uu___191_6447.tc_term);
                 type_of = (uu___191_6447.type_of);
                 universe_of = (uu___191_6447.universe_of);
                 use_bv_sorts = (uu___191_6447.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___191_6447.proof_ns);
                 synth = (uu___191_6447.synth);
                 is_native_tactic = (uu___191_6447.is_native_tactic);
                 identifier_info = (uu___191_6447.identifier_info);
                 tc_hooks = (uu___191_6447.tc_hooks);
                 dsenv = (uu___191_6447.dsenv);
                 dep_graph = (uu___191_6447.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6452,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___192_6460 = env in
               {
                 solver = (uu___192_6460.solver);
                 range = (uu___192_6460.range);
                 curmodule = (uu___192_6460.curmodule);
                 gamma = (uu___192_6460.gamma);
                 gamma_cache = (uu___192_6460.gamma_cache);
                 modules = (uu___192_6460.modules);
                 expected_typ = (uu___192_6460.expected_typ);
                 sigtab = (uu___192_6460.sigtab);
                 is_pattern = (uu___192_6460.is_pattern);
                 instantiate_imp = (uu___192_6460.instantiate_imp);
                 effects = (uu___192_6460.effects);
                 generalize = (uu___192_6460.generalize);
                 letrecs = (uu___192_6460.letrecs);
                 top_level = (uu___192_6460.top_level);
                 check_uvars = (uu___192_6460.check_uvars);
                 use_eq = (uu___192_6460.use_eq);
                 is_iface = (uu___192_6460.is_iface);
                 admit = (uu___192_6460.admit);
                 lax = (uu___192_6460.lax);
                 lax_universes = (uu___192_6460.lax_universes);
                 failhard = (uu___192_6460.failhard);
                 nosynth = (uu___192_6460.nosynth);
                 tc_term = (uu___192_6460.tc_term);
                 type_of = (uu___192_6460.type_of);
                 universe_of = (uu___192_6460.universe_of);
                 use_bv_sorts = (uu___192_6460.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___192_6460.proof_ns);
                 synth = (uu___192_6460.synth);
                 is_native_tactic = (uu___192_6460.is_native_tactic);
                 identifier_info = (uu___192_6460.identifier_info);
                 tc_hooks = (uu___192_6460.tc_hooks);
                 dsenv = (uu___192_6460.dsenv);
                 dep_graph = (uu___192_6460.dep_graph)
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
        (let uu___193_6478 = e in
         {
           solver = (uu___193_6478.solver);
           range = r;
           curmodule = (uu___193_6478.curmodule);
           gamma = (uu___193_6478.gamma);
           gamma_cache = (uu___193_6478.gamma_cache);
           modules = (uu___193_6478.modules);
           expected_typ = (uu___193_6478.expected_typ);
           sigtab = (uu___193_6478.sigtab);
           is_pattern = (uu___193_6478.is_pattern);
           instantiate_imp = (uu___193_6478.instantiate_imp);
           effects = (uu___193_6478.effects);
           generalize = (uu___193_6478.generalize);
           letrecs = (uu___193_6478.letrecs);
           top_level = (uu___193_6478.top_level);
           check_uvars = (uu___193_6478.check_uvars);
           use_eq = (uu___193_6478.use_eq);
           is_iface = (uu___193_6478.is_iface);
           admit = (uu___193_6478.admit);
           lax = (uu___193_6478.lax);
           lax_universes = (uu___193_6478.lax_universes);
           failhard = (uu___193_6478.failhard);
           nosynth = (uu___193_6478.nosynth);
           tc_term = (uu___193_6478.tc_term);
           type_of = (uu___193_6478.type_of);
           universe_of = (uu___193_6478.universe_of);
           use_bv_sorts = (uu___193_6478.use_bv_sorts);
           qname_and_index = (uu___193_6478.qname_and_index);
           proof_ns = (uu___193_6478.proof_ns);
           synth = (uu___193_6478.synth);
           is_native_tactic = (uu___193_6478.is_native_tactic);
           identifier_info = (uu___193_6478.identifier_info);
           tc_hooks = (uu___193_6478.tc_hooks);
           dsenv = (uu___193_6478.dsenv);
           dep_graph = (uu___193_6478.dep_graph)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6488 =
        let uu____6489 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6489 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6488
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6591 =
          let uu____6592 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6592 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6591
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6694 =
          let uu____6695 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6695 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6694
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6799 =
        let uu____6800 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6800 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6799
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___194_6907 = env in
      {
        solver = (uu___194_6907.solver);
        range = (uu___194_6907.range);
        curmodule = lid;
        gamma = (uu___194_6907.gamma);
        gamma_cache = (uu___194_6907.gamma_cache);
        modules = (uu___194_6907.modules);
        expected_typ = (uu___194_6907.expected_typ);
        sigtab = (uu___194_6907.sigtab);
        is_pattern = (uu___194_6907.is_pattern);
        instantiate_imp = (uu___194_6907.instantiate_imp);
        effects = (uu___194_6907.effects);
        generalize = (uu___194_6907.generalize);
        letrecs = (uu___194_6907.letrecs);
        top_level = (uu___194_6907.top_level);
        check_uvars = (uu___194_6907.check_uvars);
        use_eq = (uu___194_6907.use_eq);
        is_iface = (uu___194_6907.is_iface);
        admit = (uu___194_6907.admit);
        lax = (uu___194_6907.lax);
        lax_universes = (uu___194_6907.lax_universes);
        failhard = (uu___194_6907.failhard);
        nosynth = (uu___194_6907.nosynth);
        tc_term = (uu___194_6907.tc_term);
        type_of = (uu___194_6907.type_of);
        universe_of = (uu___194_6907.universe_of);
        use_bv_sorts = (uu___194_6907.use_bv_sorts);
        qname_and_index = (uu___194_6907.qname_and_index);
        proof_ns = (uu___194_6907.proof_ns);
        synth = (uu___194_6907.synth);
        is_native_tactic = (uu___194_6907.is_native_tactic);
        identifier_info = (uu___194_6907.identifier_info);
        tc_hooks = (uu___194_6907.tc_hooks);
        dsenv = (uu___194_6907.dsenv);
        dep_graph = (uu___194_6907.dep_graph)
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
let name_not_found:
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____6933 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str in
    (FStar_Errors.NameNotFound, uu____6933)
let variable_not_found:
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____6941 =
      let uu____6942 = FStar_Syntax_Print.bv_to_string v1 in
      FStar_Util.format1 "Variable \"%s\" not found" uu____6942 in
    (FStar_Errors.VariableNotFound, uu____6941)
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6945  ->
    let uu____6946 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6946
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
      | ((formals,t),uu____6984) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____7008 = FStar_Syntax_Subst.subst vs t in (us, uu____7008)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___173_7021  ->
    match uu___173_7021 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7045  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7058 = inst_tscheme t in
      match uu____7058 with
      | (us,t1) ->
          let uu____7069 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7069)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7081  ->
          match uu____7081 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7096 =
                         let uu____7097 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7098 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7099 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7100 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7097 uu____7098 uu____7099 uu____7100 in
                       failwith uu____7096)
                    else ();
                    (let uu____7102 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7102))
               | uu____7109 ->
                   let uu____7110 =
                     let uu____7111 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7111 in
                   failwith uu____7110)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7115 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7119 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7123 -> false
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
             | ([],uu____7157) -> Maybe
             | (uu____7164,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7183 -> No in
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
          let uu____7288 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7288 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___174_7333  ->
                   match uu___174_7333 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7376 =
                           let uu____7395 =
                             let uu____7410 = inst_tscheme t in
                             FStar_Util.Inl uu____7410 in
                           (uu____7395, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7376
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7476,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7478);
                                     FStar_Syntax_Syntax.sigrng = uu____7479;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7480;
                                     FStar_Syntax_Syntax.sigmeta = uu____7481;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7482;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7502 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7502
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7548 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7555 -> cache t in
                       let uu____7556 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7556 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7631 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7631 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7717 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7797 = find_in_sigtab env lid in
         match uu____7797 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7896) ->
          add_sigelts env ses
      | uu____7905 ->
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
            | uu____7919 -> ()))
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
        (fun uu___175_7946  ->
           match uu___175_7946 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7964 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7997,lb::[]),uu____7999) ->
          let uu____8012 =
            let uu____8021 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8030 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8021, uu____8030) in
          FStar_Pervasives_Native.Some uu____8012
      | FStar_Syntax_Syntax.Sig_let ((uu____8043,lbs),uu____8045) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8081 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8093 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8093
                   then
                     let uu____8104 =
                       let uu____8113 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8122 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8113, uu____8122) in
                     FStar_Pervasives_Native.Some uu____8104
                   else FStar_Pervasives_Native.None)
      | uu____8144 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8177 =
          let uu____8186 =
            let uu____8191 =
              let uu____8192 =
                let uu____8195 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8195 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8192) in
            inst_tscheme uu____8191 in
          (uu____8186, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8177
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8215,uu____8216) ->
        let uu____8221 =
          let uu____8230 =
            let uu____8235 =
              let uu____8236 =
                let uu____8239 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8239 in
              (us, uu____8236) in
            inst_tscheme uu____8235 in
          (uu____8230, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8221
    | uu____8256 -> FStar_Pervasives_Native.None
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
      let mapper uu____8314 =
        match uu____8314 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8410,uvs,t,uu____8413,uu____8414,uu____8415);
                    FStar_Syntax_Syntax.sigrng = uu____8416;
                    FStar_Syntax_Syntax.sigquals = uu____8417;
                    FStar_Syntax_Syntax.sigmeta = uu____8418;
                    FStar_Syntax_Syntax.sigattrs = uu____8419;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8440 =
                   let uu____8449 = inst_tscheme (uvs, t) in
                   (uu____8449, rng) in
                 FStar_Pervasives_Native.Some uu____8440
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8469;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8471;
                    FStar_Syntax_Syntax.sigattrs = uu____8472;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8489 =
                   let uu____8490 = in_cur_mod env l in uu____8490 = Yes in
                 if uu____8489
                 then
                   let uu____8501 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8501
                    then
                      let uu____8514 =
                        let uu____8523 = inst_tscheme (uvs, t) in
                        (uu____8523, rng) in
                      FStar_Pervasives_Native.Some uu____8514
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8550 =
                      let uu____8559 = inst_tscheme (uvs, t) in
                      (uu____8559, rng) in
                    FStar_Pervasives_Native.Some uu____8550)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8580,uu____8581);
                    FStar_Syntax_Syntax.sigrng = uu____8582;
                    FStar_Syntax_Syntax.sigquals = uu____8583;
                    FStar_Syntax_Syntax.sigmeta = uu____8584;
                    FStar_Syntax_Syntax.sigattrs = uu____8585;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8624 =
                        let uu____8633 = inst_tscheme (uvs, k) in
                        (uu____8633, rng) in
                      FStar_Pervasives_Native.Some uu____8624
                  | uu____8650 ->
                      let uu____8651 =
                        let uu____8660 =
                          let uu____8665 =
                            let uu____8666 =
                              let uu____8669 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8669 in
                            (uvs, uu____8666) in
                          inst_tscheme uu____8665 in
                        (uu____8660, rng) in
                      FStar_Pervasives_Native.Some uu____8651)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8690,uu____8691);
                    FStar_Syntax_Syntax.sigrng = uu____8692;
                    FStar_Syntax_Syntax.sigquals = uu____8693;
                    FStar_Syntax_Syntax.sigmeta = uu____8694;
                    FStar_Syntax_Syntax.sigattrs = uu____8695;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8735 =
                        let uu____8744 = inst_tscheme_with (uvs, k) us in
                        (uu____8744, rng) in
                      FStar_Pervasives_Native.Some uu____8735
                  | uu____8761 ->
                      let uu____8762 =
                        let uu____8771 =
                          let uu____8776 =
                            let uu____8777 =
                              let uu____8780 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8780 in
                            (uvs, uu____8777) in
                          inst_tscheme_with uu____8776 us in
                        (uu____8771, rng) in
                      FStar_Pervasives_Native.Some uu____8762)
             | FStar_Util.Inr se ->
                 let uu____8814 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8835;
                        FStar_Syntax_Syntax.sigrng = uu____8836;
                        FStar_Syntax_Syntax.sigquals = uu____8837;
                        FStar_Syntax_Syntax.sigmeta = uu____8838;
                        FStar_Syntax_Syntax.sigattrs = uu____8839;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8854 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8814
                   (FStar_Util.map_option
                      (fun uu____8902  ->
                         match uu____8902 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8933 =
        let uu____8944 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8944 mapper in
      match uu____8933 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___195_9037 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___195_9037.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___195_9037.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9062 = lookup_qname env l in
      match uu____9062 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9101 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9149 = try_lookup_bv env bv in
      match uu____9149 with
      | FStar_Pervasives_Native.None  ->
          let uu____9164 = variable_not_found bv in
          FStar_Errors.raise_error uu____9164 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9179 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9180 =
            let uu____9181 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9181 in
          (uu____9179, uu____9180)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9198 = try_lookup_lid_aux env l in
      match uu____9198 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9264 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9264 in
          let uu____9265 =
            let uu____9274 =
              let uu____9279 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9279) in
            (uu____9274, r1) in
          FStar_Pervasives_Native.Some uu____9265
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9306 = try_lookup_lid env l in
      match uu____9306 with
      | FStar_Pervasives_Native.None  ->
          let uu____9333 = name_not_found l in
          FStar_Errors.raise_error uu____9333 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___176_9373  ->
              match uu___176_9373 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9375 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9390 = lookup_qname env lid in
      match uu____9390 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9419,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9422;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9424;
              FStar_Syntax_Syntax.sigattrs = uu____9425;_},FStar_Pervasives_Native.None
            ),uu____9426)
          ->
          let uu____9475 =
            let uu____9486 =
              let uu____9491 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9491) in
            (uu____9486, q) in
          FStar_Pervasives_Native.Some uu____9475
      | uu____9508 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9545 = lookup_qname env lid in
      match uu____9545 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9570,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9573;
              FStar_Syntax_Syntax.sigquals = uu____9574;
              FStar_Syntax_Syntax.sigmeta = uu____9575;
              FStar_Syntax_Syntax.sigattrs = uu____9576;_},FStar_Pervasives_Native.None
            ),uu____9577)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9626 ->
          let uu____9647 = name_not_found lid in
          FStar_Errors.raise_error uu____9647 (FStar_Ident.range_of_lid lid)
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9666 = lookup_qname env lid in
      match uu____9666 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9691,uvs,t,uu____9694,uu____9695,uu____9696);
              FStar_Syntax_Syntax.sigrng = uu____9697;
              FStar_Syntax_Syntax.sigquals = uu____9698;
              FStar_Syntax_Syntax.sigmeta = uu____9699;
              FStar_Syntax_Syntax.sigattrs = uu____9700;_},FStar_Pervasives_Native.None
            ),uu____9701)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9754 ->
          let uu____9775 = name_not_found lid in
          FStar_Errors.raise_error uu____9775 (FStar_Ident.range_of_lid lid)
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9796 = lookup_qname env lid in
      match uu____9796 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9823,uu____9824,uu____9825,uu____9826,uu____9827,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9829;
              FStar_Syntax_Syntax.sigquals = uu____9830;
              FStar_Syntax_Syntax.sigmeta = uu____9831;
              FStar_Syntax_Syntax.sigattrs = uu____9832;_},uu____9833),uu____9834)
          -> (true, dcs)
      | uu____9895 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9924 = lookup_qname env lid in
      match uu____9924 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9945,uu____9946,uu____9947,l,uu____9949,uu____9950);
              FStar_Syntax_Syntax.sigrng = uu____9951;
              FStar_Syntax_Syntax.sigquals = uu____9952;
              FStar_Syntax_Syntax.sigmeta = uu____9953;
              FStar_Syntax_Syntax.sigattrs = uu____9954;_},uu____9955),uu____9956)
          -> l
      | uu____10011 ->
          let uu____10032 =
            let uu____10033 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10033 in
          failwith uu____10032
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
        let uu____10067 = lookup_qname env lid in
        match uu____10067 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10095)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10146,lbs),uu____10148)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10176 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10176
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10208 -> FStar_Pervasives_Native.None)
        | uu____10213 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10248 = lookup_qname env ftv in
      match uu____10248 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10272) ->
          let uu____10317 = effect_signature se in
          (match uu____10317 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10338,t),r) ->
               let uu____10353 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10353)
      | uu____10354 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10381 = try_lookup_effect_lid env ftv in
      match uu____10381 with
      | FStar_Pervasives_Native.None  ->
          let uu____10384 = name_not_found ftv in
          FStar_Errors.raise_error uu____10384 (FStar_Ident.range_of_lid ftv)
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
        let uu____10405 = lookup_qname env lid0 in
        match uu____10405 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10436);
                FStar_Syntax_Syntax.sigrng = uu____10437;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10439;
                FStar_Syntax_Syntax.sigattrs = uu____10440;_},FStar_Pervasives_Native.None
              ),uu____10441)
            ->
            let lid1 =
              let uu____10495 =
                let uu____10496 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10496 in
              FStar_Ident.set_lid_range lid uu____10495 in
            let uu____10497 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___177_10501  ->
                      match uu___177_10501 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10502 -> false)) in
            if uu____10497
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10516 =
                      let uu____10517 =
                        let uu____10518 = get_range env in
                        FStar_Range.string_of_range uu____10518 in
                      let uu____10519 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10520 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10517 uu____10519 uu____10520 in
                    failwith uu____10516) in
               match (binders, univs1) with
               | ([],uu____10527) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10544,uu____10545::uu____10546::uu____10547) ->
                   let uu____10552 =
                     let uu____10553 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10554 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10553 uu____10554 in
                   failwith uu____10552
               | uu____10561 ->
                   let uu____10566 =
                     let uu____10571 =
                       let uu____10572 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10572) in
                     inst_tscheme_with uu____10571 insts in
                   (match uu____10566 with
                    | (uu____10583,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10586 =
                          let uu____10587 = FStar_Syntax_Subst.compress t1 in
                          uu____10587.FStar_Syntax_Syntax.n in
                        (match uu____10586 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10634 -> failwith "Impossible")))
        | uu____10641 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10681 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10681 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10694,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10701 = find1 l2 in
            (match uu____10701 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10708 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10708 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10712 = find1 l in
            (match uu____10712 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10726 = lookup_qname env l1 in
      match uu____10726 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10749;
              FStar_Syntax_Syntax.sigrng = uu____10750;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10752;
              FStar_Syntax_Syntax.sigattrs = uu____10753;_},uu____10754),uu____10755)
          -> q
      | uu____10806 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10839 =
          let uu____10840 =
            let uu____10841 = FStar_Util.string_of_int i in
            let uu____10842 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10841 uu____10842 in
          failwith uu____10840 in
        let uu____10843 = lookup_datacon env lid in
        match uu____10843 with
        | (uu____10848,t) ->
            let uu____10850 =
              let uu____10851 = FStar_Syntax_Subst.compress t in
              uu____10851.FStar_Syntax_Syntax.n in
            (match uu____10850 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10855) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10886 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10886
                      FStar_Pervasives_Native.fst)
             | uu____10895 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10902 = lookup_qname env l in
      match uu____10902 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10923,uu____10924,uu____10925);
              FStar_Syntax_Syntax.sigrng = uu____10926;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10928;
              FStar_Syntax_Syntax.sigattrs = uu____10929;_},uu____10930),uu____10931)
          ->
          FStar_Util.for_some
            (fun uu___178_10984  ->
               match uu___178_10984 with
               | FStar_Syntax_Syntax.Projector uu____10985 -> true
               | uu____10990 -> false) quals
      | uu____10991 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11018 = lookup_qname env lid in
      match uu____11018 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11039,uu____11040,uu____11041,uu____11042,uu____11043,uu____11044);
              FStar_Syntax_Syntax.sigrng = uu____11045;
              FStar_Syntax_Syntax.sigquals = uu____11046;
              FStar_Syntax_Syntax.sigmeta = uu____11047;
              FStar_Syntax_Syntax.sigattrs = uu____11048;_},uu____11049),uu____11050)
          -> true
      | uu____11105 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11132 = lookup_qname env lid in
      match uu____11132 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11153,uu____11154,uu____11155,uu____11156,uu____11157,uu____11158);
              FStar_Syntax_Syntax.sigrng = uu____11159;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11161;
              FStar_Syntax_Syntax.sigattrs = uu____11162;_},uu____11163),uu____11164)
          ->
          FStar_Util.for_some
            (fun uu___179_11225  ->
               match uu___179_11225 with
               | FStar_Syntax_Syntax.RecordType uu____11226 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11235 -> true
               | uu____11244 -> false) quals
      | uu____11245 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11272 = lookup_qname env lid in
      match uu____11272 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11293,uu____11294);
              FStar_Syntax_Syntax.sigrng = uu____11295;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11297;
              FStar_Syntax_Syntax.sigattrs = uu____11298;_},uu____11299),uu____11300)
          ->
          FStar_Util.for_some
            (fun uu___180_11357  ->
               match uu___180_11357 with
               | FStar_Syntax_Syntax.Action uu____11358 -> true
               | uu____11359 -> false) quals
      | uu____11360 -> false
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
      let uu____11390 =
        let uu____11391 = FStar_Syntax_Util.un_uinst head1 in
        uu____11391.FStar_Syntax_Syntax.n in
      match uu____11390 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11395 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11460 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11476) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11493 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11500 ->
                 FStar_Pervasives_Native.Some true
             | uu____11517 -> FStar_Pervasives_Native.Some false) in
      let uu____11518 =
        let uu____11521 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11521 mapper in
      match uu____11518 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11567 = lookup_qname env lid in
      match uu____11567 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11588,uu____11589,tps,uu____11591,uu____11592,uu____11593);
              FStar_Syntax_Syntax.sigrng = uu____11594;
              FStar_Syntax_Syntax.sigquals = uu____11595;
              FStar_Syntax_Syntax.sigmeta = uu____11596;
              FStar_Syntax_Syntax.sigattrs = uu____11597;_},uu____11598),uu____11599)
          -> FStar_List.length tps
      | uu____11662 ->
          let uu____11683 = name_not_found lid in
          FStar_Errors.raise_error uu____11683 (FStar_Ident.range_of_lid lid)
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
           (fun uu____11727  ->
              match uu____11727 with
              | (d,uu____11735) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11746 = effect_decl_opt env l in
      match uu____11746 with
      | FStar_Pervasives_Native.None  ->
          let uu____11761 = name_not_found l in
          FStar_Errors.raise_error uu____11761 (FStar_Ident.range_of_lid l)
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
            (let uu____11828 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11881  ->
                       match uu____11881 with
                       | (m1,m2,uu____11894,uu____11895,uu____11896) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11828 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11913 =
                   let uu____11918 =
                     let uu____11919 = FStar_Syntax_Print.lid_to_string l1 in
                     let uu____11920 = FStar_Syntax_Print.lid_to_string l2 in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11919
                       uu____11920 in
                   (FStar_Errors.EffectsCannotBeComposed, uu____11918) in
                 FStar_Errors.raise_error uu____11913 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11927,uu____11928,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11965 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11965)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11992 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12018  ->
                match uu____12018 with
                | (d,uu____12024) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11992 with
      | FStar_Pervasives_Native.None  ->
          let uu____12035 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12035
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12048 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12048 with
           | (uu____12059,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12069)::(wp,uu____12071)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12107 -> failwith "Impossible"))
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
                 let uu____12150 = get_range env in
                 let uu____12151 =
                   let uu____12154 =
                     let uu____12155 =
                       let uu____12170 =
                         let uu____12173 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12173] in
                       (null_wp, uu____12170) in
                     FStar_Syntax_Syntax.Tm_app uu____12155 in
                   FStar_Syntax_Syntax.mk uu____12154 in
                 uu____12151 FStar_Pervasives_Native.None uu____12150 in
               let uu____12179 =
                 let uu____12180 =
                   let uu____12189 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12189] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12180;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12179)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___196_12198 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___196_12198.order);
              joins = (uu___196_12198.joins)
            } in
          let uu___197_12207 = env in
          {
            solver = (uu___197_12207.solver);
            range = (uu___197_12207.range);
            curmodule = (uu___197_12207.curmodule);
            gamma = (uu___197_12207.gamma);
            gamma_cache = (uu___197_12207.gamma_cache);
            modules = (uu___197_12207.modules);
            expected_typ = (uu___197_12207.expected_typ);
            sigtab = (uu___197_12207.sigtab);
            is_pattern = (uu___197_12207.is_pattern);
            instantiate_imp = (uu___197_12207.instantiate_imp);
            effects;
            generalize = (uu___197_12207.generalize);
            letrecs = (uu___197_12207.letrecs);
            top_level = (uu___197_12207.top_level);
            check_uvars = (uu___197_12207.check_uvars);
            use_eq = (uu___197_12207.use_eq);
            is_iface = (uu___197_12207.is_iface);
            admit = (uu___197_12207.admit);
            lax = (uu___197_12207.lax);
            lax_universes = (uu___197_12207.lax_universes);
            failhard = (uu___197_12207.failhard);
            nosynth = (uu___197_12207.nosynth);
            tc_term = (uu___197_12207.tc_term);
            type_of = (uu___197_12207.type_of);
            universe_of = (uu___197_12207.universe_of);
            use_bv_sorts = (uu___197_12207.use_bv_sorts);
            qname_and_index = (uu___197_12207.qname_and_index);
            proof_ns = (uu___197_12207.proof_ns);
            synth = (uu___197_12207.synth);
            is_native_tactic = (uu___197_12207.is_native_tactic);
            identifier_info = (uu___197_12207.identifier_info);
            tc_hooks = (uu___197_12207.tc_hooks);
            dsenv = (uu___197_12207.dsenv);
            dep_graph = (uu___197_12207.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12224 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12224 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12314 = (e1.mlift).mlift_wp t wp in
                              let uu____12315 = l1 t wp e in
                              l2 t uu____12314 uu____12315))
                | uu____12316 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12355 = inst_tscheme lift_t in
            match uu____12355 with
            | (uu____12362,lift_t1) ->
                let uu____12364 =
                  let uu____12367 =
                    let uu____12368 =
                      let uu____12383 =
                        let uu____12386 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12387 =
                          let uu____12390 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12390] in
                        uu____12386 :: uu____12387 in
                      (lift_t1, uu____12383) in
                    FStar_Syntax_Syntax.Tm_app uu____12368 in
                  FStar_Syntax_Syntax.mk uu____12367 in
                uu____12364 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12431 = inst_tscheme lift_t in
            match uu____12431 with
            | (uu____12438,lift_t1) ->
                let uu____12440 =
                  let uu____12443 =
                    let uu____12444 =
                      let uu____12459 =
                        let uu____12462 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12463 =
                          let uu____12466 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12467 =
                            let uu____12470 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12470] in
                          uu____12466 :: uu____12467 in
                        uu____12462 :: uu____12463 in
                      (lift_t1, uu____12459) in
                    FStar_Syntax_Syntax.Tm_app uu____12444 in
                  FStar_Syntax_Syntax.mk uu____12443 in
                uu____12440 FStar_Pervasives_Native.None
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
              let uu____12508 =
                let uu____12509 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12509
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12508 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12513 =
              let uu____12514 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12514 in
            let uu____12515 =
              let uu____12516 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12534 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12534) in
              FStar_Util.dflt "none" uu____12516 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12513
              uu____12515 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12560  ->
                    match uu____12560 with
                    | (e,uu____12568) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12587 =
            match uu____12587 with
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
              let uu____12625 =
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
                                    (let uu____12646 =
                                       let uu____12655 =
                                         find_edge order1 (i, k) in
                                       let uu____12658 =
                                         find_edge order1 (k, j) in
                                       (uu____12655, uu____12658) in
                                     match uu____12646 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12673 =
                                           compose_edges e1 e2 in
                                         [uu____12673]
                                     | uu____12674 -> []))))) in
              FStar_List.append order1 uu____12625 in
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
                   let uu____12704 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12706 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12706
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12704
                   then
                     let uu____12711 =
                       let uu____12716 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str in
                       (FStar_Errors.DivergentComputationCannotBeIncludedInTotal,
                         uu____12716) in
                     let uu____12717 = get_range env in
                     FStar_Errors.raise_error uu____12711 uu____12717
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
                                            let uu____12842 =
                                              let uu____12851 =
                                                find_edge order2 (i, k) in
                                              let uu____12854 =
                                                find_edge order2 (j, k) in
                                              (uu____12851, uu____12854) in
                                            match uu____12842 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12896,uu____12897)
                                                     ->
                                                     let uu____12904 =
                                                       let uu____12909 =
                                                         let uu____12910 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12910 in
                                                       let uu____12913 =
                                                         let uu____12914 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12914 in
                                                       (uu____12909,
                                                         uu____12913) in
                                                     (match uu____12904 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Errors.maybe_fatal_err
                                                               (FStar_Errors.UpperBoundCandidateAlreadyVisited,
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
                                            | uu____12949 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___198_13022 = env.effects in
              { decls = (uu___198_13022.decls); order = order2; joins } in
            let uu___199_13023 = env in
            {
              solver = (uu___199_13023.solver);
              range = (uu___199_13023.range);
              curmodule = (uu___199_13023.curmodule);
              gamma = (uu___199_13023.gamma);
              gamma_cache = (uu___199_13023.gamma_cache);
              modules = (uu___199_13023.modules);
              expected_typ = (uu___199_13023.expected_typ);
              sigtab = (uu___199_13023.sigtab);
              is_pattern = (uu___199_13023.is_pattern);
              instantiate_imp = (uu___199_13023.instantiate_imp);
              effects;
              generalize = (uu___199_13023.generalize);
              letrecs = (uu___199_13023.letrecs);
              top_level = (uu___199_13023.top_level);
              check_uvars = (uu___199_13023.check_uvars);
              use_eq = (uu___199_13023.use_eq);
              is_iface = (uu___199_13023.is_iface);
              admit = (uu___199_13023.admit);
              lax = (uu___199_13023.lax);
              lax_universes = (uu___199_13023.lax_universes);
              failhard = (uu___199_13023.failhard);
              nosynth = (uu___199_13023.nosynth);
              tc_term = (uu___199_13023.tc_term);
              type_of = (uu___199_13023.type_of);
              universe_of = (uu___199_13023.universe_of);
              use_bv_sorts = (uu___199_13023.use_bv_sorts);
              qname_and_index = (uu___199_13023.qname_and_index);
              proof_ns = (uu___199_13023.proof_ns);
              synth = (uu___199_13023.synth);
              is_native_tactic = (uu___199_13023.is_native_tactic);
              identifier_info = (uu___199_13023.identifier_info);
              tc_hooks = (uu___199_13023.tc_hooks);
              dsenv = (uu___199_13023.dsenv);
              dep_graph = (uu___199_13023.dep_graph)
            }))
      | uu____13024 -> env
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
        | uu____13048 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13056 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13056 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13073 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13073 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13091 =
                     let uu____13096 =
                       let uu____13097 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____13102 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1")) in
                       let uu____13109 =
                         let uu____13110 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____13110 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13097 uu____13102 uu____13109 in
                     (FStar_Errors.ConstructorArgLengthMismatch, uu____13096) in
                   FStar_Errors.raise_error uu____13091
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13115 =
                     let uu____13124 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13124 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13141  ->
                        fun uu____13142  ->
                          match (uu____13141, uu____13142) with
                          | ((x,uu____13164),(t,uu____13166)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13115 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13185 =
                     let uu___200_13186 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___200_13186.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___200_13186.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___200_13186.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___200_13186.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13185
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
          let uu____13208 = effect_decl_opt env effect_name in
          match uu____13208 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13241 =
                only_reifiable &&
                  (let uu____13243 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13243) in
              if uu____13241
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13259 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13278 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13307 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13307
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13308 = get_range env in
                           FStar_Errors.raise_error
                             (FStar_Errors.NotEnoughArgumentsForEffect,
                               message) uu____13308 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13318 =
                       let uu____13321 = get_range env in
                       let uu____13322 =
                         let uu____13325 =
                           let uu____13326 =
                             let uu____13341 =
                               let uu____13344 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13344; wp] in
                             (repr, uu____13341) in
                           FStar_Syntax_Syntax.Tm_app uu____13326 in
                         FStar_Syntax_Syntax.mk uu____13325 in
                       uu____13322 FStar_Pervasives_Native.None uu____13321 in
                     FStar_Pervasives_Native.Some uu____13318)
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
          let uu____13390 =
            let uu____13395 =
              let uu____13396 = FStar_Ident.string_of_lid l in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13396 in
            (FStar_Errors.EffectCannotBeReified, uu____13395) in
          let uu____13397 = get_range env in
          FStar_Errors.raise_error uu____13390 uu____13397 in
        let uu____13398 = effect_repr_aux true env c u_c in
        match uu____13398 with
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
      | uu____13432 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13439 =
        let uu____13440 = FStar_Syntax_Subst.compress t in
        uu____13440.FStar_Syntax_Syntax.n in
      match uu____13439 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13443,c) ->
          is_reifiable_comp env c
      | uu____13461 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13483)::uu____13484 -> x :: rest
        | (Binding_sig_inst uu____13493)::uu____13494 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13509 = push1 x rest1 in local :: uu____13509 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___201_13513 = env in
       let uu____13514 = push1 s env.gamma in
       {
         solver = (uu___201_13513.solver);
         range = (uu___201_13513.range);
         curmodule = (uu___201_13513.curmodule);
         gamma = uu____13514;
         gamma_cache = (uu___201_13513.gamma_cache);
         modules = (uu___201_13513.modules);
         expected_typ = (uu___201_13513.expected_typ);
         sigtab = (uu___201_13513.sigtab);
         is_pattern = (uu___201_13513.is_pattern);
         instantiate_imp = (uu___201_13513.instantiate_imp);
         effects = (uu___201_13513.effects);
         generalize = (uu___201_13513.generalize);
         letrecs = (uu___201_13513.letrecs);
         top_level = (uu___201_13513.top_level);
         check_uvars = (uu___201_13513.check_uvars);
         use_eq = (uu___201_13513.use_eq);
         is_iface = (uu___201_13513.is_iface);
         admit = (uu___201_13513.admit);
         lax = (uu___201_13513.lax);
         lax_universes = (uu___201_13513.lax_universes);
         failhard = (uu___201_13513.failhard);
         nosynth = (uu___201_13513.nosynth);
         tc_term = (uu___201_13513.tc_term);
         type_of = (uu___201_13513.type_of);
         universe_of = (uu___201_13513.universe_of);
         use_bv_sorts = (uu___201_13513.use_bv_sorts);
         qname_and_index = (uu___201_13513.qname_and_index);
         proof_ns = (uu___201_13513.proof_ns);
         synth = (uu___201_13513.synth);
         is_native_tactic = (uu___201_13513.is_native_tactic);
         identifier_info = (uu___201_13513.identifier_info);
         tc_hooks = (uu___201_13513.tc_hooks);
         dsenv = (uu___201_13513.dsenv);
         dep_graph = (uu___201_13513.dep_graph)
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
      let uu___202_13544 = env in
      {
        solver = (uu___202_13544.solver);
        range = (uu___202_13544.range);
        curmodule = (uu___202_13544.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___202_13544.gamma_cache);
        modules = (uu___202_13544.modules);
        expected_typ = (uu___202_13544.expected_typ);
        sigtab = (uu___202_13544.sigtab);
        is_pattern = (uu___202_13544.is_pattern);
        instantiate_imp = (uu___202_13544.instantiate_imp);
        effects = (uu___202_13544.effects);
        generalize = (uu___202_13544.generalize);
        letrecs = (uu___202_13544.letrecs);
        top_level = (uu___202_13544.top_level);
        check_uvars = (uu___202_13544.check_uvars);
        use_eq = (uu___202_13544.use_eq);
        is_iface = (uu___202_13544.is_iface);
        admit = (uu___202_13544.admit);
        lax = (uu___202_13544.lax);
        lax_universes = (uu___202_13544.lax_universes);
        failhard = (uu___202_13544.failhard);
        nosynth = (uu___202_13544.nosynth);
        tc_term = (uu___202_13544.tc_term);
        type_of = (uu___202_13544.type_of);
        universe_of = (uu___202_13544.universe_of);
        use_bv_sorts = (uu___202_13544.use_bv_sorts);
        qname_and_index = (uu___202_13544.qname_and_index);
        proof_ns = (uu___202_13544.proof_ns);
        synth = (uu___202_13544.synth);
        is_native_tactic = (uu___202_13544.is_native_tactic);
        identifier_info = (uu___202_13544.identifier_info);
        tc_hooks = (uu___202_13544.tc_hooks);
        dsenv = (uu___202_13544.dsenv);
        dep_graph = (uu___202_13544.dep_graph)
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
            (let uu___203_13575 = env in
             {
               solver = (uu___203_13575.solver);
               range = (uu___203_13575.range);
               curmodule = (uu___203_13575.curmodule);
               gamma = rest;
               gamma_cache = (uu___203_13575.gamma_cache);
               modules = (uu___203_13575.modules);
               expected_typ = (uu___203_13575.expected_typ);
               sigtab = (uu___203_13575.sigtab);
               is_pattern = (uu___203_13575.is_pattern);
               instantiate_imp = (uu___203_13575.instantiate_imp);
               effects = (uu___203_13575.effects);
               generalize = (uu___203_13575.generalize);
               letrecs = (uu___203_13575.letrecs);
               top_level = (uu___203_13575.top_level);
               check_uvars = (uu___203_13575.check_uvars);
               use_eq = (uu___203_13575.use_eq);
               is_iface = (uu___203_13575.is_iface);
               admit = (uu___203_13575.admit);
               lax = (uu___203_13575.lax);
               lax_universes = (uu___203_13575.lax_universes);
               failhard = (uu___203_13575.failhard);
               nosynth = (uu___203_13575.nosynth);
               tc_term = (uu___203_13575.tc_term);
               type_of = (uu___203_13575.type_of);
               universe_of = (uu___203_13575.universe_of);
               use_bv_sorts = (uu___203_13575.use_bv_sorts);
               qname_and_index = (uu___203_13575.qname_and_index);
               proof_ns = (uu___203_13575.proof_ns);
               synth = (uu___203_13575.synth);
               is_native_tactic = (uu___203_13575.is_native_tactic);
               identifier_info = (uu___203_13575.identifier_info);
               tc_hooks = (uu___203_13575.tc_hooks);
               dsenv = (uu___203_13575.dsenv);
               dep_graph = (uu___203_13575.dep_graph)
             }))
    | uu____13576 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13598  ->
             match uu____13598 with | (x,uu____13604) -> push_bv env1 x) env
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
            let uu___204_13632 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___204_13632.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___204_13632.FStar_Syntax_Syntax.index);
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
      (let uu___205_13662 = env in
       {
         solver = (uu___205_13662.solver);
         range = (uu___205_13662.range);
         curmodule = (uu___205_13662.curmodule);
         gamma = [];
         gamma_cache = (uu___205_13662.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___205_13662.sigtab);
         is_pattern = (uu___205_13662.is_pattern);
         instantiate_imp = (uu___205_13662.instantiate_imp);
         effects = (uu___205_13662.effects);
         generalize = (uu___205_13662.generalize);
         letrecs = (uu___205_13662.letrecs);
         top_level = (uu___205_13662.top_level);
         check_uvars = (uu___205_13662.check_uvars);
         use_eq = (uu___205_13662.use_eq);
         is_iface = (uu___205_13662.is_iface);
         admit = (uu___205_13662.admit);
         lax = (uu___205_13662.lax);
         lax_universes = (uu___205_13662.lax_universes);
         failhard = (uu___205_13662.failhard);
         nosynth = (uu___205_13662.nosynth);
         tc_term = (uu___205_13662.tc_term);
         type_of = (uu___205_13662.type_of);
         universe_of = (uu___205_13662.universe_of);
         use_bv_sorts = (uu___205_13662.use_bv_sorts);
         qname_and_index = (uu___205_13662.qname_and_index);
         proof_ns = (uu___205_13662.proof_ns);
         synth = (uu___205_13662.synth);
         is_native_tactic = (uu___205_13662.is_native_tactic);
         identifier_info = (uu___205_13662.identifier_info);
         tc_hooks = (uu___205_13662.tc_hooks);
         dsenv = (uu___205_13662.dsenv);
         dep_graph = (uu___205_13662.dep_graph)
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
        let uu____13694 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13694 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13722 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13722)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___206_13735 = env in
      {
        solver = (uu___206_13735.solver);
        range = (uu___206_13735.range);
        curmodule = (uu___206_13735.curmodule);
        gamma = (uu___206_13735.gamma);
        gamma_cache = (uu___206_13735.gamma_cache);
        modules = (uu___206_13735.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___206_13735.sigtab);
        is_pattern = (uu___206_13735.is_pattern);
        instantiate_imp = (uu___206_13735.instantiate_imp);
        effects = (uu___206_13735.effects);
        generalize = (uu___206_13735.generalize);
        letrecs = (uu___206_13735.letrecs);
        top_level = (uu___206_13735.top_level);
        check_uvars = (uu___206_13735.check_uvars);
        use_eq = false;
        is_iface = (uu___206_13735.is_iface);
        admit = (uu___206_13735.admit);
        lax = (uu___206_13735.lax);
        lax_universes = (uu___206_13735.lax_universes);
        failhard = (uu___206_13735.failhard);
        nosynth = (uu___206_13735.nosynth);
        tc_term = (uu___206_13735.tc_term);
        type_of = (uu___206_13735.type_of);
        universe_of = (uu___206_13735.universe_of);
        use_bv_sorts = (uu___206_13735.use_bv_sorts);
        qname_and_index = (uu___206_13735.qname_and_index);
        proof_ns = (uu___206_13735.proof_ns);
        synth = (uu___206_13735.synth);
        is_native_tactic = (uu___206_13735.is_native_tactic);
        identifier_info = (uu___206_13735.identifier_info);
        tc_hooks = (uu___206_13735.tc_hooks);
        dsenv = (uu___206_13735.dsenv);
        dep_graph = (uu___206_13735.dep_graph)
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
    let uu____13759 = expected_typ env_ in
    ((let uu___207_13765 = env_ in
      {
        solver = (uu___207_13765.solver);
        range = (uu___207_13765.range);
        curmodule = (uu___207_13765.curmodule);
        gamma = (uu___207_13765.gamma);
        gamma_cache = (uu___207_13765.gamma_cache);
        modules = (uu___207_13765.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___207_13765.sigtab);
        is_pattern = (uu___207_13765.is_pattern);
        instantiate_imp = (uu___207_13765.instantiate_imp);
        effects = (uu___207_13765.effects);
        generalize = (uu___207_13765.generalize);
        letrecs = (uu___207_13765.letrecs);
        top_level = (uu___207_13765.top_level);
        check_uvars = (uu___207_13765.check_uvars);
        use_eq = false;
        is_iface = (uu___207_13765.is_iface);
        admit = (uu___207_13765.admit);
        lax = (uu___207_13765.lax);
        lax_universes = (uu___207_13765.lax_universes);
        failhard = (uu___207_13765.failhard);
        nosynth = (uu___207_13765.nosynth);
        tc_term = (uu___207_13765.tc_term);
        type_of = (uu___207_13765.type_of);
        universe_of = (uu___207_13765.universe_of);
        use_bv_sorts = (uu___207_13765.use_bv_sorts);
        qname_and_index = (uu___207_13765.qname_and_index);
        proof_ns = (uu___207_13765.proof_ns);
        synth = (uu___207_13765.synth);
        is_native_tactic = (uu___207_13765.is_native_tactic);
        identifier_info = (uu___207_13765.identifier_info);
        tc_hooks = (uu___207_13765.tc_hooks);
        dsenv = (uu___207_13765.dsenv);
        dep_graph = (uu___207_13765.dep_graph)
      }), uu____13759)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13778 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___181_13788  ->
                    match uu___181_13788 with
                    | Binding_sig (uu____13791,se) -> [se]
                    | uu____13797 -> [])) in
          FStar_All.pipe_right uu____13778 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___208_13804 = env in
       {
         solver = (uu___208_13804.solver);
         range = (uu___208_13804.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___208_13804.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___208_13804.expected_typ);
         sigtab = (uu___208_13804.sigtab);
         is_pattern = (uu___208_13804.is_pattern);
         instantiate_imp = (uu___208_13804.instantiate_imp);
         effects = (uu___208_13804.effects);
         generalize = (uu___208_13804.generalize);
         letrecs = (uu___208_13804.letrecs);
         top_level = (uu___208_13804.top_level);
         check_uvars = (uu___208_13804.check_uvars);
         use_eq = (uu___208_13804.use_eq);
         is_iface = (uu___208_13804.is_iface);
         admit = (uu___208_13804.admit);
         lax = (uu___208_13804.lax);
         lax_universes = (uu___208_13804.lax_universes);
         failhard = (uu___208_13804.failhard);
         nosynth = (uu___208_13804.nosynth);
         tc_term = (uu___208_13804.tc_term);
         type_of = (uu___208_13804.type_of);
         universe_of = (uu___208_13804.universe_of);
         use_bv_sorts = (uu___208_13804.use_bv_sorts);
         qname_and_index = (uu___208_13804.qname_and_index);
         proof_ns = (uu___208_13804.proof_ns);
         synth = (uu___208_13804.synth);
         is_native_tactic = (uu___208_13804.is_native_tactic);
         identifier_info = (uu___208_13804.identifier_info);
         tc_hooks = (uu___208_13804.tc_hooks);
         dsenv = (uu___208_13804.dsenv);
         dep_graph = (uu___208_13804.dep_graph)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13885)::tl1 -> aux out tl1
      | (Binding_lid (uu____13889,(uu____13890,t)))::tl1 ->
          let uu____13905 =
            let uu____13912 = FStar_Syntax_Free.uvars t in
            ext out uu____13912 in
          aux uu____13905 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13919;
            FStar_Syntax_Syntax.index = uu____13920;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13927 =
            let uu____13934 = FStar_Syntax_Free.uvars t in
            ext out uu____13934 in
          aux uu____13927 tl1
      | (Binding_sig uu____13941)::uu____13942 -> out
      | (Binding_sig_inst uu____13951)::uu____13952 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14007)::tl1 -> aux out tl1
      | (Binding_univ uu____14019)::tl1 -> aux out tl1
      | (Binding_lid (uu____14023,(uu____14024,t)))::tl1 ->
          let uu____14039 =
            let uu____14042 = FStar_Syntax_Free.univs t in
            ext out uu____14042 in
          aux uu____14039 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14045;
            FStar_Syntax_Syntax.index = uu____14046;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14053 =
            let uu____14056 = FStar_Syntax_Free.univs t in
            ext out uu____14056 in
          aux uu____14053 tl1
      | (Binding_sig uu____14059)::uu____14060 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14113)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14129 = FStar_Util.fifo_set_add uname out in
          aux uu____14129 tl1
      | (Binding_lid (uu____14132,(uu____14133,t)))::tl1 ->
          let uu____14148 =
            let uu____14151 = FStar_Syntax_Free.univnames t in
            ext out uu____14151 in
          aux uu____14148 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14154;
            FStar_Syntax_Syntax.index = uu____14155;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14162 =
            let uu____14165 = FStar_Syntax_Free.univnames t in
            ext out uu____14165 in
          aux uu____14162 tl1
      | (Binding_sig uu____14168)::uu____14169 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___182_14193  ->
            match uu___182_14193 with
            | Binding_var x -> [x]
            | Binding_lid uu____14197 -> []
            | Binding_sig uu____14202 -> []
            | Binding_univ uu____14209 -> []
            | Binding_sig_inst uu____14210 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14226 =
      let uu____14229 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14229
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14226 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14251 =
      let uu____14252 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___183_14262  ->
                match uu___183_14262 with
                | Binding_var x ->
                    let uu____14264 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14264
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14267) ->
                    let uu____14268 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14268
                | Binding_sig (ls,uu____14270) ->
                    let uu____14275 =
                      let uu____14276 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14276
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14275
                | Binding_sig_inst (ls,uu____14286,uu____14287) ->
                    let uu____14292 =
                      let uu____14293 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14293
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14292)) in
      FStar_All.pipe_right uu____14252 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14251 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14310 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14310
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14338  ->
                 fun uu____14339  ->
                   match (uu____14338, uu____14339) with
                   | ((b1,uu____14357),(b2,uu____14359)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___184_14401  ->
    match uu___184_14401 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14402 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___185_14420  ->
             match uu___185_14420 with
             | Binding_sig (lids,uu____14426) -> FStar_List.append lids keys
             | uu____14431 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14437  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14471) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14490,uu____14491) -> false in
      let uu____14500 =
        FStar_List.tryFind
          (fun uu____14518  ->
             match uu____14518 with | (p,uu____14526) -> list_prefix p path)
          env.proof_ns in
      match uu____14500 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14537,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14555 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14555
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___209_14567 = e in
        {
          solver = (uu___209_14567.solver);
          range = (uu___209_14567.range);
          curmodule = (uu___209_14567.curmodule);
          gamma = (uu___209_14567.gamma);
          gamma_cache = (uu___209_14567.gamma_cache);
          modules = (uu___209_14567.modules);
          expected_typ = (uu___209_14567.expected_typ);
          sigtab = (uu___209_14567.sigtab);
          is_pattern = (uu___209_14567.is_pattern);
          instantiate_imp = (uu___209_14567.instantiate_imp);
          effects = (uu___209_14567.effects);
          generalize = (uu___209_14567.generalize);
          letrecs = (uu___209_14567.letrecs);
          top_level = (uu___209_14567.top_level);
          check_uvars = (uu___209_14567.check_uvars);
          use_eq = (uu___209_14567.use_eq);
          is_iface = (uu___209_14567.is_iface);
          admit = (uu___209_14567.admit);
          lax = (uu___209_14567.lax);
          lax_universes = (uu___209_14567.lax_universes);
          failhard = (uu___209_14567.failhard);
          nosynth = (uu___209_14567.nosynth);
          tc_term = (uu___209_14567.tc_term);
          type_of = (uu___209_14567.type_of);
          universe_of = (uu___209_14567.universe_of);
          use_bv_sorts = (uu___209_14567.use_bv_sorts);
          qname_and_index = (uu___209_14567.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___209_14567.synth);
          is_native_tactic = (uu___209_14567.is_native_tactic);
          identifier_info = (uu___209_14567.identifier_info);
          tc_hooks = (uu___209_14567.tc_hooks);
          dsenv = (uu___209_14567.dsenv);
          dep_graph = (uu___209_14567.dep_graph)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___210_14593 = e in
      {
        solver = (uu___210_14593.solver);
        range = (uu___210_14593.range);
        curmodule = (uu___210_14593.curmodule);
        gamma = (uu___210_14593.gamma);
        gamma_cache = (uu___210_14593.gamma_cache);
        modules = (uu___210_14593.modules);
        expected_typ = (uu___210_14593.expected_typ);
        sigtab = (uu___210_14593.sigtab);
        is_pattern = (uu___210_14593.is_pattern);
        instantiate_imp = (uu___210_14593.instantiate_imp);
        effects = (uu___210_14593.effects);
        generalize = (uu___210_14593.generalize);
        letrecs = (uu___210_14593.letrecs);
        top_level = (uu___210_14593.top_level);
        check_uvars = (uu___210_14593.check_uvars);
        use_eq = (uu___210_14593.use_eq);
        is_iface = (uu___210_14593.is_iface);
        admit = (uu___210_14593.admit);
        lax = (uu___210_14593.lax);
        lax_universes = (uu___210_14593.lax_universes);
        failhard = (uu___210_14593.failhard);
        nosynth = (uu___210_14593.nosynth);
        tc_term = (uu___210_14593.tc_term);
        type_of = (uu___210_14593.type_of);
        universe_of = (uu___210_14593.universe_of);
        use_bv_sorts = (uu___210_14593.use_bv_sorts);
        qname_and_index = (uu___210_14593.qname_and_index);
        proof_ns = ns;
        synth = (uu___210_14593.synth);
        is_native_tactic = (uu___210_14593.is_native_tactic);
        identifier_info = (uu___210_14593.identifier_info);
        tc_hooks = (uu___210_14593.tc_hooks);
        dsenv = (uu___210_14593.dsenv);
        dep_graph = (uu___210_14593.dep_graph)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14604 = FStar_Syntax_Free.names t in
      let uu____14607 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14604 uu____14607
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14624 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14624
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14630 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14630
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14645 =
      match uu____14645 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14661 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14661) in
    let uu____14663 =
      let uu____14666 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14666 FStar_List.rev in
    FStar_All.pipe_right uu____14663 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14683  -> ());
    push = (fun uu____14685  -> ());
    pop = (fun uu____14687  -> ());
    encode_modul = (fun uu____14690  -> fun uu____14691  -> ());
    encode_sig = (fun uu____14694  -> fun uu____14695  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14701 =
             let uu____14708 = FStar_Options.peek () in (e, g, uu____14708) in
           [uu____14701]);
    solve = (fun uu____14724  -> fun uu____14725  -> fun uu____14726  -> ());
    finish = (fun uu____14732  -> ());
    refresh = (fun uu____14734  -> ())
  }