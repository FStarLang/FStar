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
           (fun uu___251_4961  ->
              match uu___251_4961 with
              | Binding_var x ->
                  let y =
                    let uu____4964 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____4964 in
                  let uu____4965 =
                    let uu____4966 = FStar_Syntax_Subst.compress y in
                    uu____4966.FStar_Syntax_Syntax.n in
                  (match uu____4965 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____4970 =
                         let uu___265_4971 = y1 in
                         let uu____4972 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___265_4971.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___265_4971.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____4972
                         } in
                       Binding_var uu____4970
                   | uu____4975 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___266_4983 = env in
      let uu____4984 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___266_4983.solver);
        range = (uu___266_4983.range);
        curmodule = (uu___266_4983.curmodule);
        gamma = uu____4984;
        gamma_cache = (uu___266_4983.gamma_cache);
        modules = (uu___266_4983.modules);
        expected_typ = (uu___266_4983.expected_typ);
        sigtab = (uu___266_4983.sigtab);
        is_pattern = (uu___266_4983.is_pattern);
        instantiate_imp = (uu___266_4983.instantiate_imp);
        effects = (uu___266_4983.effects);
        generalize = (uu___266_4983.generalize);
        letrecs = (uu___266_4983.letrecs);
        top_level = (uu___266_4983.top_level);
        check_uvars = (uu___266_4983.check_uvars);
        use_eq = (uu___266_4983.use_eq);
        is_iface = (uu___266_4983.is_iface);
        admit = (uu___266_4983.admit);
        lax = (uu___266_4983.lax);
        lax_universes = (uu___266_4983.lax_universes);
        failhard = (uu___266_4983.failhard);
        nosynth = (uu___266_4983.nosynth);
        tc_term = (uu___266_4983.tc_term);
        type_of = (uu___266_4983.type_of);
        universe_of = (uu___266_4983.universe_of);
        use_bv_sorts = (uu___266_4983.use_bv_sorts);
        qname_and_index = (uu___266_4983.qname_and_index);
        proof_ns = (uu___266_4983.proof_ns);
        synth = (uu___266_4983.synth);
        is_native_tactic = (uu___266_4983.is_native_tactic);
        identifier_info = (uu___266_4983.identifier_info);
        tc_hooks = (uu___266_4983.tc_hooks);
        dsenv = (uu___266_4983.dsenv);
        dep_graph = (uu___266_4983.dep_graph)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4991  -> fun uu____4992  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___267_5002 = env in
      {
        solver = (uu___267_5002.solver);
        range = (uu___267_5002.range);
        curmodule = (uu___267_5002.curmodule);
        gamma = (uu___267_5002.gamma);
        gamma_cache = (uu___267_5002.gamma_cache);
        modules = (uu___267_5002.modules);
        expected_typ = (uu___267_5002.expected_typ);
        sigtab = (uu___267_5002.sigtab);
        is_pattern = (uu___267_5002.is_pattern);
        instantiate_imp = (uu___267_5002.instantiate_imp);
        effects = (uu___267_5002.effects);
        generalize = (uu___267_5002.generalize);
        letrecs = (uu___267_5002.letrecs);
        top_level = (uu___267_5002.top_level);
        check_uvars = (uu___267_5002.check_uvars);
        use_eq = (uu___267_5002.use_eq);
        is_iface = (uu___267_5002.is_iface);
        admit = (uu___267_5002.admit);
        lax = (uu___267_5002.lax);
        lax_universes = (uu___267_5002.lax_universes);
        failhard = (uu___267_5002.failhard);
        nosynth = (uu___267_5002.nosynth);
        tc_term = (uu___267_5002.tc_term);
        type_of = (uu___267_5002.type_of);
        universe_of = (uu___267_5002.universe_of);
        use_bv_sorts = (uu___267_5002.use_bv_sorts);
        qname_and_index = (uu___267_5002.qname_and_index);
        proof_ns = (uu___267_5002.proof_ns);
        synth = (uu___267_5002.synth);
        is_native_tactic = (uu___267_5002.is_native_tactic);
        identifier_info = (uu___267_5002.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___267_5002.dsenv);
        dep_graph = (uu___267_5002.dep_graph)
      }
let set_dep_graph: env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___268_5009 = e in
      {
        solver = (uu___268_5009.solver);
        range = (uu___268_5009.range);
        curmodule = (uu___268_5009.curmodule);
        gamma = (uu___268_5009.gamma);
        gamma_cache = (uu___268_5009.gamma_cache);
        modules = (uu___268_5009.modules);
        expected_typ = (uu___268_5009.expected_typ);
        sigtab = (uu___268_5009.sigtab);
        is_pattern = (uu___268_5009.is_pattern);
        instantiate_imp = (uu___268_5009.instantiate_imp);
        effects = (uu___268_5009.effects);
        generalize = (uu___268_5009.generalize);
        letrecs = (uu___268_5009.letrecs);
        top_level = (uu___268_5009.top_level);
        check_uvars = (uu___268_5009.check_uvars);
        use_eq = (uu___268_5009.use_eq);
        is_iface = (uu___268_5009.is_iface);
        admit = (uu___268_5009.admit);
        lax = (uu___268_5009.lax);
        lax_universes = (uu___268_5009.lax_universes);
        failhard = (uu___268_5009.failhard);
        nosynth = (uu___268_5009.nosynth);
        tc_term = (uu___268_5009.tc_term);
        type_of = (uu___268_5009.type_of);
        universe_of = (uu___268_5009.universe_of);
        use_bv_sorts = (uu___268_5009.use_bv_sorts);
        qname_and_index = (uu___268_5009.qname_and_index);
        proof_ns = (uu___268_5009.proof_ns);
        synth = (uu___268_5009.synth);
        is_native_tactic = (uu___268_5009.is_native_tactic);
        identifier_info = (uu___268_5009.identifier_info);
        tc_hooks = (uu___268_5009.tc_hooks);
        dsenv = (uu___268_5009.dsenv);
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
      | (NoDelta ,uu____5024) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5025,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5026,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5027 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5034 . Prims.unit -> 'Auu____5034 FStar_Util.smap =
  fun uu____5040  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5043 . Prims.unit -> 'Auu____5043 FStar_Util.smap =
  fun uu____5049  -> FStar_Util.smap_create (Prims.parse_int "100")
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
              let uu____5122 = new_gamma_cache () in
              let uu____5125 = new_sigtab () in
              let uu____5128 = FStar_Options.using_facts_from () in
              let uu____5129 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty in
              let uu____5132 = FStar_ToSyntax_Env.empty_env () in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5122;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5125;
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
                proof_ns = uu____5128;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5164  -> false);
                identifier_info = uu____5129;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5132;
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
  fun uu____5232  ->
    let uu____5233 = FStar_ST.op_Bang query_indices in
    match uu____5233 with
    | [] -> failwith "Empty query indices!"
    | uu____5310 ->
        let uu____5319 =
          let uu____5328 =
            let uu____5335 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5335 in
          let uu____5412 = FStar_ST.op_Bang query_indices in uu____5328 ::
            uu____5412 in
        FStar_ST.op_Colon_Equals query_indices uu____5319
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5553  ->
    let uu____5554 = FStar_ST.op_Bang query_indices in
    match uu____5554 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5721  ->
    match uu____5721 with
    | (l,n1) ->
        let uu____5728 = FStar_ST.op_Bang query_indices in
        (match uu____5728 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5893 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5910  ->
    let uu____5911 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5911
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6005 =
       let uu____6008 = FStar_ST.op_Bang stack in env :: uu____6008 in
     FStar_ST.op_Colon_Equals stack uu____6005);
    (let uu___269_6111 = env in
     let uu____6112 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6115 = FStar_Util.smap_copy (sigtab env) in
     let uu____6118 =
       let uu____6121 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6121 in
     {
       solver = (uu___269_6111.solver);
       range = (uu___269_6111.range);
       curmodule = (uu___269_6111.curmodule);
       gamma = (uu___269_6111.gamma);
       gamma_cache = uu____6112;
       modules = (uu___269_6111.modules);
       expected_typ = (uu___269_6111.expected_typ);
       sigtab = uu____6115;
       is_pattern = (uu___269_6111.is_pattern);
       instantiate_imp = (uu___269_6111.instantiate_imp);
       effects = (uu___269_6111.effects);
       generalize = (uu___269_6111.generalize);
       letrecs = (uu___269_6111.letrecs);
       top_level = (uu___269_6111.top_level);
       check_uvars = (uu___269_6111.check_uvars);
       use_eq = (uu___269_6111.use_eq);
       is_iface = (uu___269_6111.is_iface);
       admit = (uu___269_6111.admit);
       lax = (uu___269_6111.lax);
       lax_universes = (uu___269_6111.lax_universes);
       failhard = (uu___269_6111.failhard);
       nosynth = (uu___269_6111.nosynth);
       tc_term = (uu___269_6111.tc_term);
       type_of = (uu___269_6111.type_of);
       universe_of = (uu___269_6111.universe_of);
       use_bv_sorts = (uu___269_6111.use_bv_sorts);
       qname_and_index = (uu___269_6111.qname_and_index);
       proof_ns = (uu___269_6111.proof_ns);
       synth = (uu___269_6111.synth);
       is_native_tactic = (uu___269_6111.is_native_tactic);
       identifier_info = uu____6118;
       tc_hooks = (uu___269_6111.tc_hooks);
       dsenv = (uu___269_6111.dsenv);
       dep_graph = (uu___269_6111.dep_graph)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6184  ->
    let uu____6185 = FStar_ST.op_Bang stack in
    match uu____6185 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6293 -> failwith "Impossible: Too many pops"
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
        let uu____6332 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6358  ->
                  match uu____6358 with
                  | (m,uu____6364) -> FStar_Ident.lid_equals l m)) in
        (match uu____6332 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___270_6371 = env in
               {
                 solver = (uu___270_6371.solver);
                 range = (uu___270_6371.range);
                 curmodule = (uu___270_6371.curmodule);
                 gamma = (uu___270_6371.gamma);
                 gamma_cache = (uu___270_6371.gamma_cache);
                 modules = (uu___270_6371.modules);
                 expected_typ = (uu___270_6371.expected_typ);
                 sigtab = (uu___270_6371.sigtab);
                 is_pattern = (uu___270_6371.is_pattern);
                 instantiate_imp = (uu___270_6371.instantiate_imp);
                 effects = (uu___270_6371.effects);
                 generalize = (uu___270_6371.generalize);
                 letrecs = (uu___270_6371.letrecs);
                 top_level = (uu___270_6371.top_level);
                 check_uvars = (uu___270_6371.check_uvars);
                 use_eq = (uu___270_6371.use_eq);
                 is_iface = (uu___270_6371.is_iface);
                 admit = (uu___270_6371.admit);
                 lax = (uu___270_6371.lax);
                 lax_universes = (uu___270_6371.lax_universes);
                 failhard = (uu___270_6371.failhard);
                 nosynth = (uu___270_6371.nosynth);
                 tc_term = (uu___270_6371.tc_term);
                 type_of = (uu___270_6371.type_of);
                 universe_of = (uu___270_6371.universe_of);
                 use_bv_sorts = (uu___270_6371.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___270_6371.proof_ns);
                 synth = (uu___270_6371.synth);
                 is_native_tactic = (uu___270_6371.is_native_tactic);
                 identifier_info = (uu___270_6371.identifier_info);
                 tc_hooks = (uu___270_6371.tc_hooks);
                 dsenv = (uu___270_6371.dsenv);
                 dep_graph = (uu___270_6371.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6376,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___271_6384 = env in
               {
                 solver = (uu___271_6384.solver);
                 range = (uu___271_6384.range);
                 curmodule = (uu___271_6384.curmodule);
                 gamma = (uu___271_6384.gamma);
                 gamma_cache = (uu___271_6384.gamma_cache);
                 modules = (uu___271_6384.modules);
                 expected_typ = (uu___271_6384.expected_typ);
                 sigtab = (uu___271_6384.sigtab);
                 is_pattern = (uu___271_6384.is_pattern);
                 instantiate_imp = (uu___271_6384.instantiate_imp);
                 effects = (uu___271_6384.effects);
                 generalize = (uu___271_6384.generalize);
                 letrecs = (uu___271_6384.letrecs);
                 top_level = (uu___271_6384.top_level);
                 check_uvars = (uu___271_6384.check_uvars);
                 use_eq = (uu___271_6384.use_eq);
                 is_iface = (uu___271_6384.is_iface);
                 admit = (uu___271_6384.admit);
                 lax = (uu___271_6384.lax);
                 lax_universes = (uu___271_6384.lax_universes);
                 failhard = (uu___271_6384.failhard);
                 nosynth = (uu___271_6384.nosynth);
                 tc_term = (uu___271_6384.tc_term);
                 type_of = (uu___271_6384.type_of);
                 universe_of = (uu___271_6384.universe_of);
                 use_bv_sorts = (uu___271_6384.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___271_6384.proof_ns);
                 synth = (uu___271_6384.synth);
                 is_native_tactic = (uu___271_6384.is_native_tactic);
                 identifier_info = (uu___271_6384.identifier_info);
                 tc_hooks = (uu___271_6384.tc_hooks);
                 dsenv = (uu___271_6384.dsenv);
                 dep_graph = (uu___271_6384.dep_graph)
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
        (let uu___272_6402 = e in
         {
           solver = (uu___272_6402.solver);
           range = r;
           curmodule = (uu___272_6402.curmodule);
           gamma = (uu___272_6402.gamma);
           gamma_cache = (uu___272_6402.gamma_cache);
           modules = (uu___272_6402.modules);
           expected_typ = (uu___272_6402.expected_typ);
           sigtab = (uu___272_6402.sigtab);
           is_pattern = (uu___272_6402.is_pattern);
           instantiate_imp = (uu___272_6402.instantiate_imp);
           effects = (uu___272_6402.effects);
           generalize = (uu___272_6402.generalize);
           letrecs = (uu___272_6402.letrecs);
           top_level = (uu___272_6402.top_level);
           check_uvars = (uu___272_6402.check_uvars);
           use_eq = (uu___272_6402.use_eq);
           is_iface = (uu___272_6402.is_iface);
           admit = (uu___272_6402.admit);
           lax = (uu___272_6402.lax);
           lax_universes = (uu___272_6402.lax_universes);
           failhard = (uu___272_6402.failhard);
           nosynth = (uu___272_6402.nosynth);
           tc_term = (uu___272_6402.tc_term);
           type_of = (uu___272_6402.type_of);
           universe_of = (uu___272_6402.universe_of);
           use_bv_sorts = (uu___272_6402.use_bv_sorts);
           qname_and_index = (uu___272_6402.qname_and_index);
           proof_ns = (uu___272_6402.proof_ns);
           synth = (uu___272_6402.synth);
           is_native_tactic = (uu___272_6402.is_native_tactic);
           identifier_info = (uu___272_6402.identifier_info);
           tc_hooks = (uu___272_6402.tc_hooks);
           dsenv = (uu___272_6402.dsenv);
           dep_graph = (uu___272_6402.dep_graph)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6412 =
        let uu____6413 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6413 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6412
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6515 =
          let uu____6516 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6516 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6515
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6618 =
          let uu____6619 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6619 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6618
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6723 =
        let uu____6724 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6724 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6723
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___273_6831 = env in
      {
        solver = (uu___273_6831.solver);
        range = (uu___273_6831.range);
        curmodule = lid;
        gamma = (uu___273_6831.gamma);
        gamma_cache = (uu___273_6831.gamma_cache);
        modules = (uu___273_6831.modules);
        expected_typ = (uu___273_6831.expected_typ);
        sigtab = (uu___273_6831.sigtab);
        is_pattern = (uu___273_6831.is_pattern);
        instantiate_imp = (uu___273_6831.instantiate_imp);
        effects = (uu___273_6831.effects);
        generalize = (uu___273_6831.generalize);
        letrecs = (uu___273_6831.letrecs);
        top_level = (uu___273_6831.top_level);
        check_uvars = (uu___273_6831.check_uvars);
        use_eq = (uu___273_6831.use_eq);
        is_iface = (uu___273_6831.is_iface);
        admit = (uu___273_6831.admit);
        lax = (uu___273_6831.lax);
        lax_universes = (uu___273_6831.lax_universes);
        failhard = (uu___273_6831.failhard);
        nosynth = (uu___273_6831.nosynth);
        tc_term = (uu___273_6831.tc_term);
        type_of = (uu___273_6831.type_of);
        universe_of = (uu___273_6831.universe_of);
        use_bv_sorts = (uu___273_6831.use_bv_sorts);
        qname_and_index = (uu___273_6831.qname_and_index);
        proof_ns = (uu___273_6831.proof_ns);
        synth = (uu___273_6831.synth);
        is_native_tactic = (uu___273_6831.is_native_tactic);
        identifier_info = (uu___273_6831.identifier_info);
        tc_hooks = (uu___273_6831.tc_hooks);
        dsenv = (uu___273_6831.dsenv);
        dep_graph = (uu___273_6831.dep_graph)
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
    let uu____6857 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str in
    (FStar_Errors.NameNotFound, uu____6857)
let variable_not_found:
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____6865 =
      let uu____6866 = FStar_Syntax_Print.bv_to_string v1 in
      FStar_Util.format1 "Variable \"%s\" not found" uu____6866 in
    (FStar_Errors.VariableNotFound, uu____6865)
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6869  ->
    let uu____6870 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6870
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
      | ((formals,t),uu____6908) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6932 = FStar_Syntax_Subst.subst vs t in (us, uu____6932)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___252_6945  ->
    match uu___252_6945 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6969  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6982 = inst_tscheme t in
      match uu____6982 with
      | (us,t1) ->
          let uu____6993 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6993)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7005  ->
          match uu____7005 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7020 =
                         let uu____7021 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7022 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7023 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7024 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7021 uu____7022 uu____7023 uu____7024 in
                       failwith uu____7020)
                    else ();
                    (let uu____7026 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7026))
               | uu____7033 ->
                   let uu____7034 =
                     let uu____7035 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7035 in
                   failwith uu____7034)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7039 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7043 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7047 -> false
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
             | ([],uu____7081) -> Maybe
             | (uu____7088,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7107 -> No in
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
          let uu____7212 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7212 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___253_7257  ->
                   match uu___253_7257 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7300 =
                           let uu____7319 =
                             let uu____7334 = inst_tscheme t in
                             FStar_Util.Inl uu____7334 in
                           (uu____7319, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7300
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7400,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7402);
                                     FStar_Syntax_Syntax.sigrng = uu____7403;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7404;
                                     FStar_Syntax_Syntax.sigmeta = uu____7405;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7406;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7426 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7426
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7472 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7479 -> cache t in
                       let uu____7480 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7480 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7555 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7555 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7641 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7721 = find_in_sigtab env lid in
         match uu____7721 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7820) ->
          add_sigelts env ses
      | uu____7829 ->
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
            | uu____7843 -> ()))
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
        (fun uu___254_7870  ->
           match uu___254_7870 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7888 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7921,lb::[]),uu____7923) ->
          let uu____7936 =
            let uu____7945 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7954 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7945, uu____7954) in
          FStar_Pervasives_Native.Some uu____7936
      | FStar_Syntax_Syntax.Sig_let ((uu____7967,lbs),uu____7969) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8005 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8017 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8017
                   then
                     let uu____8028 =
                       let uu____8037 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8046 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8037, uu____8046) in
                     FStar_Pervasives_Native.Some uu____8028
                   else FStar_Pervasives_Native.None)
      | uu____8068 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8101 =
          let uu____8110 =
            let uu____8115 =
              let uu____8116 =
                let uu____8119 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8119 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8116) in
            inst_tscheme uu____8115 in
          (uu____8110, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8101
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8139,uu____8140) ->
        let uu____8145 =
          let uu____8154 =
            let uu____8159 =
              let uu____8160 =
                let uu____8163 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8163 in
              (us, uu____8160) in
            inst_tscheme uu____8159 in
          (uu____8154, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8145
    | uu____8180 -> FStar_Pervasives_Native.None
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
      let mapper uu____8238 =
        match uu____8238 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8334,uvs,t,uu____8337,uu____8338,uu____8339);
                    FStar_Syntax_Syntax.sigrng = uu____8340;
                    FStar_Syntax_Syntax.sigquals = uu____8341;
                    FStar_Syntax_Syntax.sigmeta = uu____8342;
                    FStar_Syntax_Syntax.sigattrs = uu____8343;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8364 =
                   let uu____8373 = inst_tscheme (uvs, t) in
                   (uu____8373, rng) in
                 FStar_Pervasives_Native.Some uu____8364
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8393;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8395;
                    FStar_Syntax_Syntax.sigattrs = uu____8396;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8413 =
                   let uu____8414 = in_cur_mod env l in uu____8414 = Yes in
                 if uu____8413
                 then
                   let uu____8425 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8425
                    then
                      let uu____8438 =
                        let uu____8447 = inst_tscheme (uvs, t) in
                        (uu____8447, rng) in
                      FStar_Pervasives_Native.Some uu____8438
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8474 =
                      let uu____8483 = inst_tscheme (uvs, t) in
                      (uu____8483, rng) in
                    FStar_Pervasives_Native.Some uu____8474)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8504,uu____8505);
                    FStar_Syntax_Syntax.sigrng = uu____8506;
                    FStar_Syntax_Syntax.sigquals = uu____8507;
                    FStar_Syntax_Syntax.sigmeta = uu____8508;
                    FStar_Syntax_Syntax.sigattrs = uu____8509;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8548 =
                        let uu____8557 = inst_tscheme (uvs, k) in
                        (uu____8557, rng) in
                      FStar_Pervasives_Native.Some uu____8548
                  | uu____8574 ->
                      let uu____8575 =
                        let uu____8584 =
                          let uu____8589 =
                            let uu____8590 =
                              let uu____8593 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8593 in
                            (uvs, uu____8590) in
                          inst_tscheme uu____8589 in
                        (uu____8584, rng) in
                      FStar_Pervasives_Native.Some uu____8575)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8614,uu____8615);
                    FStar_Syntax_Syntax.sigrng = uu____8616;
                    FStar_Syntax_Syntax.sigquals = uu____8617;
                    FStar_Syntax_Syntax.sigmeta = uu____8618;
                    FStar_Syntax_Syntax.sigattrs = uu____8619;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8659 =
                        let uu____8668 = inst_tscheme_with (uvs, k) us in
                        (uu____8668, rng) in
                      FStar_Pervasives_Native.Some uu____8659
                  | uu____8685 ->
                      let uu____8686 =
                        let uu____8695 =
                          let uu____8700 =
                            let uu____8701 =
                              let uu____8704 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8704 in
                            (uvs, uu____8701) in
                          inst_tscheme_with uu____8700 us in
                        (uu____8695, rng) in
                      FStar_Pervasives_Native.Some uu____8686)
             | FStar_Util.Inr se ->
                 let uu____8738 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8759;
                        FStar_Syntax_Syntax.sigrng = uu____8760;
                        FStar_Syntax_Syntax.sigquals = uu____8761;
                        FStar_Syntax_Syntax.sigmeta = uu____8762;
                        FStar_Syntax_Syntax.sigattrs = uu____8763;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8778 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8738
                   (FStar_Util.map_option
                      (fun uu____8826  ->
                         match uu____8826 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8857 =
        let uu____8868 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8868 mapper in
      match uu____8857 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___274_8961 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___274_8961.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___274_8961.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8986 = lookup_qname env l in
      match uu____8986 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9025 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9073 = try_lookup_bv env bv in
      match uu____9073 with
      | FStar_Pervasives_Native.None  ->
          let uu____9088 = variable_not_found bv in
          FStar_Errors.raise_error uu____9088 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9103 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9104 =
            let uu____9105 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9105 in
          (uu____9103, uu____9104)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9122 = try_lookup_lid_aux env l in
      match uu____9122 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9188 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9188 in
          let uu____9189 =
            let uu____9198 =
              let uu____9203 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9203) in
            (uu____9198, r1) in
          FStar_Pervasives_Native.Some uu____9189
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9230 = try_lookup_lid env l in
      match uu____9230 with
      | FStar_Pervasives_Native.None  ->
          let uu____9257 = name_not_found l in
          FStar_Errors.raise_error uu____9257 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___255_9297  ->
              match uu___255_9297 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9299 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9314 = lookup_qname env lid in
      match uu____9314 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9343,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9346;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9348;
              FStar_Syntax_Syntax.sigattrs = uu____9349;_},FStar_Pervasives_Native.None
            ),uu____9350)
          ->
          let uu____9399 =
            let uu____9410 =
              let uu____9415 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9415) in
            (uu____9410, q) in
          FStar_Pervasives_Native.Some uu____9399
      | uu____9432 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9469 = lookup_qname env lid in
      match uu____9469 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9494,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9497;
              FStar_Syntax_Syntax.sigquals = uu____9498;
              FStar_Syntax_Syntax.sigmeta = uu____9499;
              FStar_Syntax_Syntax.sigattrs = uu____9500;_},FStar_Pervasives_Native.None
            ),uu____9501)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9550 ->
          let uu____9571 = name_not_found lid in
          FStar_Errors.raise_error uu____9571 (FStar_Ident.range_of_lid lid)
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9590 = lookup_qname env lid in
      match uu____9590 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9615,uvs,t,uu____9618,uu____9619,uu____9620);
              FStar_Syntax_Syntax.sigrng = uu____9621;
              FStar_Syntax_Syntax.sigquals = uu____9622;
              FStar_Syntax_Syntax.sigmeta = uu____9623;
              FStar_Syntax_Syntax.sigattrs = uu____9624;_},FStar_Pervasives_Native.None
            ),uu____9625)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9678 ->
          let uu____9699 = name_not_found lid in
          FStar_Errors.raise_error uu____9699 (FStar_Ident.range_of_lid lid)
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9720 = lookup_qname env lid in
      match uu____9720 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9747,uu____9748,uu____9749,uu____9750,uu____9751,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9753;
              FStar_Syntax_Syntax.sigquals = uu____9754;
              FStar_Syntax_Syntax.sigmeta = uu____9755;
              FStar_Syntax_Syntax.sigattrs = uu____9756;_},uu____9757),uu____9758)
          -> (true, dcs)
      | uu____9819 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9848 = lookup_qname env lid in
      match uu____9848 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9869,uu____9870,uu____9871,l,uu____9873,uu____9874);
              FStar_Syntax_Syntax.sigrng = uu____9875;
              FStar_Syntax_Syntax.sigquals = uu____9876;
              FStar_Syntax_Syntax.sigmeta = uu____9877;
              FStar_Syntax_Syntax.sigattrs = uu____9878;_},uu____9879),uu____9880)
          -> l
      | uu____9935 ->
          let uu____9956 =
            let uu____9957 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9957 in
          failwith uu____9956
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
        let uu____9991 = lookup_qname env lid in
        match uu____9991 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10019)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10070,lbs),uu____10072)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10100 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10100
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10132 -> FStar_Pervasives_Native.None)
        | uu____10137 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10172 = lookup_qname env ftv in
      match uu____10172 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10196) ->
          let uu____10241 = effect_signature se in
          (match uu____10241 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10262,t),r) ->
               let uu____10277 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10277)
      | uu____10278 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10305 = try_lookup_effect_lid env ftv in
      match uu____10305 with
      | FStar_Pervasives_Native.None  ->
          let uu____10308 = name_not_found ftv in
          FStar_Errors.raise_error uu____10308 (FStar_Ident.range_of_lid ftv)
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
        let uu____10329 = lookup_qname env lid0 in
        match uu____10329 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10360);
                FStar_Syntax_Syntax.sigrng = uu____10361;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10363;
                FStar_Syntax_Syntax.sigattrs = uu____10364;_},FStar_Pervasives_Native.None
              ),uu____10365)
            ->
            let lid1 =
              let uu____10419 =
                let uu____10420 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10420 in
              FStar_Ident.set_lid_range lid uu____10419 in
            let uu____10421 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___256_10425  ->
                      match uu___256_10425 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10426 -> false)) in
            if uu____10421
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10440 =
                      let uu____10441 =
                        let uu____10442 = get_range env in
                        FStar_Range.string_of_range uu____10442 in
                      let uu____10443 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10444 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10441 uu____10443 uu____10444 in
                    failwith uu____10440) in
               match (binders, univs1) with
               | ([],uu____10451) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10468,uu____10469::uu____10470::uu____10471) ->
                   let uu____10476 =
                     let uu____10477 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10478 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10477 uu____10478 in
                   failwith uu____10476
               | uu____10485 ->
                   let uu____10490 =
                     let uu____10495 =
                       let uu____10496 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10496) in
                     inst_tscheme_with uu____10495 insts in
                   (match uu____10490 with
                    | (uu____10507,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10510 =
                          let uu____10511 = FStar_Syntax_Subst.compress t1 in
                          uu____10511.FStar_Syntax_Syntax.n in
                        (match uu____10510 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10558 -> failwith "Impossible")))
        | uu____10565 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10605 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10605 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10618,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10625 = find1 l2 in
            (match uu____10625 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10632 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10632 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10636 = find1 l in
            (match uu____10636 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10650 = lookup_qname env l1 in
      match uu____10650 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10673;
              FStar_Syntax_Syntax.sigrng = uu____10674;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10676;
              FStar_Syntax_Syntax.sigattrs = uu____10677;_},uu____10678),uu____10679)
          -> q
      | uu____10730 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10763 =
          let uu____10764 =
            let uu____10765 = FStar_Util.string_of_int i in
            let uu____10766 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10765 uu____10766 in
          failwith uu____10764 in
        let uu____10767 = lookup_datacon env lid in
        match uu____10767 with
        | (uu____10772,t) ->
            let uu____10774 =
              let uu____10775 = FStar_Syntax_Subst.compress t in
              uu____10775.FStar_Syntax_Syntax.n in
            (match uu____10774 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10779) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10810 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10810
                      FStar_Pervasives_Native.fst)
             | uu____10819 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10826 = lookup_qname env l in
      match uu____10826 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10847,uu____10848,uu____10849);
              FStar_Syntax_Syntax.sigrng = uu____10850;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10852;
              FStar_Syntax_Syntax.sigattrs = uu____10853;_},uu____10854),uu____10855)
          ->
          FStar_Util.for_some
            (fun uu___257_10908  ->
               match uu___257_10908 with
               | FStar_Syntax_Syntax.Projector uu____10909 -> true
               | uu____10914 -> false) quals
      | uu____10915 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10942 = lookup_qname env lid in
      match uu____10942 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10963,uu____10964,uu____10965,uu____10966,uu____10967,uu____10968);
              FStar_Syntax_Syntax.sigrng = uu____10969;
              FStar_Syntax_Syntax.sigquals = uu____10970;
              FStar_Syntax_Syntax.sigmeta = uu____10971;
              FStar_Syntax_Syntax.sigattrs = uu____10972;_},uu____10973),uu____10974)
          -> true
      | uu____11029 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11056 = lookup_qname env lid in
      match uu____11056 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11077,uu____11078,uu____11079,uu____11080,uu____11081,uu____11082);
              FStar_Syntax_Syntax.sigrng = uu____11083;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11085;
              FStar_Syntax_Syntax.sigattrs = uu____11086;_},uu____11087),uu____11088)
          ->
          FStar_Util.for_some
            (fun uu___258_11149  ->
               match uu___258_11149 with
               | FStar_Syntax_Syntax.RecordType uu____11150 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11159 -> true
               | uu____11168 -> false) quals
      | uu____11169 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11196 = lookup_qname env lid in
      match uu____11196 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11217,uu____11218);
              FStar_Syntax_Syntax.sigrng = uu____11219;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11221;
              FStar_Syntax_Syntax.sigattrs = uu____11222;_},uu____11223),uu____11224)
          ->
          FStar_Util.for_some
            (fun uu___259_11281  ->
               match uu___259_11281 with
               | FStar_Syntax_Syntax.Action uu____11282 -> true
               | uu____11283 -> false) quals
      | uu____11284 -> false
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
      let uu____11314 =
        let uu____11315 = FStar_Syntax_Util.un_uinst head1 in
        uu____11315.FStar_Syntax_Syntax.n in
      match uu____11314 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11319 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11384 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11400) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11417 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11424 ->
                 FStar_Pervasives_Native.Some true
             | uu____11441 -> FStar_Pervasives_Native.Some false) in
      let uu____11442 =
        let uu____11445 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11445 mapper in
      match uu____11442 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11491 = lookup_qname env lid in
      match uu____11491 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11512,uu____11513,tps,uu____11515,uu____11516,uu____11517);
              FStar_Syntax_Syntax.sigrng = uu____11518;
              FStar_Syntax_Syntax.sigquals = uu____11519;
              FStar_Syntax_Syntax.sigmeta = uu____11520;
              FStar_Syntax_Syntax.sigattrs = uu____11521;_},uu____11522),uu____11523)
          -> FStar_List.length tps
      | uu____11586 ->
          let uu____11607 = name_not_found lid in
          FStar_Errors.raise_error uu____11607 (FStar_Ident.range_of_lid lid)
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
           (fun uu____11651  ->
              match uu____11651 with
              | (d,uu____11659) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11670 = effect_decl_opt env l in
      match uu____11670 with
      | FStar_Pervasives_Native.None  ->
          let uu____11685 = name_not_found l in
          FStar_Errors.raise_error uu____11685 (FStar_Ident.range_of_lid l)
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
            (let uu____11752 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11805  ->
                       match uu____11805 with
                       | (m1,m2,uu____11818,uu____11819,uu____11820) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11752 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11837 =
                   let uu____11842 =
                     let uu____11843 = FStar_Syntax_Print.lid_to_string l1 in
                     let uu____11844 = FStar_Syntax_Print.lid_to_string l2 in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11843
                       uu____11844 in
                   (FStar_Errors.EffectsCannotBeComposed, uu____11842) in
                 FStar_Errors.raise_error uu____11837 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11851,uu____11852,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11889 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11889)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11916 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11942  ->
                match uu____11942 with
                | (d,uu____11948) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11916 with
      | FStar_Pervasives_Native.None  ->
          let uu____11959 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11959
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11972 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11972 with
           | (uu____11983,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11993)::(wp,uu____11995)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12031 -> failwith "Impossible"))
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
                 let uu____12074 = get_range env in
                 let uu____12075 =
                   let uu____12078 =
                     let uu____12079 =
                       let uu____12094 =
                         let uu____12097 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12097] in
                       (null_wp, uu____12094) in
                     FStar_Syntax_Syntax.Tm_app uu____12079 in
                   FStar_Syntax_Syntax.mk uu____12078 in
                 uu____12075 FStar_Pervasives_Native.None uu____12074 in
               let uu____12103 =
                 let uu____12104 =
                   let uu____12113 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12113] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12104;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12103)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___275_12122 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___275_12122.order);
              joins = (uu___275_12122.joins)
            } in
          let uu___276_12131 = env in
          {
            solver = (uu___276_12131.solver);
            range = (uu___276_12131.range);
            curmodule = (uu___276_12131.curmodule);
            gamma = (uu___276_12131.gamma);
            gamma_cache = (uu___276_12131.gamma_cache);
            modules = (uu___276_12131.modules);
            expected_typ = (uu___276_12131.expected_typ);
            sigtab = (uu___276_12131.sigtab);
            is_pattern = (uu___276_12131.is_pattern);
            instantiate_imp = (uu___276_12131.instantiate_imp);
            effects;
            generalize = (uu___276_12131.generalize);
            letrecs = (uu___276_12131.letrecs);
            top_level = (uu___276_12131.top_level);
            check_uvars = (uu___276_12131.check_uvars);
            use_eq = (uu___276_12131.use_eq);
            is_iface = (uu___276_12131.is_iface);
            admit = (uu___276_12131.admit);
            lax = (uu___276_12131.lax);
            lax_universes = (uu___276_12131.lax_universes);
            failhard = (uu___276_12131.failhard);
            nosynth = (uu___276_12131.nosynth);
            tc_term = (uu___276_12131.tc_term);
            type_of = (uu___276_12131.type_of);
            universe_of = (uu___276_12131.universe_of);
            use_bv_sorts = (uu___276_12131.use_bv_sorts);
            qname_and_index = (uu___276_12131.qname_and_index);
            proof_ns = (uu___276_12131.proof_ns);
            synth = (uu___276_12131.synth);
            is_native_tactic = (uu___276_12131.is_native_tactic);
            identifier_info = (uu___276_12131.identifier_info);
            tc_hooks = (uu___276_12131.tc_hooks);
            dsenv = (uu___276_12131.dsenv);
            dep_graph = (uu___276_12131.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12148 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12148 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12238 = (e1.mlift).mlift_wp t wp in
                              let uu____12239 = l1 t wp e in
                              l2 t uu____12238 uu____12239))
                | uu____12240 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12279 = inst_tscheme lift_t in
            match uu____12279 with
            | (uu____12286,lift_t1) ->
                let uu____12288 =
                  let uu____12291 =
                    let uu____12292 =
                      let uu____12307 =
                        let uu____12310 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12311 =
                          let uu____12314 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12314] in
                        uu____12310 :: uu____12311 in
                      (lift_t1, uu____12307) in
                    FStar_Syntax_Syntax.Tm_app uu____12292 in
                  FStar_Syntax_Syntax.mk uu____12291 in
                uu____12288 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
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
                          let uu____12391 =
                            let uu____12394 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12394] in
                          uu____12390 :: uu____12391 in
                        uu____12386 :: uu____12387 in
                      (lift_t1, uu____12383) in
                    FStar_Syntax_Syntax.Tm_app uu____12368 in
                  FStar_Syntax_Syntax.mk uu____12367 in
                uu____12364 FStar_Pervasives_Native.None
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
              let uu____12432 =
                let uu____12433 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12433
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12432 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12437 =
              let uu____12438 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12438 in
            let uu____12439 =
              let uu____12440 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12458 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12458) in
              FStar_Util.dflt "none" uu____12440 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12437
              uu____12439 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12484  ->
                    match uu____12484 with
                    | (e,uu____12492) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12511 =
            match uu____12511 with
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
              let uu____12549 =
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
                                    (let uu____12570 =
                                       let uu____12579 =
                                         find_edge order1 (i, k) in
                                       let uu____12582 =
                                         find_edge order1 (k, j) in
                                       (uu____12579, uu____12582) in
                                     match uu____12570 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12597 =
                                           compose_edges e1 e2 in
                                         [uu____12597]
                                     | uu____12598 -> []))))) in
              FStar_List.append order1 uu____12549 in
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
                   let uu____12628 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12630 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12630
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12628
                   then
                     let uu____12635 =
                       let uu____12640 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str in
                       (FStar_Errors.DivergentComputationCannotBeIncludedInTotal,
                         uu____12640) in
                     let uu____12641 = get_range env in
                     FStar_Errors.raise_error uu____12635 uu____12641
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
                                            let uu____12766 =
                                              let uu____12775 =
                                                find_edge order2 (i, k) in
                                              let uu____12778 =
                                                find_edge order2 (j, k) in
                                              (uu____12775, uu____12778) in
                                            match uu____12766 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12820,uu____12821)
                                                     ->
                                                     let uu____12828 =
                                                       let uu____12833 =
                                                         let uu____12834 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12834 in
                                                       let uu____12837 =
                                                         let uu____12838 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12838 in
                                                       (uu____12833,
                                                         uu____12837) in
                                                     (match uu____12828 with
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
                                            | uu____12873 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___277_12946 = env.effects in
              { decls = (uu___277_12946.decls); order = order2; joins } in
            let uu___278_12947 = env in
            {
              solver = (uu___278_12947.solver);
              range = (uu___278_12947.range);
              curmodule = (uu___278_12947.curmodule);
              gamma = (uu___278_12947.gamma);
              gamma_cache = (uu___278_12947.gamma_cache);
              modules = (uu___278_12947.modules);
              expected_typ = (uu___278_12947.expected_typ);
              sigtab = (uu___278_12947.sigtab);
              is_pattern = (uu___278_12947.is_pattern);
              instantiate_imp = (uu___278_12947.instantiate_imp);
              effects;
              generalize = (uu___278_12947.generalize);
              letrecs = (uu___278_12947.letrecs);
              top_level = (uu___278_12947.top_level);
              check_uvars = (uu___278_12947.check_uvars);
              use_eq = (uu___278_12947.use_eq);
              is_iface = (uu___278_12947.is_iface);
              admit = (uu___278_12947.admit);
              lax = (uu___278_12947.lax);
              lax_universes = (uu___278_12947.lax_universes);
              failhard = (uu___278_12947.failhard);
              nosynth = (uu___278_12947.nosynth);
              tc_term = (uu___278_12947.tc_term);
              type_of = (uu___278_12947.type_of);
              universe_of = (uu___278_12947.universe_of);
              use_bv_sorts = (uu___278_12947.use_bv_sorts);
              qname_and_index = (uu___278_12947.qname_and_index);
              proof_ns = (uu___278_12947.proof_ns);
              synth = (uu___278_12947.synth);
              is_native_tactic = (uu___278_12947.is_native_tactic);
              identifier_info = (uu___278_12947.identifier_info);
              tc_hooks = (uu___278_12947.tc_hooks);
              dsenv = (uu___278_12947.dsenv);
              dep_graph = (uu___278_12947.dep_graph)
            }))
      | uu____12948 -> env
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
        | uu____12972 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12980 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12980 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12997 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12997 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13015 =
                     let uu____13020 =
                       let uu____13021 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____13026 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1")) in
                       let uu____13033 =
                         let uu____13034 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____13034 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____13021 uu____13026 uu____13033 in
                     (FStar_Errors.ConstructorArgLengthMismatch, uu____13020) in
                   FStar_Errors.raise_error uu____13015
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____13039 =
                     let uu____13048 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13048 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13065  ->
                        fun uu____13066  ->
                          match (uu____13065, uu____13066) with
                          | ((x,uu____13088),(t,uu____13090)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13039 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13109 =
                     let uu___279_13110 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___279_13110.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___279_13110.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___279_13110.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___279_13110.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13109
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
          let uu____13132 = effect_decl_opt env effect_name in
          match uu____13132 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13165 =
                only_reifiable &&
                  (let uu____13167 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13167) in
              if uu____13165
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13183 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13202 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13231 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13231
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13232 = get_range env in
                           FStar_Errors.raise_error
                             (FStar_Errors.NotEnoughArgumentsForEffect,
                               message) uu____13232 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13242 =
                       let uu____13245 = get_range env in
                       let uu____13246 =
                         let uu____13249 =
                           let uu____13250 =
                             let uu____13265 =
                               let uu____13268 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13268; wp] in
                             (repr, uu____13265) in
                           FStar_Syntax_Syntax.Tm_app uu____13250 in
                         FStar_Syntax_Syntax.mk uu____13249 in
                       uu____13246 FStar_Pervasives_Native.None uu____13245 in
                     FStar_Pervasives_Native.Some uu____13242)
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
          let uu____13314 =
            let uu____13319 =
              let uu____13320 = FStar_Ident.string_of_lid l in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13320 in
            (FStar_Errors.EffectCannotBeReified, uu____13319) in
          let uu____13321 = get_range env in
          FStar_Errors.raise_error uu____13314 uu____13321 in
        let uu____13322 = effect_repr_aux true env c u_c in
        match uu____13322 with
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
      | uu____13356 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13363 =
        let uu____13364 = FStar_Syntax_Subst.compress t in
        uu____13364.FStar_Syntax_Syntax.n in
      match uu____13363 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13367,c) ->
          is_reifiable_comp env c
      | uu____13385 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13407)::uu____13408 -> x :: rest
        | (Binding_sig_inst uu____13417)::uu____13418 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13433 = push1 x rest1 in local :: uu____13433 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___280_13437 = env in
       let uu____13438 = push1 s env.gamma in
       {
         solver = (uu___280_13437.solver);
         range = (uu___280_13437.range);
         curmodule = (uu___280_13437.curmodule);
         gamma = uu____13438;
         gamma_cache = (uu___280_13437.gamma_cache);
         modules = (uu___280_13437.modules);
         expected_typ = (uu___280_13437.expected_typ);
         sigtab = (uu___280_13437.sigtab);
         is_pattern = (uu___280_13437.is_pattern);
         instantiate_imp = (uu___280_13437.instantiate_imp);
         effects = (uu___280_13437.effects);
         generalize = (uu___280_13437.generalize);
         letrecs = (uu___280_13437.letrecs);
         top_level = (uu___280_13437.top_level);
         check_uvars = (uu___280_13437.check_uvars);
         use_eq = (uu___280_13437.use_eq);
         is_iface = (uu___280_13437.is_iface);
         admit = (uu___280_13437.admit);
         lax = (uu___280_13437.lax);
         lax_universes = (uu___280_13437.lax_universes);
         failhard = (uu___280_13437.failhard);
         nosynth = (uu___280_13437.nosynth);
         tc_term = (uu___280_13437.tc_term);
         type_of = (uu___280_13437.type_of);
         universe_of = (uu___280_13437.universe_of);
         use_bv_sorts = (uu___280_13437.use_bv_sorts);
         qname_and_index = (uu___280_13437.qname_and_index);
         proof_ns = (uu___280_13437.proof_ns);
         synth = (uu___280_13437.synth);
         is_native_tactic = (uu___280_13437.is_native_tactic);
         identifier_info = (uu___280_13437.identifier_info);
         tc_hooks = (uu___280_13437.tc_hooks);
         dsenv = (uu___280_13437.dsenv);
         dep_graph = (uu___280_13437.dep_graph)
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
      let uu___281_13468 = env in
      {
        solver = (uu___281_13468.solver);
        range = (uu___281_13468.range);
        curmodule = (uu___281_13468.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___281_13468.gamma_cache);
        modules = (uu___281_13468.modules);
        expected_typ = (uu___281_13468.expected_typ);
        sigtab = (uu___281_13468.sigtab);
        is_pattern = (uu___281_13468.is_pattern);
        instantiate_imp = (uu___281_13468.instantiate_imp);
        effects = (uu___281_13468.effects);
        generalize = (uu___281_13468.generalize);
        letrecs = (uu___281_13468.letrecs);
        top_level = (uu___281_13468.top_level);
        check_uvars = (uu___281_13468.check_uvars);
        use_eq = (uu___281_13468.use_eq);
        is_iface = (uu___281_13468.is_iface);
        admit = (uu___281_13468.admit);
        lax = (uu___281_13468.lax);
        lax_universes = (uu___281_13468.lax_universes);
        failhard = (uu___281_13468.failhard);
        nosynth = (uu___281_13468.nosynth);
        tc_term = (uu___281_13468.tc_term);
        type_of = (uu___281_13468.type_of);
        universe_of = (uu___281_13468.universe_of);
        use_bv_sorts = (uu___281_13468.use_bv_sorts);
        qname_and_index = (uu___281_13468.qname_and_index);
        proof_ns = (uu___281_13468.proof_ns);
        synth = (uu___281_13468.synth);
        is_native_tactic = (uu___281_13468.is_native_tactic);
        identifier_info = (uu___281_13468.identifier_info);
        tc_hooks = (uu___281_13468.tc_hooks);
        dsenv = (uu___281_13468.dsenv);
        dep_graph = (uu___281_13468.dep_graph)
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
            (let uu___282_13499 = env in
             {
               solver = (uu___282_13499.solver);
               range = (uu___282_13499.range);
               curmodule = (uu___282_13499.curmodule);
               gamma = rest;
               gamma_cache = (uu___282_13499.gamma_cache);
               modules = (uu___282_13499.modules);
               expected_typ = (uu___282_13499.expected_typ);
               sigtab = (uu___282_13499.sigtab);
               is_pattern = (uu___282_13499.is_pattern);
               instantiate_imp = (uu___282_13499.instantiate_imp);
               effects = (uu___282_13499.effects);
               generalize = (uu___282_13499.generalize);
               letrecs = (uu___282_13499.letrecs);
               top_level = (uu___282_13499.top_level);
               check_uvars = (uu___282_13499.check_uvars);
               use_eq = (uu___282_13499.use_eq);
               is_iface = (uu___282_13499.is_iface);
               admit = (uu___282_13499.admit);
               lax = (uu___282_13499.lax);
               lax_universes = (uu___282_13499.lax_universes);
               failhard = (uu___282_13499.failhard);
               nosynth = (uu___282_13499.nosynth);
               tc_term = (uu___282_13499.tc_term);
               type_of = (uu___282_13499.type_of);
               universe_of = (uu___282_13499.universe_of);
               use_bv_sorts = (uu___282_13499.use_bv_sorts);
               qname_and_index = (uu___282_13499.qname_and_index);
               proof_ns = (uu___282_13499.proof_ns);
               synth = (uu___282_13499.synth);
               is_native_tactic = (uu___282_13499.is_native_tactic);
               identifier_info = (uu___282_13499.identifier_info);
               tc_hooks = (uu___282_13499.tc_hooks);
               dsenv = (uu___282_13499.dsenv);
               dep_graph = (uu___282_13499.dep_graph)
             }))
    | uu____13500 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13522  ->
             match uu____13522 with | (x,uu____13528) -> push_bv env1 x) env
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
            let uu___283_13556 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___283_13556.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___283_13556.FStar_Syntax_Syntax.index);
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
      (let uu___284_13586 = env in
       {
         solver = (uu___284_13586.solver);
         range = (uu___284_13586.range);
         curmodule = (uu___284_13586.curmodule);
         gamma = [];
         gamma_cache = (uu___284_13586.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___284_13586.sigtab);
         is_pattern = (uu___284_13586.is_pattern);
         instantiate_imp = (uu___284_13586.instantiate_imp);
         effects = (uu___284_13586.effects);
         generalize = (uu___284_13586.generalize);
         letrecs = (uu___284_13586.letrecs);
         top_level = (uu___284_13586.top_level);
         check_uvars = (uu___284_13586.check_uvars);
         use_eq = (uu___284_13586.use_eq);
         is_iface = (uu___284_13586.is_iface);
         admit = (uu___284_13586.admit);
         lax = (uu___284_13586.lax);
         lax_universes = (uu___284_13586.lax_universes);
         failhard = (uu___284_13586.failhard);
         nosynth = (uu___284_13586.nosynth);
         tc_term = (uu___284_13586.tc_term);
         type_of = (uu___284_13586.type_of);
         universe_of = (uu___284_13586.universe_of);
         use_bv_sorts = (uu___284_13586.use_bv_sorts);
         qname_and_index = (uu___284_13586.qname_and_index);
         proof_ns = (uu___284_13586.proof_ns);
         synth = (uu___284_13586.synth);
         is_native_tactic = (uu___284_13586.is_native_tactic);
         identifier_info = (uu___284_13586.identifier_info);
         tc_hooks = (uu___284_13586.tc_hooks);
         dsenv = (uu___284_13586.dsenv);
         dep_graph = (uu___284_13586.dep_graph)
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
        let uu____13618 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13618 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13646 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13646)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___285_13659 = env in
      {
        solver = (uu___285_13659.solver);
        range = (uu___285_13659.range);
        curmodule = (uu___285_13659.curmodule);
        gamma = (uu___285_13659.gamma);
        gamma_cache = (uu___285_13659.gamma_cache);
        modules = (uu___285_13659.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___285_13659.sigtab);
        is_pattern = (uu___285_13659.is_pattern);
        instantiate_imp = (uu___285_13659.instantiate_imp);
        effects = (uu___285_13659.effects);
        generalize = (uu___285_13659.generalize);
        letrecs = (uu___285_13659.letrecs);
        top_level = (uu___285_13659.top_level);
        check_uvars = (uu___285_13659.check_uvars);
        use_eq = false;
        is_iface = (uu___285_13659.is_iface);
        admit = (uu___285_13659.admit);
        lax = (uu___285_13659.lax);
        lax_universes = (uu___285_13659.lax_universes);
        failhard = (uu___285_13659.failhard);
        nosynth = (uu___285_13659.nosynth);
        tc_term = (uu___285_13659.tc_term);
        type_of = (uu___285_13659.type_of);
        universe_of = (uu___285_13659.universe_of);
        use_bv_sorts = (uu___285_13659.use_bv_sorts);
        qname_and_index = (uu___285_13659.qname_and_index);
        proof_ns = (uu___285_13659.proof_ns);
        synth = (uu___285_13659.synth);
        is_native_tactic = (uu___285_13659.is_native_tactic);
        identifier_info = (uu___285_13659.identifier_info);
        tc_hooks = (uu___285_13659.tc_hooks);
        dsenv = (uu___285_13659.dsenv);
        dep_graph = (uu___285_13659.dep_graph)
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
    let uu____13683 = expected_typ env_ in
    ((let uu___286_13689 = env_ in
      {
        solver = (uu___286_13689.solver);
        range = (uu___286_13689.range);
        curmodule = (uu___286_13689.curmodule);
        gamma = (uu___286_13689.gamma);
        gamma_cache = (uu___286_13689.gamma_cache);
        modules = (uu___286_13689.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___286_13689.sigtab);
        is_pattern = (uu___286_13689.is_pattern);
        instantiate_imp = (uu___286_13689.instantiate_imp);
        effects = (uu___286_13689.effects);
        generalize = (uu___286_13689.generalize);
        letrecs = (uu___286_13689.letrecs);
        top_level = (uu___286_13689.top_level);
        check_uvars = (uu___286_13689.check_uvars);
        use_eq = false;
        is_iface = (uu___286_13689.is_iface);
        admit = (uu___286_13689.admit);
        lax = (uu___286_13689.lax);
        lax_universes = (uu___286_13689.lax_universes);
        failhard = (uu___286_13689.failhard);
        nosynth = (uu___286_13689.nosynth);
        tc_term = (uu___286_13689.tc_term);
        type_of = (uu___286_13689.type_of);
        universe_of = (uu___286_13689.universe_of);
        use_bv_sorts = (uu___286_13689.use_bv_sorts);
        qname_and_index = (uu___286_13689.qname_and_index);
        proof_ns = (uu___286_13689.proof_ns);
        synth = (uu___286_13689.synth);
        is_native_tactic = (uu___286_13689.is_native_tactic);
        identifier_info = (uu___286_13689.identifier_info);
        tc_hooks = (uu___286_13689.tc_hooks);
        dsenv = (uu___286_13689.dsenv);
        dep_graph = (uu___286_13689.dep_graph)
      }), uu____13683)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13702 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___260_13712  ->
                    match uu___260_13712 with
                    | Binding_sig (uu____13715,se) -> [se]
                    | uu____13721 -> [])) in
          FStar_All.pipe_right uu____13702 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___287_13728 = env in
       {
         solver = (uu___287_13728.solver);
         range = (uu___287_13728.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___287_13728.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___287_13728.expected_typ);
         sigtab = (uu___287_13728.sigtab);
         is_pattern = (uu___287_13728.is_pattern);
         instantiate_imp = (uu___287_13728.instantiate_imp);
         effects = (uu___287_13728.effects);
         generalize = (uu___287_13728.generalize);
         letrecs = (uu___287_13728.letrecs);
         top_level = (uu___287_13728.top_level);
         check_uvars = (uu___287_13728.check_uvars);
         use_eq = (uu___287_13728.use_eq);
         is_iface = (uu___287_13728.is_iface);
         admit = (uu___287_13728.admit);
         lax = (uu___287_13728.lax);
         lax_universes = (uu___287_13728.lax_universes);
         failhard = (uu___287_13728.failhard);
         nosynth = (uu___287_13728.nosynth);
         tc_term = (uu___287_13728.tc_term);
         type_of = (uu___287_13728.type_of);
         universe_of = (uu___287_13728.universe_of);
         use_bv_sorts = (uu___287_13728.use_bv_sorts);
         qname_and_index = (uu___287_13728.qname_and_index);
         proof_ns = (uu___287_13728.proof_ns);
         synth = (uu___287_13728.synth);
         is_native_tactic = (uu___287_13728.is_native_tactic);
         identifier_info = (uu___287_13728.identifier_info);
         tc_hooks = (uu___287_13728.tc_hooks);
         dsenv = (uu___287_13728.dsenv);
         dep_graph = (uu___287_13728.dep_graph)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13809)::tl1 -> aux out tl1
      | (Binding_lid (uu____13813,(uu____13814,t)))::tl1 ->
          let uu____13829 =
            let uu____13836 = FStar_Syntax_Free.uvars t in
            ext out uu____13836 in
          aux uu____13829 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13843;
            FStar_Syntax_Syntax.index = uu____13844;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13851 =
            let uu____13858 = FStar_Syntax_Free.uvars t in
            ext out uu____13858 in
          aux uu____13851 tl1
      | (Binding_sig uu____13865)::uu____13866 -> out
      | (Binding_sig_inst uu____13875)::uu____13876 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13931)::tl1 -> aux out tl1
      | (Binding_univ uu____13943)::tl1 -> aux out tl1
      | (Binding_lid (uu____13947,(uu____13948,t)))::tl1 ->
          let uu____13963 =
            let uu____13966 = FStar_Syntax_Free.univs t in
            ext out uu____13966 in
          aux uu____13963 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13969;
            FStar_Syntax_Syntax.index = uu____13970;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13977 =
            let uu____13980 = FStar_Syntax_Free.univs t in
            ext out uu____13980 in
          aux uu____13977 tl1
      | (Binding_sig uu____13983)::uu____13984 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14037)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14053 = FStar_Util.fifo_set_add uname out in
          aux uu____14053 tl1
      | (Binding_lid (uu____14056,(uu____14057,t)))::tl1 ->
          let uu____14072 =
            let uu____14075 = FStar_Syntax_Free.univnames t in
            ext out uu____14075 in
          aux uu____14072 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14078;
            FStar_Syntax_Syntax.index = uu____14079;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14086 =
            let uu____14089 = FStar_Syntax_Free.univnames t in
            ext out uu____14089 in
          aux uu____14086 tl1
      | (Binding_sig uu____14092)::uu____14093 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___261_14117  ->
            match uu___261_14117 with
            | Binding_var x -> [x]
            | Binding_lid uu____14121 -> []
            | Binding_sig uu____14126 -> []
            | Binding_univ uu____14133 -> []
            | Binding_sig_inst uu____14134 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14150 =
      let uu____14153 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14153
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14150 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14175 =
      let uu____14176 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___262_14186  ->
                match uu___262_14186 with
                | Binding_var x ->
                    let uu____14188 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14188
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14191) ->
                    let uu____14192 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14192
                | Binding_sig (ls,uu____14194) ->
                    let uu____14199 =
                      let uu____14200 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14200
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14199
                | Binding_sig_inst (ls,uu____14210,uu____14211) ->
                    let uu____14216 =
                      let uu____14217 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14217
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14216)) in
      FStar_All.pipe_right uu____14176 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14175 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14234 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14234
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14262  ->
                 fun uu____14263  ->
                   match (uu____14262, uu____14263) with
                   | ((b1,uu____14281),(b2,uu____14283)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___263_14325  ->
    match uu___263_14325 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14326 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___264_14344  ->
             match uu___264_14344 with
             | Binding_sig (lids,uu____14350) -> FStar_List.append lids keys
             | uu____14355 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14361  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14395) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14414,uu____14415) -> false in
      let uu____14424 =
        FStar_List.tryFind
          (fun uu____14442  ->
             match uu____14442 with | (p,uu____14450) -> list_prefix p path)
          env.proof_ns in
      match uu____14424 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14461,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14479 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14479
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___288_14491 = e in
        {
          solver = (uu___288_14491.solver);
          range = (uu___288_14491.range);
          curmodule = (uu___288_14491.curmodule);
          gamma = (uu___288_14491.gamma);
          gamma_cache = (uu___288_14491.gamma_cache);
          modules = (uu___288_14491.modules);
          expected_typ = (uu___288_14491.expected_typ);
          sigtab = (uu___288_14491.sigtab);
          is_pattern = (uu___288_14491.is_pattern);
          instantiate_imp = (uu___288_14491.instantiate_imp);
          effects = (uu___288_14491.effects);
          generalize = (uu___288_14491.generalize);
          letrecs = (uu___288_14491.letrecs);
          top_level = (uu___288_14491.top_level);
          check_uvars = (uu___288_14491.check_uvars);
          use_eq = (uu___288_14491.use_eq);
          is_iface = (uu___288_14491.is_iface);
          admit = (uu___288_14491.admit);
          lax = (uu___288_14491.lax);
          lax_universes = (uu___288_14491.lax_universes);
          failhard = (uu___288_14491.failhard);
          nosynth = (uu___288_14491.nosynth);
          tc_term = (uu___288_14491.tc_term);
          type_of = (uu___288_14491.type_of);
          universe_of = (uu___288_14491.universe_of);
          use_bv_sorts = (uu___288_14491.use_bv_sorts);
          qname_and_index = (uu___288_14491.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___288_14491.synth);
          is_native_tactic = (uu___288_14491.is_native_tactic);
          identifier_info = (uu___288_14491.identifier_info);
          tc_hooks = (uu___288_14491.tc_hooks);
          dsenv = (uu___288_14491.dsenv);
          dep_graph = (uu___288_14491.dep_graph)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___289_14517 = e in
      {
        solver = (uu___289_14517.solver);
        range = (uu___289_14517.range);
        curmodule = (uu___289_14517.curmodule);
        gamma = (uu___289_14517.gamma);
        gamma_cache = (uu___289_14517.gamma_cache);
        modules = (uu___289_14517.modules);
        expected_typ = (uu___289_14517.expected_typ);
        sigtab = (uu___289_14517.sigtab);
        is_pattern = (uu___289_14517.is_pattern);
        instantiate_imp = (uu___289_14517.instantiate_imp);
        effects = (uu___289_14517.effects);
        generalize = (uu___289_14517.generalize);
        letrecs = (uu___289_14517.letrecs);
        top_level = (uu___289_14517.top_level);
        check_uvars = (uu___289_14517.check_uvars);
        use_eq = (uu___289_14517.use_eq);
        is_iface = (uu___289_14517.is_iface);
        admit = (uu___289_14517.admit);
        lax = (uu___289_14517.lax);
        lax_universes = (uu___289_14517.lax_universes);
        failhard = (uu___289_14517.failhard);
        nosynth = (uu___289_14517.nosynth);
        tc_term = (uu___289_14517.tc_term);
        type_of = (uu___289_14517.type_of);
        universe_of = (uu___289_14517.universe_of);
        use_bv_sorts = (uu___289_14517.use_bv_sorts);
        qname_and_index = (uu___289_14517.qname_and_index);
        proof_ns = ns;
        synth = (uu___289_14517.synth);
        is_native_tactic = (uu___289_14517.is_native_tactic);
        identifier_info = (uu___289_14517.identifier_info);
        tc_hooks = (uu___289_14517.tc_hooks);
        dsenv = (uu___289_14517.dsenv);
        dep_graph = (uu___289_14517.dep_graph)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14528 = FStar_Syntax_Free.names t in
      let uu____14531 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14528 uu____14531
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14548 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14548
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14554 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14554
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14569 =
      match uu____14569 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14585 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14585) in
    let uu____14587 =
      let uu____14590 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14590 FStar_List.rev in
    FStar_All.pipe_right uu____14587 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14607  -> ());
    push = (fun uu____14609  -> ());
    pop = (fun uu____14611  -> ());
    encode_modul = (fun uu____14614  -> fun uu____14615  -> ());
    encode_sig = (fun uu____14618  -> fun uu____14619  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14625 =
             let uu____14632 = FStar_Options.peek () in (e, g, uu____14632) in
           [uu____14625]);
    solve = (fun uu____14648  -> fun uu____14649  -> fun uu____14650  -> ());
    finish = (fun uu____14656  -> ());
    refresh = (fun uu____14658  -> ())
  }