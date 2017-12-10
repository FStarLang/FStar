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
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkmlift__item__mlift_wp:
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let __proj__Mkmlift__item__mlift_term:
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
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
           (fun uu___171_5059  ->
              match uu___171_5059 with
              | Binding_var x ->
                  let y =
                    let uu____5062 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____5062 in
                  let uu____5063 =
                    let uu____5064 = FStar_Syntax_Subst.compress y in
                    uu____5064.FStar_Syntax_Syntax.n in
                  (match uu____5063 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5068 =
                         let uu___185_5069 = y1 in
                         let uu____5070 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___185_5069.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___185_5069.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5070
                         } in
                       Binding_var uu____5068
                   | uu____5073 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___186_5081 = env in
      let uu____5082 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___186_5081.solver);
        range = (uu___186_5081.range);
        curmodule = (uu___186_5081.curmodule);
        gamma = uu____5082;
        gamma_cache = (uu___186_5081.gamma_cache);
        modules = (uu___186_5081.modules);
        expected_typ = (uu___186_5081.expected_typ);
        sigtab = (uu___186_5081.sigtab);
        is_pattern = (uu___186_5081.is_pattern);
        instantiate_imp = (uu___186_5081.instantiate_imp);
        effects = (uu___186_5081.effects);
        generalize = (uu___186_5081.generalize);
        letrecs = (uu___186_5081.letrecs);
        top_level = (uu___186_5081.top_level);
        check_uvars = (uu___186_5081.check_uvars);
        use_eq = (uu___186_5081.use_eq);
        is_iface = (uu___186_5081.is_iface);
        admit = (uu___186_5081.admit);
        lax = (uu___186_5081.lax);
        lax_universes = (uu___186_5081.lax_universes);
        failhard = (uu___186_5081.failhard);
        nosynth = (uu___186_5081.nosynth);
        tc_term = (uu___186_5081.tc_term);
        type_of = (uu___186_5081.type_of);
        universe_of = (uu___186_5081.universe_of);
        use_bv_sorts = (uu___186_5081.use_bv_sorts);
        qname_and_index = (uu___186_5081.qname_and_index);
        proof_ns = (uu___186_5081.proof_ns);
        synth = (uu___186_5081.synth);
        is_native_tactic = (uu___186_5081.is_native_tactic);
        identifier_info = (uu___186_5081.identifier_info);
        tc_hooks = (uu___186_5081.tc_hooks);
        dsenv = (uu___186_5081.dsenv);
        dep_graph = (uu___186_5081.dep_graph)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5089  -> fun uu____5090  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___187_5100 = env in
      {
        solver = (uu___187_5100.solver);
        range = (uu___187_5100.range);
        curmodule = (uu___187_5100.curmodule);
        gamma = (uu___187_5100.gamma);
        gamma_cache = (uu___187_5100.gamma_cache);
        modules = (uu___187_5100.modules);
        expected_typ = (uu___187_5100.expected_typ);
        sigtab = (uu___187_5100.sigtab);
        is_pattern = (uu___187_5100.is_pattern);
        instantiate_imp = (uu___187_5100.instantiate_imp);
        effects = (uu___187_5100.effects);
        generalize = (uu___187_5100.generalize);
        letrecs = (uu___187_5100.letrecs);
        top_level = (uu___187_5100.top_level);
        check_uvars = (uu___187_5100.check_uvars);
        use_eq = (uu___187_5100.use_eq);
        is_iface = (uu___187_5100.is_iface);
        admit = (uu___187_5100.admit);
        lax = (uu___187_5100.lax);
        lax_universes = (uu___187_5100.lax_universes);
        failhard = (uu___187_5100.failhard);
        nosynth = (uu___187_5100.nosynth);
        tc_term = (uu___187_5100.tc_term);
        type_of = (uu___187_5100.type_of);
        universe_of = (uu___187_5100.universe_of);
        use_bv_sorts = (uu___187_5100.use_bv_sorts);
        qname_and_index = (uu___187_5100.qname_and_index);
        proof_ns = (uu___187_5100.proof_ns);
        synth = (uu___187_5100.synth);
        is_native_tactic = (uu___187_5100.is_native_tactic);
        identifier_info = (uu___187_5100.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___187_5100.dsenv);
        dep_graph = (uu___187_5100.dep_graph)
      }
let set_dep_graph: env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___188_5107 = e in
      {
        solver = (uu___188_5107.solver);
        range = (uu___188_5107.range);
        curmodule = (uu___188_5107.curmodule);
        gamma = (uu___188_5107.gamma);
        gamma_cache = (uu___188_5107.gamma_cache);
        modules = (uu___188_5107.modules);
        expected_typ = (uu___188_5107.expected_typ);
        sigtab = (uu___188_5107.sigtab);
        is_pattern = (uu___188_5107.is_pattern);
        instantiate_imp = (uu___188_5107.instantiate_imp);
        effects = (uu___188_5107.effects);
        generalize = (uu___188_5107.generalize);
        letrecs = (uu___188_5107.letrecs);
        top_level = (uu___188_5107.top_level);
        check_uvars = (uu___188_5107.check_uvars);
        use_eq = (uu___188_5107.use_eq);
        is_iface = (uu___188_5107.is_iface);
        admit = (uu___188_5107.admit);
        lax = (uu___188_5107.lax);
        lax_universes = (uu___188_5107.lax_universes);
        failhard = (uu___188_5107.failhard);
        nosynth = (uu___188_5107.nosynth);
        tc_term = (uu___188_5107.tc_term);
        type_of = (uu___188_5107.type_of);
        universe_of = (uu___188_5107.universe_of);
        use_bv_sorts = (uu___188_5107.use_bv_sorts);
        qname_and_index = (uu___188_5107.qname_and_index);
        proof_ns = (uu___188_5107.proof_ns);
        synth = (uu___188_5107.synth);
        is_native_tactic = (uu___188_5107.is_native_tactic);
        identifier_info = (uu___188_5107.identifier_info);
        tc_hooks = (uu___188_5107.tc_hooks);
        dsenv = (uu___188_5107.dsenv);
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
      | (NoDelta ,uu____5122) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5123,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5124,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5125 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5132 . Prims.unit -> 'Auu____5132 FStar_Util.smap =
  fun uu____5138  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5141 . Prims.unit -> 'Auu____5141 FStar_Util.smap =
  fun uu____5147  -> FStar_Util.smap_create (Prims.parse_int "100")
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
              let uu____5220 = new_gamma_cache () in
              let uu____5223 = new_sigtab () in
              let uu____5226 = FStar_Options.using_facts_from () in
              let uu____5227 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty in
              let uu____5230 = FStar_ToSyntax_Env.empty_env () in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5220;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5223;
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
                proof_ns = uu____5226;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5264  -> false);
                identifier_info = uu____5227;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5230;
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
  fun uu____5332  ->
    let uu____5333 = FStar_ST.op_Bang query_indices in
    match uu____5333 with
    | [] -> failwith "Empty query indices!"
    | uu____5412 ->
        let uu____5421 =
          let uu____5430 =
            let uu____5437 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5437 in
          let uu____5516 = FStar_ST.op_Bang query_indices in uu____5430 ::
            uu____5516 in
        FStar_ST.op_Colon_Equals query_indices uu____5421
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5661  ->
    let uu____5662 = FStar_ST.op_Bang query_indices in
    match uu____5662 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5833  ->
    match uu____5833 with
    | (l,n1) ->
        let uu____5840 = FStar_ST.op_Bang query_indices in
        (match uu____5840 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6009 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6026  ->
    let uu____6027 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____6027
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6123 =
       let uu____6126 = FStar_ST.op_Bang stack in env :: uu____6126 in
     FStar_ST.op_Colon_Equals stack uu____6123);
    (let uu___189_6233 = env in
     let uu____6234 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6237 = FStar_Util.smap_copy (sigtab env) in
     let uu____6240 =
       let uu____6243 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6243 in
     {
       solver = (uu___189_6233.solver);
       range = (uu___189_6233.range);
       curmodule = (uu___189_6233.curmodule);
       gamma = (uu___189_6233.gamma);
       gamma_cache = uu____6234;
       modules = (uu___189_6233.modules);
       expected_typ = (uu___189_6233.expected_typ);
       sigtab = uu____6237;
       is_pattern = (uu___189_6233.is_pattern);
       instantiate_imp = (uu___189_6233.instantiate_imp);
       effects = (uu___189_6233.effects);
       generalize = (uu___189_6233.generalize);
       letrecs = (uu___189_6233.letrecs);
       top_level = (uu___189_6233.top_level);
       check_uvars = (uu___189_6233.check_uvars);
       use_eq = (uu___189_6233.use_eq);
       is_iface = (uu___189_6233.is_iface);
       admit = (uu___189_6233.admit);
       lax = (uu___189_6233.lax);
       lax_universes = (uu___189_6233.lax_universes);
       failhard = (uu___189_6233.failhard);
       nosynth = (uu___189_6233.nosynth);
       tc_term = (uu___189_6233.tc_term);
       type_of = (uu___189_6233.type_of);
       universe_of = (uu___189_6233.universe_of);
       use_bv_sorts = (uu___189_6233.use_bv_sorts);
       qname_and_index = (uu___189_6233.qname_and_index);
       proof_ns = (uu___189_6233.proof_ns);
       synth = (uu___189_6233.synth);
       is_native_tactic = (uu___189_6233.is_native_tactic);
       identifier_info = uu____6240;
       tc_hooks = (uu___189_6233.tc_hooks);
       dsenv = (uu___189_6233.dsenv);
       dep_graph = (uu___189_6233.dep_graph)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6308  ->
    let uu____6309 = FStar_ST.op_Bang stack in
    match uu____6309 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6421 -> failwith "Impossible: Too many pops"
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
        let uu____6460 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6486  ->
                  match uu____6486 with
                  | (m,uu____6492) -> FStar_Ident.lid_equals l m)) in
        (match uu____6460 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___190_6499 = env in
               {
                 solver = (uu___190_6499.solver);
                 range = (uu___190_6499.range);
                 curmodule = (uu___190_6499.curmodule);
                 gamma = (uu___190_6499.gamma);
                 gamma_cache = (uu___190_6499.gamma_cache);
                 modules = (uu___190_6499.modules);
                 expected_typ = (uu___190_6499.expected_typ);
                 sigtab = (uu___190_6499.sigtab);
                 is_pattern = (uu___190_6499.is_pattern);
                 instantiate_imp = (uu___190_6499.instantiate_imp);
                 effects = (uu___190_6499.effects);
                 generalize = (uu___190_6499.generalize);
                 letrecs = (uu___190_6499.letrecs);
                 top_level = (uu___190_6499.top_level);
                 check_uvars = (uu___190_6499.check_uvars);
                 use_eq = (uu___190_6499.use_eq);
                 is_iface = (uu___190_6499.is_iface);
                 admit = (uu___190_6499.admit);
                 lax = (uu___190_6499.lax);
                 lax_universes = (uu___190_6499.lax_universes);
                 failhard = (uu___190_6499.failhard);
                 nosynth = (uu___190_6499.nosynth);
                 tc_term = (uu___190_6499.tc_term);
                 type_of = (uu___190_6499.type_of);
                 universe_of = (uu___190_6499.universe_of);
                 use_bv_sorts = (uu___190_6499.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___190_6499.proof_ns);
                 synth = (uu___190_6499.synth);
                 is_native_tactic = (uu___190_6499.is_native_tactic);
                 identifier_info = (uu___190_6499.identifier_info);
                 tc_hooks = (uu___190_6499.tc_hooks);
                 dsenv = (uu___190_6499.dsenv);
                 dep_graph = (uu___190_6499.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6504,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___191_6512 = env in
               {
                 solver = (uu___191_6512.solver);
                 range = (uu___191_6512.range);
                 curmodule = (uu___191_6512.curmodule);
                 gamma = (uu___191_6512.gamma);
                 gamma_cache = (uu___191_6512.gamma_cache);
                 modules = (uu___191_6512.modules);
                 expected_typ = (uu___191_6512.expected_typ);
                 sigtab = (uu___191_6512.sigtab);
                 is_pattern = (uu___191_6512.is_pattern);
                 instantiate_imp = (uu___191_6512.instantiate_imp);
                 effects = (uu___191_6512.effects);
                 generalize = (uu___191_6512.generalize);
                 letrecs = (uu___191_6512.letrecs);
                 top_level = (uu___191_6512.top_level);
                 check_uvars = (uu___191_6512.check_uvars);
                 use_eq = (uu___191_6512.use_eq);
                 is_iface = (uu___191_6512.is_iface);
                 admit = (uu___191_6512.admit);
                 lax = (uu___191_6512.lax);
                 lax_universes = (uu___191_6512.lax_universes);
                 failhard = (uu___191_6512.failhard);
                 nosynth = (uu___191_6512.nosynth);
                 tc_term = (uu___191_6512.tc_term);
                 type_of = (uu___191_6512.type_of);
                 universe_of = (uu___191_6512.universe_of);
                 use_bv_sorts = (uu___191_6512.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___191_6512.proof_ns);
                 synth = (uu___191_6512.synth);
                 is_native_tactic = (uu___191_6512.is_native_tactic);
                 identifier_info = (uu___191_6512.identifier_info);
                 tc_hooks = (uu___191_6512.tc_hooks);
                 dsenv = (uu___191_6512.dsenv);
                 dep_graph = (uu___191_6512.dep_graph)
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
        (let uu___192_6530 = e in
         {
           solver = (uu___192_6530.solver);
           range = r;
           curmodule = (uu___192_6530.curmodule);
           gamma = (uu___192_6530.gamma);
           gamma_cache = (uu___192_6530.gamma_cache);
           modules = (uu___192_6530.modules);
           expected_typ = (uu___192_6530.expected_typ);
           sigtab = (uu___192_6530.sigtab);
           is_pattern = (uu___192_6530.is_pattern);
           instantiate_imp = (uu___192_6530.instantiate_imp);
           effects = (uu___192_6530.effects);
           generalize = (uu___192_6530.generalize);
           letrecs = (uu___192_6530.letrecs);
           top_level = (uu___192_6530.top_level);
           check_uvars = (uu___192_6530.check_uvars);
           use_eq = (uu___192_6530.use_eq);
           is_iface = (uu___192_6530.is_iface);
           admit = (uu___192_6530.admit);
           lax = (uu___192_6530.lax);
           lax_universes = (uu___192_6530.lax_universes);
           failhard = (uu___192_6530.failhard);
           nosynth = (uu___192_6530.nosynth);
           tc_term = (uu___192_6530.tc_term);
           type_of = (uu___192_6530.type_of);
           universe_of = (uu___192_6530.universe_of);
           use_bv_sorts = (uu___192_6530.use_bv_sorts);
           qname_and_index = (uu___192_6530.qname_and_index);
           proof_ns = (uu___192_6530.proof_ns);
           synth = (uu___192_6530.synth);
           is_native_tactic = (uu___192_6530.is_native_tactic);
           identifier_info = (uu___192_6530.identifier_info);
           tc_hooks = (uu___192_6530.tc_hooks);
           dsenv = (uu___192_6530.dsenv);
           dep_graph = (uu___192_6530.dep_graph)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6540 =
        let uu____6541 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6541 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6540
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6647 =
          let uu____6648 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6648 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6647
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6754 =
          let uu____6755 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6755 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6754
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6863 =
        let uu____6864 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6864 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6863
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___193_6975 = env in
      {
        solver = (uu___193_6975.solver);
        range = (uu___193_6975.range);
        curmodule = lid;
        gamma = (uu___193_6975.gamma);
        gamma_cache = (uu___193_6975.gamma_cache);
        modules = (uu___193_6975.modules);
        expected_typ = (uu___193_6975.expected_typ);
        sigtab = (uu___193_6975.sigtab);
        is_pattern = (uu___193_6975.is_pattern);
        instantiate_imp = (uu___193_6975.instantiate_imp);
        effects = (uu___193_6975.effects);
        generalize = (uu___193_6975.generalize);
        letrecs = (uu___193_6975.letrecs);
        top_level = (uu___193_6975.top_level);
        check_uvars = (uu___193_6975.check_uvars);
        use_eq = (uu___193_6975.use_eq);
        is_iface = (uu___193_6975.is_iface);
        admit = (uu___193_6975.admit);
        lax = (uu___193_6975.lax);
        lax_universes = (uu___193_6975.lax_universes);
        failhard = (uu___193_6975.failhard);
        nosynth = (uu___193_6975.nosynth);
        tc_term = (uu___193_6975.tc_term);
        type_of = (uu___193_6975.type_of);
        universe_of = (uu___193_6975.universe_of);
        use_bv_sorts = (uu___193_6975.use_bv_sorts);
        qname_and_index = (uu___193_6975.qname_and_index);
        proof_ns = (uu___193_6975.proof_ns);
        synth = (uu___193_6975.synth);
        is_native_tactic = (uu___193_6975.is_native_tactic);
        identifier_info = (uu___193_6975.identifier_info);
        tc_hooks = (uu___193_6975.tc_hooks);
        dsenv = (uu___193_6975.dsenv);
        dep_graph = (uu___193_6975.dep_graph)
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
    let uu____7000 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____7000
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7003  ->
    let uu____7004 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____7004
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
      | ((formals,t),uu____7042) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____7066 = FStar_Syntax_Subst.subst vs t in (us, uu____7066)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___172_7079  ->
    match uu___172_7079 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7103  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7116 = inst_tscheme t in
      match uu____7116 with
      | (us,t1) ->
          let uu____7127 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7127)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7139  ->
          match uu____7139 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7154 =
                         let uu____7155 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7156 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7157 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7158 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7155 uu____7156 uu____7157 uu____7158 in
                       failwith uu____7154)
                    else ();
                    (let uu____7160 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7160))
               | uu____7167 ->
                   let uu____7168 =
                     let uu____7169 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7169 in
                   failwith uu____7168)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7173 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7177 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7181 -> false
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
             | ([],uu____7215) -> Maybe
             | (uu____7222,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7241 -> No in
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
          let uu____7346 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7346 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___173_7391  ->
                   match uu___173_7391 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7434 =
                           let uu____7453 =
                             let uu____7468 = inst_tscheme t in
                             FStar_Util.Inl uu____7468 in
                           (uu____7453, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7434
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7534,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7536);
                                     FStar_Syntax_Syntax.sigrng = uu____7537;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7538;
                                     FStar_Syntax_Syntax.sigmeta = uu____7539;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7540;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7560 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7560
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7606 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7613 -> cache t in
                       let uu____7614 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7614 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7689 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7689 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7775 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7855 = find_in_sigtab env lid in
         match uu____7855 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7954) ->
          add_sigelts env ses
      | uu____7963 ->
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
            | uu____7977 -> ()))
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
        (fun uu___174_8004  ->
           match uu___174_8004 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8022 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____8055,lb::[]),uu____8057) ->
          let uu____8070 =
            let uu____8079 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8088 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8079, uu____8088) in
          FStar_Pervasives_Native.Some uu____8070
      | FStar_Syntax_Syntax.Sig_let ((uu____8101,lbs),uu____8103) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8139 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8151 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8151
                   then
                     let uu____8162 =
                       let uu____8171 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8180 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8171, uu____8180) in
                     FStar_Pervasives_Native.Some uu____8162
                   else FStar_Pervasives_Native.None)
      | uu____8202 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8235 =
          let uu____8244 =
            let uu____8249 =
              let uu____8250 =
                let uu____8253 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8253 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8250) in
            inst_tscheme uu____8249 in
          (uu____8244, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8235
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8273,uu____8274) ->
        let uu____8279 =
          let uu____8288 =
            let uu____8293 =
              let uu____8294 =
                let uu____8297 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8297 in
              (us, uu____8294) in
            inst_tscheme uu____8293 in
          (uu____8288, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8279
    | uu____8314 -> FStar_Pervasives_Native.None
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
      let mapper uu____8372 =
        match uu____8372 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8468,uvs,t,uu____8471,uu____8472,uu____8473);
                    FStar_Syntax_Syntax.sigrng = uu____8474;
                    FStar_Syntax_Syntax.sigquals = uu____8475;
                    FStar_Syntax_Syntax.sigmeta = uu____8476;
                    FStar_Syntax_Syntax.sigattrs = uu____8477;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8498 =
                   let uu____8507 = inst_tscheme (uvs, t) in
                   (uu____8507, rng) in
                 FStar_Pervasives_Native.Some uu____8498
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8527;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8529;
                    FStar_Syntax_Syntax.sigattrs = uu____8530;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8547 =
                   let uu____8548 = in_cur_mod env l in uu____8548 = Yes in
                 if uu____8547
                 then
                   let uu____8559 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8559
                    then
                      let uu____8572 =
                        let uu____8581 = inst_tscheme (uvs, t) in
                        (uu____8581, rng) in
                      FStar_Pervasives_Native.Some uu____8572
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8608 =
                      let uu____8617 = inst_tscheme (uvs, t) in
                      (uu____8617, rng) in
                    FStar_Pervasives_Native.Some uu____8608)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8638,uu____8639);
                    FStar_Syntax_Syntax.sigrng = uu____8640;
                    FStar_Syntax_Syntax.sigquals = uu____8641;
                    FStar_Syntax_Syntax.sigmeta = uu____8642;
                    FStar_Syntax_Syntax.sigattrs = uu____8643;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8682 =
                        let uu____8691 = inst_tscheme (uvs, k) in
                        (uu____8691, rng) in
                      FStar_Pervasives_Native.Some uu____8682
                  | uu____8708 ->
                      let uu____8709 =
                        let uu____8718 =
                          let uu____8723 =
                            let uu____8724 =
                              let uu____8727 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8727 in
                            (uvs, uu____8724) in
                          inst_tscheme uu____8723 in
                        (uu____8718, rng) in
                      FStar_Pervasives_Native.Some uu____8709)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8748,uu____8749);
                    FStar_Syntax_Syntax.sigrng = uu____8750;
                    FStar_Syntax_Syntax.sigquals = uu____8751;
                    FStar_Syntax_Syntax.sigmeta = uu____8752;
                    FStar_Syntax_Syntax.sigattrs = uu____8753;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8793 =
                        let uu____8802 = inst_tscheme_with (uvs, k) us in
                        (uu____8802, rng) in
                      FStar_Pervasives_Native.Some uu____8793
                  | uu____8819 ->
                      let uu____8820 =
                        let uu____8829 =
                          let uu____8834 =
                            let uu____8835 =
                              let uu____8838 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8838 in
                            (uvs, uu____8835) in
                          inst_tscheme_with uu____8834 us in
                        (uu____8829, rng) in
                      FStar_Pervasives_Native.Some uu____8820)
             | FStar_Util.Inr se ->
                 let uu____8872 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8893;
                        FStar_Syntax_Syntax.sigrng = uu____8894;
                        FStar_Syntax_Syntax.sigquals = uu____8895;
                        FStar_Syntax_Syntax.sigmeta = uu____8896;
                        FStar_Syntax_Syntax.sigattrs = uu____8897;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8912 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8872
                   (FStar_Util.map_option
                      (fun uu____8960  ->
                         match uu____8960 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8991 =
        let uu____9002 = lookup_qname env lid in
        FStar_Util.bind_opt uu____9002 mapper in
      match uu____8991 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___194_9095 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___194_9095.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___194_9095.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9120 = lookup_qname env l in
      match uu____9120 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9159 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9207 = try_lookup_bv env bv in
      match uu____9207 with
      | FStar_Pervasives_Native.None  ->
          let uu____9222 =
            let uu____9223 =
              let uu____9228 = variable_not_found bv in (uu____9228, bvr) in
            FStar_Errors.Error uu____9223 in
          FStar_Exn.raise uu____9222
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9239 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9240 =
            let uu____9241 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9241 in
          (uu____9239, uu____9240)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9258 = try_lookup_lid_aux env l in
      match uu____9258 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9324 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9324 in
          let uu____9325 =
            let uu____9334 =
              let uu____9339 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9339) in
            (uu____9334, r1) in
          FStar_Pervasives_Native.Some uu____9325
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9366 = try_lookup_lid env l in
      match uu____9366 with
      | FStar_Pervasives_Native.None  ->
          let uu____9393 =
            let uu____9394 =
              let uu____9399 = name_not_found l in
              (uu____9399, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9394 in
          FStar_Exn.raise uu____9393
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___175_9435  ->
              match uu___175_9435 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9437 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9452 = lookup_qname env lid in
      match uu____9452 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9481,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9484;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9486;
              FStar_Syntax_Syntax.sigattrs = uu____9487;_},FStar_Pervasives_Native.None
            ),uu____9488)
          ->
          let uu____9537 =
            let uu____9548 =
              let uu____9553 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9553) in
            (uu____9548, q) in
          FStar_Pervasives_Native.Some uu____9537
      | uu____9570 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9607 = lookup_qname env lid in
      match uu____9607 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9632,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9635;
              FStar_Syntax_Syntax.sigquals = uu____9636;
              FStar_Syntax_Syntax.sigmeta = uu____9637;
              FStar_Syntax_Syntax.sigattrs = uu____9638;_},FStar_Pervasives_Native.None
            ),uu____9639)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9688 ->
          let uu____9709 =
            let uu____9710 =
              let uu____9715 = name_not_found lid in
              (uu____9715, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9710 in
          FStar_Exn.raise uu____9709
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9730 = lookup_qname env lid in
      match uu____9730 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9755,uvs,t,uu____9758,uu____9759,uu____9760);
              FStar_Syntax_Syntax.sigrng = uu____9761;
              FStar_Syntax_Syntax.sigquals = uu____9762;
              FStar_Syntax_Syntax.sigmeta = uu____9763;
              FStar_Syntax_Syntax.sigattrs = uu____9764;_},FStar_Pervasives_Native.None
            ),uu____9765)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9818 ->
          let uu____9839 =
            let uu____9840 =
              let uu____9845 = name_not_found lid in
              (uu____9845, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9840 in
          FStar_Exn.raise uu____9839
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9862 = lookup_qname env lid in
      match uu____9862 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9889,uu____9890,uu____9891,uu____9892,uu____9893,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9895;
              FStar_Syntax_Syntax.sigquals = uu____9896;
              FStar_Syntax_Syntax.sigmeta = uu____9897;
              FStar_Syntax_Syntax.sigattrs = uu____9898;_},uu____9899),uu____9900)
          -> (true, dcs)
      | uu____9961 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9990 = lookup_qname env lid in
      match uu____9990 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10011,uu____10012,uu____10013,l,uu____10015,uu____10016);
              FStar_Syntax_Syntax.sigrng = uu____10017;
              FStar_Syntax_Syntax.sigquals = uu____10018;
              FStar_Syntax_Syntax.sigmeta = uu____10019;
              FStar_Syntax_Syntax.sigattrs = uu____10020;_},uu____10021),uu____10022)
          -> l
      | uu____10077 ->
          let uu____10098 =
            let uu____10099 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10099 in
          failwith uu____10098
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
        let uu____10133 = lookup_qname env lid in
        match uu____10133 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10161)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10212,lbs),uu____10214)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10242 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10242
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10274 -> FStar_Pervasives_Native.None)
        | uu____10279 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10314 = lookup_qname env ftv in
      match uu____10314 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10338) ->
          let uu____10383 = effect_signature se in
          (match uu____10383 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10404,t),r) ->
               let uu____10419 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10419)
      | uu____10420 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10447 = try_lookup_effect_lid env ftv in
      match uu____10447 with
      | FStar_Pervasives_Native.None  ->
          let uu____10450 =
            let uu____10451 =
              let uu____10456 = name_not_found ftv in
              (uu____10456, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10451 in
          FStar_Exn.raise uu____10450
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
        let uu____10473 = lookup_qname env lid0 in
        match uu____10473 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10504);
                FStar_Syntax_Syntax.sigrng = uu____10505;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10507;
                FStar_Syntax_Syntax.sigattrs = uu____10508;_},FStar_Pervasives_Native.None
              ),uu____10509)
            ->
            let lid1 =
              let uu____10563 =
                let uu____10564 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10564 in
              FStar_Ident.set_lid_range lid uu____10563 in
            let uu____10565 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___176_10569  ->
                      match uu___176_10569 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10570 -> false)) in
            if uu____10565
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10584 =
                      let uu____10585 =
                        let uu____10586 = get_range env in
                        FStar_Range.string_of_range uu____10586 in
                      let uu____10587 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10588 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10585 uu____10587 uu____10588 in
                    failwith uu____10584) in
               match (binders, univs1) with
               | ([],uu____10595) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10612,uu____10613::uu____10614::uu____10615) ->
                   let uu____10620 =
                     let uu____10621 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10622 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10621 uu____10622 in
                   failwith uu____10620
               | uu____10629 ->
                   let uu____10634 =
                     let uu____10639 =
                       let uu____10640 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10640) in
                     inst_tscheme_with uu____10639 insts in
                   (match uu____10634 with
                    | (uu____10651,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10654 =
                          let uu____10655 = FStar_Syntax_Subst.compress t1 in
                          uu____10655.FStar_Syntax_Syntax.n in
                        (match uu____10654 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10702 -> failwith "Impossible")))
        | uu____10709 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10749 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10749 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10762,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10769 = find1 l2 in
            (match uu____10769 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10776 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10776 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10780 = find1 l in
            (match uu____10780 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10794 = lookup_qname env l1 in
      match uu____10794 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10817;
              FStar_Syntax_Syntax.sigrng = uu____10818;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10820;
              FStar_Syntax_Syntax.sigattrs = uu____10821;_},uu____10822),uu____10823)
          -> q
      | uu____10874 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10907 =
          let uu____10908 =
            let uu____10909 = FStar_Util.string_of_int i in
            let uu____10910 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10909 uu____10910 in
          failwith uu____10908 in
        let uu____10911 = lookup_datacon env lid in
        match uu____10911 with
        | (uu____10916,t) ->
            let uu____10918 =
              let uu____10919 = FStar_Syntax_Subst.compress t in
              uu____10919.FStar_Syntax_Syntax.n in
            (match uu____10918 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10923) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10954 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10954
                      FStar_Pervasives_Native.fst)
             | uu____10963 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10970 = lookup_qname env l in
      match uu____10970 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10991,uu____10992,uu____10993);
              FStar_Syntax_Syntax.sigrng = uu____10994;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10996;
              FStar_Syntax_Syntax.sigattrs = uu____10997;_},uu____10998),uu____10999)
          ->
          FStar_Util.for_some
            (fun uu___177_11052  ->
               match uu___177_11052 with
               | FStar_Syntax_Syntax.Projector uu____11053 -> true
               | uu____11058 -> false) quals
      | uu____11059 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11086 = lookup_qname env lid in
      match uu____11086 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11107,uu____11108,uu____11109,uu____11110,uu____11111,uu____11112);
              FStar_Syntax_Syntax.sigrng = uu____11113;
              FStar_Syntax_Syntax.sigquals = uu____11114;
              FStar_Syntax_Syntax.sigmeta = uu____11115;
              FStar_Syntax_Syntax.sigattrs = uu____11116;_},uu____11117),uu____11118)
          -> true
      | uu____11173 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11200 = lookup_qname env lid in
      match uu____11200 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11221,uu____11222,uu____11223,uu____11224,uu____11225,uu____11226);
              FStar_Syntax_Syntax.sigrng = uu____11227;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11229;
              FStar_Syntax_Syntax.sigattrs = uu____11230;_},uu____11231),uu____11232)
          ->
          FStar_Util.for_some
            (fun uu___178_11293  ->
               match uu___178_11293 with
               | FStar_Syntax_Syntax.RecordType uu____11294 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11303 -> true
               | uu____11312 -> false) quals
      | uu____11313 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11340 = lookup_qname env lid in
      match uu____11340 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11361,uu____11362);
              FStar_Syntax_Syntax.sigrng = uu____11363;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11365;
              FStar_Syntax_Syntax.sigattrs = uu____11366;_},uu____11367),uu____11368)
          ->
          FStar_Util.for_some
            (fun uu___179_11425  ->
               match uu___179_11425 with
               | FStar_Syntax_Syntax.Action uu____11426 -> true
               | uu____11427 -> false) quals
      | uu____11428 -> false
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
      let uu____11458 =
        let uu____11459 = FStar_Syntax_Util.un_uinst head1 in
        uu____11459.FStar_Syntax_Syntax.n in
      match uu____11458 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11463 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11528 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11544) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11561 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11568 ->
                 FStar_Pervasives_Native.Some true
             | uu____11585 -> FStar_Pervasives_Native.Some false) in
      let uu____11586 =
        let uu____11589 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11589 mapper in
      match uu____11586 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11635 = lookup_qname env lid in
      match uu____11635 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11656,uu____11657,tps,uu____11659,uu____11660,uu____11661);
              FStar_Syntax_Syntax.sigrng = uu____11662;
              FStar_Syntax_Syntax.sigquals = uu____11663;
              FStar_Syntax_Syntax.sigmeta = uu____11664;
              FStar_Syntax_Syntax.sigattrs = uu____11665;_},uu____11666),uu____11667)
          -> FStar_List.length tps
      | uu____11730 ->
          let uu____11751 =
            let uu____11752 =
              let uu____11757 = name_not_found lid in
              (uu____11757, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11752 in
          FStar_Exn.raise uu____11751
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
           (fun uu____11797  ->
              match uu____11797 with
              | (d,uu____11805) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11816 = effect_decl_opt env l in
      match uu____11816 with
      | FStar_Pervasives_Native.None  ->
          let uu____11831 =
            let uu____11832 =
              let uu____11837 = name_not_found l in
              (uu____11837, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11832 in
          FStar_Exn.raise uu____11831
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun uu____11859  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11874  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
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
            (let uu____11907 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11960  ->
                       match uu____11960 with
                       | (m1,m2,uu____11973,uu____11974,uu____11975) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11907 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11992 =
                   let uu____11993 =
                     let uu____11998 =
                       let uu____11999 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____12000 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11999
                         uu____12000 in
                     (uu____11998, (env.range)) in
                   FStar_Errors.Error uu____11993 in
                 FStar_Exn.raise uu____11992
             | FStar_Pervasives_Native.Some
                 (uu____12007,uu____12008,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____12045 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12045)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12072 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12098  ->
                match uu____12098 with
                | (d,uu____12104) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12072 with
      | FStar_Pervasives_Native.None  ->
          let uu____12115 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12115
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12128 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12128 with
           | (uu____12139,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12149)::(wp,uu____12151)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12187 -> failwith "Impossible"))
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
                 let uu____12230 = get_range env in
                 let uu____12231 =
                   let uu____12234 =
                     let uu____12235 =
                       let uu____12250 =
                         let uu____12253 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12253] in
                       (null_wp, uu____12250) in
                     FStar_Syntax_Syntax.Tm_app uu____12235 in
                   FStar_Syntax_Syntax.mk uu____12234 in
                 uu____12231 FStar_Pervasives_Native.None uu____12230 in
               let uu____12259 =
                 let uu____12260 =
                   let uu____12269 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12269] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12260;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12259)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___195_12278 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___195_12278.order);
              joins = (uu___195_12278.joins)
            } in
          let uu___196_12287 = env in
          {
            solver = (uu___196_12287.solver);
            range = (uu___196_12287.range);
            curmodule = (uu___196_12287.curmodule);
            gamma = (uu___196_12287.gamma);
            gamma_cache = (uu___196_12287.gamma_cache);
            modules = (uu___196_12287.modules);
            expected_typ = (uu___196_12287.expected_typ);
            sigtab = (uu___196_12287.sigtab);
            is_pattern = (uu___196_12287.is_pattern);
            instantiate_imp = (uu___196_12287.instantiate_imp);
            effects;
            generalize = (uu___196_12287.generalize);
            letrecs = (uu___196_12287.letrecs);
            top_level = (uu___196_12287.top_level);
            check_uvars = (uu___196_12287.check_uvars);
            use_eq = (uu___196_12287.use_eq);
            is_iface = (uu___196_12287.is_iface);
            admit = (uu___196_12287.admit);
            lax = (uu___196_12287.lax);
            lax_universes = (uu___196_12287.lax_universes);
            failhard = (uu___196_12287.failhard);
            nosynth = (uu___196_12287.nosynth);
            tc_term = (uu___196_12287.tc_term);
            type_of = (uu___196_12287.type_of);
            universe_of = (uu___196_12287.universe_of);
            use_bv_sorts = (uu___196_12287.use_bv_sorts);
            qname_and_index = (uu___196_12287.qname_and_index);
            proof_ns = (uu___196_12287.proof_ns);
            synth = (uu___196_12287.synth);
            is_native_tactic = (uu___196_12287.is_native_tactic);
            identifier_info = (uu___196_12287.identifier_info);
            tc_hooks = (uu___196_12287.tc_hooks);
            dsenv = (uu___196_12287.dsenv);
            dep_graph = (uu___196_12287.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12307 = (e1.mlift).mlift_wp u r wp1 in
                (e2.mlift).mlift_wp u r uu____12307 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12421 = (e1.mlift).mlift_wp u t wp in
                                let uu____12422 = l1 u t wp e in
                                l2 u t uu____12421 uu____12422))
                | uu____12423 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12471 = inst_tscheme_with lift_t [u] in
            match uu____12471 with
            | (uu____12478,lift_t1) ->
                let uu____12480 =
                  let uu____12483 =
                    let uu____12484 =
                      let uu____12499 =
                        let uu____12502 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12503 =
                          let uu____12506 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12506] in
                        uu____12502 :: uu____12503 in
                      (lift_t1, uu____12499) in
                    FStar_Syntax_Syntax.Tm_app uu____12484 in
                  FStar_Syntax_Syntax.mk uu____12483 in
                uu____12480 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____12556 = inst_tscheme_with lift_t [u] in
            match uu____12556 with
            | (uu____12563,lift_t1) ->
                let uu____12565 =
                  let uu____12568 =
                    let uu____12569 =
                      let uu____12584 =
                        let uu____12587 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12588 =
                          let uu____12591 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12592 =
                            let uu____12595 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12595] in
                          uu____12591 :: uu____12592 in
                        uu____12587 :: uu____12588 in
                      (lift_t1, uu____12584) in
                    FStar_Syntax_Syntax.Tm_app uu____12569 in
                  FStar_Syntax_Syntax.mk uu____12568 in
                uu____12565 FStar_Pervasives_Native.None
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
              let uu____12637 =
                let uu____12638 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12638
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12637 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12642 =
              let uu____12643 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp in
              FStar_Syntax_Print.term_to_string uu____12643 in
            let uu____12644 =
              let uu____12645 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12667 = l1 FStar_Syntax_Syntax.U_zero arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12667) in
              FStar_Util.dflt "none" uu____12645 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12642
              uu____12644 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12693  ->
                    match uu____12693 with
                    | (e,uu____12701) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12720 =
            match uu____12720 with
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
              let uu____12758 =
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
                                    (let uu____12779 =
                                       let uu____12788 =
                                         find_edge order1 (i, k) in
                                       let uu____12791 =
                                         find_edge order1 (k, j) in
                                       (uu____12788, uu____12791) in
                                     match uu____12779 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12806 =
                                           compose_edges e1 e2 in
                                         [uu____12806]
                                     | uu____12807 -> []))))) in
              FStar_List.append order1 uu____12758 in
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
                   let uu____12836 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12838 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12838
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12836
                   then
                     let uu____12843 =
                       let uu____12844 =
                         let uu____12849 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12850 = get_range env in
                         (uu____12849, uu____12850) in
                       FStar_Errors.Error uu____12844 in
                     FStar_Exn.raise uu____12843
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
                                            let uu____12975 =
                                              let uu____12984 =
                                                find_edge order2 (i, k) in
                                              let uu____12987 =
                                                find_edge order2 (j, k) in
                                              (uu____12984, uu____12987) in
                                            match uu____12975 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13029,uu____13030)
                                                     ->
                                                     let uu____13037 =
                                                       let uu____13042 =
                                                         let uu____13043 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____13043 in
                                                       let uu____13046 =
                                                         let uu____13047 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____13047 in
                                                       (uu____13042,
                                                         uu____13046) in
                                                     (match uu____13037 with
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
                                            | uu____13082 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___197_13155 = env.effects in
              { decls = (uu___197_13155.decls); order = order2; joins } in
            let uu___198_13156 = env in
            {
              solver = (uu___198_13156.solver);
              range = (uu___198_13156.range);
              curmodule = (uu___198_13156.curmodule);
              gamma = (uu___198_13156.gamma);
              gamma_cache = (uu___198_13156.gamma_cache);
              modules = (uu___198_13156.modules);
              expected_typ = (uu___198_13156.expected_typ);
              sigtab = (uu___198_13156.sigtab);
              is_pattern = (uu___198_13156.is_pattern);
              instantiate_imp = (uu___198_13156.instantiate_imp);
              effects;
              generalize = (uu___198_13156.generalize);
              letrecs = (uu___198_13156.letrecs);
              top_level = (uu___198_13156.top_level);
              check_uvars = (uu___198_13156.check_uvars);
              use_eq = (uu___198_13156.use_eq);
              is_iface = (uu___198_13156.is_iface);
              admit = (uu___198_13156.admit);
              lax = (uu___198_13156.lax);
              lax_universes = (uu___198_13156.lax_universes);
              failhard = (uu___198_13156.failhard);
              nosynth = (uu___198_13156.nosynth);
              tc_term = (uu___198_13156.tc_term);
              type_of = (uu___198_13156.type_of);
              universe_of = (uu___198_13156.universe_of);
              use_bv_sorts = (uu___198_13156.use_bv_sorts);
              qname_and_index = (uu___198_13156.qname_and_index);
              proof_ns = (uu___198_13156.proof_ns);
              synth = (uu___198_13156.synth);
              is_native_tactic = (uu___198_13156.is_native_tactic);
              identifier_info = (uu___198_13156.identifier_info);
              tc_hooks = (uu___198_13156.tc_hooks);
              dsenv = (uu___198_13156.dsenv);
              dep_graph = (uu___198_13156.dep_graph)
            }))
      | uu____13157 -> env
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
        | uu____13181 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13189 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13189 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13206 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13206 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13224 =
                     let uu____13225 =
                       let uu____13230 =
                         let uu____13231 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13236 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13243 =
                           let uu____13244 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13244 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13231 uu____13236 uu____13243 in
                       (uu____13230, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13225 in
                   FStar_Exn.raise uu____13224)
                else ();
                (let inst1 =
                   let uu____13249 =
                     let uu____13258 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13258 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13275  ->
                        fun uu____13276  ->
                          match (uu____13275, uu____13276) with
                          | ((x,uu____13298),(t,uu____13300)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13249 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13319 =
                     let uu___199_13320 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___199_13320.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___199_13320.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___199_13320.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___199_13320.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13319
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
          let uu____13342 = effect_decl_opt env effect_name in
          match uu____13342 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13375 =
                only_reifiable &&
                  (let uu____13377 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13377) in
              if uu____13375
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13393 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13412 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13441 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13441
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13442 =
                             let uu____13443 =
                               let uu____13448 = get_range env in
                               (message, uu____13448) in
                             FStar_Errors.Error uu____13443 in
                           FStar_Exn.raise uu____13442 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13458 =
                       let uu____13461 = get_range env in
                       let uu____13462 =
                         let uu____13465 =
                           let uu____13466 =
                             let uu____13481 =
                               let uu____13484 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13484; wp] in
                             (repr, uu____13481) in
                           FStar_Syntax_Syntax.Tm_app uu____13466 in
                         FStar_Syntax_Syntax.mk uu____13465 in
                       uu____13462 FStar_Pervasives_Native.None uu____13461 in
                     FStar_Pervasives_Native.Some uu____13458)
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
          let uu____13530 =
            let uu____13531 =
              let uu____13536 =
                let uu____13537 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13537 in
              let uu____13538 = get_range env in (uu____13536, uu____13538) in
            FStar_Errors.Error uu____13531 in
          FStar_Exn.raise uu____13530 in
        let uu____13539 = effect_repr_aux true env c u_c in
        match uu____13539 with
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
      | uu____13573 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13580 =
        let uu____13581 = FStar_Syntax_Subst.compress t in
        uu____13581.FStar_Syntax_Syntax.n in
      match uu____13580 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13584,c) ->
          is_reifiable_comp env c
      | uu____13602 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13624)::uu____13625 -> x :: rest
        | (Binding_sig_inst uu____13634)::uu____13635 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13650 = push1 x rest1 in local :: uu____13650 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___200_13654 = env in
       let uu____13655 = push1 s env.gamma in
       {
         solver = (uu___200_13654.solver);
         range = (uu___200_13654.range);
         curmodule = (uu___200_13654.curmodule);
         gamma = uu____13655;
         gamma_cache = (uu___200_13654.gamma_cache);
         modules = (uu___200_13654.modules);
         expected_typ = (uu___200_13654.expected_typ);
         sigtab = (uu___200_13654.sigtab);
         is_pattern = (uu___200_13654.is_pattern);
         instantiate_imp = (uu___200_13654.instantiate_imp);
         effects = (uu___200_13654.effects);
         generalize = (uu___200_13654.generalize);
         letrecs = (uu___200_13654.letrecs);
         top_level = (uu___200_13654.top_level);
         check_uvars = (uu___200_13654.check_uvars);
         use_eq = (uu___200_13654.use_eq);
         is_iface = (uu___200_13654.is_iface);
         admit = (uu___200_13654.admit);
         lax = (uu___200_13654.lax);
         lax_universes = (uu___200_13654.lax_universes);
         failhard = (uu___200_13654.failhard);
         nosynth = (uu___200_13654.nosynth);
         tc_term = (uu___200_13654.tc_term);
         type_of = (uu___200_13654.type_of);
         universe_of = (uu___200_13654.universe_of);
         use_bv_sorts = (uu___200_13654.use_bv_sorts);
         qname_and_index = (uu___200_13654.qname_and_index);
         proof_ns = (uu___200_13654.proof_ns);
         synth = (uu___200_13654.synth);
         is_native_tactic = (uu___200_13654.is_native_tactic);
         identifier_info = (uu___200_13654.identifier_info);
         tc_hooks = (uu___200_13654.tc_hooks);
         dsenv = (uu___200_13654.dsenv);
         dep_graph = (uu___200_13654.dep_graph)
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
      let uu___201_13685 = env in
      {
        solver = (uu___201_13685.solver);
        range = (uu___201_13685.range);
        curmodule = (uu___201_13685.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___201_13685.gamma_cache);
        modules = (uu___201_13685.modules);
        expected_typ = (uu___201_13685.expected_typ);
        sigtab = (uu___201_13685.sigtab);
        is_pattern = (uu___201_13685.is_pattern);
        instantiate_imp = (uu___201_13685.instantiate_imp);
        effects = (uu___201_13685.effects);
        generalize = (uu___201_13685.generalize);
        letrecs = (uu___201_13685.letrecs);
        top_level = (uu___201_13685.top_level);
        check_uvars = (uu___201_13685.check_uvars);
        use_eq = (uu___201_13685.use_eq);
        is_iface = (uu___201_13685.is_iface);
        admit = (uu___201_13685.admit);
        lax = (uu___201_13685.lax);
        lax_universes = (uu___201_13685.lax_universes);
        failhard = (uu___201_13685.failhard);
        nosynth = (uu___201_13685.nosynth);
        tc_term = (uu___201_13685.tc_term);
        type_of = (uu___201_13685.type_of);
        universe_of = (uu___201_13685.universe_of);
        use_bv_sorts = (uu___201_13685.use_bv_sorts);
        qname_and_index = (uu___201_13685.qname_and_index);
        proof_ns = (uu___201_13685.proof_ns);
        synth = (uu___201_13685.synth);
        is_native_tactic = (uu___201_13685.is_native_tactic);
        identifier_info = (uu___201_13685.identifier_info);
        tc_hooks = (uu___201_13685.tc_hooks);
        dsenv = (uu___201_13685.dsenv);
        dep_graph = (uu___201_13685.dep_graph)
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
            (let uu___202_13716 = env in
             {
               solver = (uu___202_13716.solver);
               range = (uu___202_13716.range);
               curmodule = (uu___202_13716.curmodule);
               gamma = rest;
               gamma_cache = (uu___202_13716.gamma_cache);
               modules = (uu___202_13716.modules);
               expected_typ = (uu___202_13716.expected_typ);
               sigtab = (uu___202_13716.sigtab);
               is_pattern = (uu___202_13716.is_pattern);
               instantiate_imp = (uu___202_13716.instantiate_imp);
               effects = (uu___202_13716.effects);
               generalize = (uu___202_13716.generalize);
               letrecs = (uu___202_13716.letrecs);
               top_level = (uu___202_13716.top_level);
               check_uvars = (uu___202_13716.check_uvars);
               use_eq = (uu___202_13716.use_eq);
               is_iface = (uu___202_13716.is_iface);
               admit = (uu___202_13716.admit);
               lax = (uu___202_13716.lax);
               lax_universes = (uu___202_13716.lax_universes);
               failhard = (uu___202_13716.failhard);
               nosynth = (uu___202_13716.nosynth);
               tc_term = (uu___202_13716.tc_term);
               type_of = (uu___202_13716.type_of);
               universe_of = (uu___202_13716.universe_of);
               use_bv_sorts = (uu___202_13716.use_bv_sorts);
               qname_and_index = (uu___202_13716.qname_and_index);
               proof_ns = (uu___202_13716.proof_ns);
               synth = (uu___202_13716.synth);
               is_native_tactic = (uu___202_13716.is_native_tactic);
               identifier_info = (uu___202_13716.identifier_info);
               tc_hooks = (uu___202_13716.tc_hooks);
               dsenv = (uu___202_13716.dsenv);
               dep_graph = (uu___202_13716.dep_graph)
             }))
    | uu____13717 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13739  ->
             match uu____13739 with | (x,uu____13745) -> push_bv env1 x) env
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
            let uu___203_13773 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___203_13773.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___203_13773.FStar_Syntax_Syntax.index);
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
      (let uu___204_13803 = env in
       {
         solver = (uu___204_13803.solver);
         range = (uu___204_13803.range);
         curmodule = (uu___204_13803.curmodule);
         gamma = [];
         gamma_cache = (uu___204_13803.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___204_13803.sigtab);
         is_pattern = (uu___204_13803.is_pattern);
         instantiate_imp = (uu___204_13803.instantiate_imp);
         effects = (uu___204_13803.effects);
         generalize = (uu___204_13803.generalize);
         letrecs = (uu___204_13803.letrecs);
         top_level = (uu___204_13803.top_level);
         check_uvars = (uu___204_13803.check_uvars);
         use_eq = (uu___204_13803.use_eq);
         is_iface = (uu___204_13803.is_iface);
         admit = (uu___204_13803.admit);
         lax = (uu___204_13803.lax);
         lax_universes = (uu___204_13803.lax_universes);
         failhard = (uu___204_13803.failhard);
         nosynth = (uu___204_13803.nosynth);
         tc_term = (uu___204_13803.tc_term);
         type_of = (uu___204_13803.type_of);
         universe_of = (uu___204_13803.universe_of);
         use_bv_sorts = (uu___204_13803.use_bv_sorts);
         qname_and_index = (uu___204_13803.qname_and_index);
         proof_ns = (uu___204_13803.proof_ns);
         synth = (uu___204_13803.synth);
         is_native_tactic = (uu___204_13803.is_native_tactic);
         identifier_info = (uu___204_13803.identifier_info);
         tc_hooks = (uu___204_13803.tc_hooks);
         dsenv = (uu___204_13803.dsenv);
         dep_graph = (uu___204_13803.dep_graph)
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
        let uu____13835 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13835 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13863 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13863)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___205_13876 = env in
      {
        solver = (uu___205_13876.solver);
        range = (uu___205_13876.range);
        curmodule = (uu___205_13876.curmodule);
        gamma = (uu___205_13876.gamma);
        gamma_cache = (uu___205_13876.gamma_cache);
        modules = (uu___205_13876.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___205_13876.sigtab);
        is_pattern = (uu___205_13876.is_pattern);
        instantiate_imp = (uu___205_13876.instantiate_imp);
        effects = (uu___205_13876.effects);
        generalize = (uu___205_13876.generalize);
        letrecs = (uu___205_13876.letrecs);
        top_level = (uu___205_13876.top_level);
        check_uvars = (uu___205_13876.check_uvars);
        use_eq = false;
        is_iface = (uu___205_13876.is_iface);
        admit = (uu___205_13876.admit);
        lax = (uu___205_13876.lax);
        lax_universes = (uu___205_13876.lax_universes);
        failhard = (uu___205_13876.failhard);
        nosynth = (uu___205_13876.nosynth);
        tc_term = (uu___205_13876.tc_term);
        type_of = (uu___205_13876.type_of);
        universe_of = (uu___205_13876.universe_of);
        use_bv_sorts = (uu___205_13876.use_bv_sorts);
        qname_and_index = (uu___205_13876.qname_and_index);
        proof_ns = (uu___205_13876.proof_ns);
        synth = (uu___205_13876.synth);
        is_native_tactic = (uu___205_13876.is_native_tactic);
        identifier_info = (uu___205_13876.identifier_info);
        tc_hooks = (uu___205_13876.tc_hooks);
        dsenv = (uu___205_13876.dsenv);
        dep_graph = (uu___205_13876.dep_graph)
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
    let uu____13900 = expected_typ env_ in
    ((let uu___206_13906 = env_ in
      {
        solver = (uu___206_13906.solver);
        range = (uu___206_13906.range);
        curmodule = (uu___206_13906.curmodule);
        gamma = (uu___206_13906.gamma);
        gamma_cache = (uu___206_13906.gamma_cache);
        modules = (uu___206_13906.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___206_13906.sigtab);
        is_pattern = (uu___206_13906.is_pattern);
        instantiate_imp = (uu___206_13906.instantiate_imp);
        effects = (uu___206_13906.effects);
        generalize = (uu___206_13906.generalize);
        letrecs = (uu___206_13906.letrecs);
        top_level = (uu___206_13906.top_level);
        check_uvars = (uu___206_13906.check_uvars);
        use_eq = false;
        is_iface = (uu___206_13906.is_iface);
        admit = (uu___206_13906.admit);
        lax = (uu___206_13906.lax);
        lax_universes = (uu___206_13906.lax_universes);
        failhard = (uu___206_13906.failhard);
        nosynth = (uu___206_13906.nosynth);
        tc_term = (uu___206_13906.tc_term);
        type_of = (uu___206_13906.type_of);
        universe_of = (uu___206_13906.universe_of);
        use_bv_sorts = (uu___206_13906.use_bv_sorts);
        qname_and_index = (uu___206_13906.qname_and_index);
        proof_ns = (uu___206_13906.proof_ns);
        synth = (uu___206_13906.synth);
        is_native_tactic = (uu___206_13906.is_native_tactic);
        identifier_info = (uu___206_13906.identifier_info);
        tc_hooks = (uu___206_13906.tc_hooks);
        dsenv = (uu___206_13906.dsenv);
        dep_graph = (uu___206_13906.dep_graph)
      }), uu____13900)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13919 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___180_13929  ->
                    match uu___180_13929 with
                    | Binding_sig (uu____13932,se) -> [se]
                    | uu____13938 -> [])) in
          FStar_All.pipe_right uu____13919 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___207_13945 = env in
       {
         solver = (uu___207_13945.solver);
         range = (uu___207_13945.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___207_13945.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___207_13945.expected_typ);
         sigtab = (uu___207_13945.sigtab);
         is_pattern = (uu___207_13945.is_pattern);
         instantiate_imp = (uu___207_13945.instantiate_imp);
         effects = (uu___207_13945.effects);
         generalize = (uu___207_13945.generalize);
         letrecs = (uu___207_13945.letrecs);
         top_level = (uu___207_13945.top_level);
         check_uvars = (uu___207_13945.check_uvars);
         use_eq = (uu___207_13945.use_eq);
         is_iface = (uu___207_13945.is_iface);
         admit = (uu___207_13945.admit);
         lax = (uu___207_13945.lax);
         lax_universes = (uu___207_13945.lax_universes);
         failhard = (uu___207_13945.failhard);
         nosynth = (uu___207_13945.nosynth);
         tc_term = (uu___207_13945.tc_term);
         type_of = (uu___207_13945.type_of);
         universe_of = (uu___207_13945.universe_of);
         use_bv_sorts = (uu___207_13945.use_bv_sorts);
         qname_and_index = (uu___207_13945.qname_and_index);
         proof_ns = (uu___207_13945.proof_ns);
         synth = (uu___207_13945.synth);
         is_native_tactic = (uu___207_13945.is_native_tactic);
         identifier_info = (uu___207_13945.identifier_info);
         tc_hooks = (uu___207_13945.tc_hooks);
         dsenv = (uu___207_13945.dsenv);
         dep_graph = (uu___207_13945.dep_graph)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14026)::tl1 -> aux out tl1
      | (Binding_lid (uu____14030,(uu____14031,t)))::tl1 ->
          let uu____14046 =
            let uu____14053 = FStar_Syntax_Free.uvars t in
            ext out uu____14053 in
          aux uu____14046 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14060;
            FStar_Syntax_Syntax.index = uu____14061;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14068 =
            let uu____14075 = FStar_Syntax_Free.uvars t in
            ext out uu____14075 in
          aux uu____14068 tl1
      | (Binding_sig uu____14082)::uu____14083 -> out
      | (Binding_sig_inst uu____14092)::uu____14093 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14148)::tl1 -> aux out tl1
      | (Binding_univ uu____14160)::tl1 -> aux out tl1
      | (Binding_lid (uu____14164,(uu____14165,t)))::tl1 ->
          let uu____14180 =
            let uu____14183 = FStar_Syntax_Free.univs t in
            ext out uu____14183 in
          aux uu____14180 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14186;
            FStar_Syntax_Syntax.index = uu____14187;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14194 =
            let uu____14197 = FStar_Syntax_Free.univs t in
            ext out uu____14197 in
          aux uu____14194 tl1
      | (Binding_sig uu____14200)::uu____14201 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14254)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14270 = FStar_Util.fifo_set_add uname out in
          aux uu____14270 tl1
      | (Binding_lid (uu____14273,(uu____14274,t)))::tl1 ->
          let uu____14289 =
            let uu____14292 = FStar_Syntax_Free.univnames t in
            ext out uu____14292 in
          aux uu____14289 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14295;
            FStar_Syntax_Syntax.index = uu____14296;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14303 =
            let uu____14306 = FStar_Syntax_Free.univnames t in
            ext out uu____14306 in
          aux uu____14303 tl1
      | (Binding_sig uu____14309)::uu____14310 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___181_14334  ->
            match uu___181_14334 with
            | Binding_var x -> [x]
            | Binding_lid uu____14338 -> []
            | Binding_sig uu____14343 -> []
            | Binding_univ uu____14350 -> []
            | Binding_sig_inst uu____14351 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14367 =
      let uu____14370 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14370
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14367 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14392 =
      let uu____14393 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___182_14403  ->
                match uu___182_14403 with
                | Binding_var x ->
                    let uu____14405 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14405
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14408) ->
                    let uu____14409 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14409
                | Binding_sig (ls,uu____14411) ->
                    let uu____14416 =
                      let uu____14417 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14417
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14416
                | Binding_sig_inst (ls,uu____14427,uu____14428) ->
                    let uu____14433 =
                      let uu____14434 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14434
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14433)) in
      FStar_All.pipe_right uu____14393 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14392 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14451 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14451
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14479  ->
                 fun uu____14480  ->
                   match (uu____14479, uu____14480) with
                   | ((b1,uu____14498),(b2,uu____14500)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___183_14542  ->
    match uu___183_14542 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14543 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___184_14561  ->
             match uu___184_14561 with
             | Binding_sig (lids,uu____14567) -> FStar_List.append lids keys
             | uu____14572 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14578  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14612) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14631,uu____14632) -> false in
      let uu____14641 =
        FStar_List.tryFind
          (fun uu____14659  ->
             match uu____14659 with | (p,uu____14667) -> list_prefix p path)
          env.proof_ns in
      match uu____14641 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14678,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14696 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14696
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___208_14708 = e in
        {
          solver = (uu___208_14708.solver);
          range = (uu___208_14708.range);
          curmodule = (uu___208_14708.curmodule);
          gamma = (uu___208_14708.gamma);
          gamma_cache = (uu___208_14708.gamma_cache);
          modules = (uu___208_14708.modules);
          expected_typ = (uu___208_14708.expected_typ);
          sigtab = (uu___208_14708.sigtab);
          is_pattern = (uu___208_14708.is_pattern);
          instantiate_imp = (uu___208_14708.instantiate_imp);
          effects = (uu___208_14708.effects);
          generalize = (uu___208_14708.generalize);
          letrecs = (uu___208_14708.letrecs);
          top_level = (uu___208_14708.top_level);
          check_uvars = (uu___208_14708.check_uvars);
          use_eq = (uu___208_14708.use_eq);
          is_iface = (uu___208_14708.is_iface);
          admit = (uu___208_14708.admit);
          lax = (uu___208_14708.lax);
          lax_universes = (uu___208_14708.lax_universes);
          failhard = (uu___208_14708.failhard);
          nosynth = (uu___208_14708.nosynth);
          tc_term = (uu___208_14708.tc_term);
          type_of = (uu___208_14708.type_of);
          universe_of = (uu___208_14708.universe_of);
          use_bv_sorts = (uu___208_14708.use_bv_sorts);
          qname_and_index = (uu___208_14708.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___208_14708.synth);
          is_native_tactic = (uu___208_14708.is_native_tactic);
          identifier_info = (uu___208_14708.identifier_info);
          tc_hooks = (uu___208_14708.tc_hooks);
          dsenv = (uu___208_14708.dsenv);
          dep_graph = (uu___208_14708.dep_graph)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___209_14734 = e in
      {
        solver = (uu___209_14734.solver);
        range = (uu___209_14734.range);
        curmodule = (uu___209_14734.curmodule);
        gamma = (uu___209_14734.gamma);
        gamma_cache = (uu___209_14734.gamma_cache);
        modules = (uu___209_14734.modules);
        expected_typ = (uu___209_14734.expected_typ);
        sigtab = (uu___209_14734.sigtab);
        is_pattern = (uu___209_14734.is_pattern);
        instantiate_imp = (uu___209_14734.instantiate_imp);
        effects = (uu___209_14734.effects);
        generalize = (uu___209_14734.generalize);
        letrecs = (uu___209_14734.letrecs);
        top_level = (uu___209_14734.top_level);
        check_uvars = (uu___209_14734.check_uvars);
        use_eq = (uu___209_14734.use_eq);
        is_iface = (uu___209_14734.is_iface);
        admit = (uu___209_14734.admit);
        lax = (uu___209_14734.lax);
        lax_universes = (uu___209_14734.lax_universes);
        failhard = (uu___209_14734.failhard);
        nosynth = (uu___209_14734.nosynth);
        tc_term = (uu___209_14734.tc_term);
        type_of = (uu___209_14734.type_of);
        universe_of = (uu___209_14734.universe_of);
        use_bv_sorts = (uu___209_14734.use_bv_sorts);
        qname_and_index = (uu___209_14734.qname_and_index);
        proof_ns = ns;
        synth = (uu___209_14734.synth);
        is_native_tactic = (uu___209_14734.is_native_tactic);
        identifier_info = (uu___209_14734.identifier_info);
        tc_hooks = (uu___209_14734.tc_hooks);
        dsenv = (uu___209_14734.dsenv);
        dep_graph = (uu___209_14734.dep_graph)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14745 = FStar_Syntax_Free.names t in
      let uu____14748 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14745 uu____14748
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14765 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14765
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14771 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14771
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14786 =
      match uu____14786 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14802 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14802) in
    let uu____14804 =
      let uu____14807 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14807 FStar_List.rev in
    FStar_All.pipe_right uu____14804 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14824  -> ());
    push = (fun uu____14826  -> ());
    pop = (fun uu____14828  -> ());
    encode_modul = (fun uu____14831  -> fun uu____14832  -> ());
    encode_sig = (fun uu____14835  -> fun uu____14836  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14842 =
             let uu____14849 = FStar_Options.peek () in (e, g, uu____14849) in
           [uu____14842]);
    solve = (fun uu____14865  -> fun uu____14866  -> fun uu____14867  -> ());
    finish = (fun uu____14873  -> ());
    refresh = (fun uu____14875  -> ())
  }