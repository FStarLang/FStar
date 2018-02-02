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
           (fun uu___70_5079  ->
              match uu___70_5079 with
              | Binding_var x ->
                  let y =
                    let uu____5082 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____5082 in
                  let uu____5083 =
                    let uu____5084 = FStar_Syntax_Subst.compress y in
                    uu____5084.FStar_Syntax_Syntax.n in
                  (match uu____5083 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5088 =
                         let uu___85_5089 = y1 in
                         let uu____5090 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___85_5089.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___85_5089.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5090
                         } in
                       Binding_var uu____5088
                   | uu____5093 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___86_5101 = env in
      let uu____5102 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___86_5101.solver);
        range = (uu___86_5101.range);
        curmodule = (uu___86_5101.curmodule);
        gamma = uu____5102;
        gamma_cache = (uu___86_5101.gamma_cache);
        modules = (uu___86_5101.modules);
        expected_typ = (uu___86_5101.expected_typ);
        sigtab = (uu___86_5101.sigtab);
        is_pattern = (uu___86_5101.is_pattern);
        instantiate_imp = (uu___86_5101.instantiate_imp);
        effects = (uu___86_5101.effects);
        generalize = (uu___86_5101.generalize);
        letrecs = (uu___86_5101.letrecs);
        top_level = (uu___86_5101.top_level);
        check_uvars = (uu___86_5101.check_uvars);
        use_eq = (uu___86_5101.use_eq);
        is_iface = (uu___86_5101.is_iface);
        admit = (uu___86_5101.admit);
        lax = (uu___86_5101.lax);
        lax_universes = (uu___86_5101.lax_universes);
        failhard = (uu___86_5101.failhard);
        nosynth = (uu___86_5101.nosynth);
        tc_term = (uu___86_5101.tc_term);
        type_of = (uu___86_5101.type_of);
        universe_of = (uu___86_5101.universe_of);
        use_bv_sorts = (uu___86_5101.use_bv_sorts);
        qname_and_index = (uu___86_5101.qname_and_index);
        proof_ns = (uu___86_5101.proof_ns);
        synth = (uu___86_5101.synth);
        is_native_tactic = (uu___86_5101.is_native_tactic);
        identifier_info = (uu___86_5101.identifier_info);
        tc_hooks = (uu___86_5101.tc_hooks);
        dsenv = (uu___86_5101.dsenv);
        dep_graph = (uu___86_5101.dep_graph)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5109  -> fun uu____5110  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___87_5120 = env in
      {
        solver = (uu___87_5120.solver);
        range = (uu___87_5120.range);
        curmodule = (uu___87_5120.curmodule);
        gamma = (uu___87_5120.gamma);
        gamma_cache = (uu___87_5120.gamma_cache);
        modules = (uu___87_5120.modules);
        expected_typ = (uu___87_5120.expected_typ);
        sigtab = (uu___87_5120.sigtab);
        is_pattern = (uu___87_5120.is_pattern);
        instantiate_imp = (uu___87_5120.instantiate_imp);
        effects = (uu___87_5120.effects);
        generalize = (uu___87_5120.generalize);
        letrecs = (uu___87_5120.letrecs);
        top_level = (uu___87_5120.top_level);
        check_uvars = (uu___87_5120.check_uvars);
        use_eq = (uu___87_5120.use_eq);
        is_iface = (uu___87_5120.is_iface);
        admit = (uu___87_5120.admit);
        lax = (uu___87_5120.lax);
        lax_universes = (uu___87_5120.lax_universes);
        failhard = (uu___87_5120.failhard);
        nosynth = (uu___87_5120.nosynth);
        tc_term = (uu___87_5120.tc_term);
        type_of = (uu___87_5120.type_of);
        universe_of = (uu___87_5120.universe_of);
        use_bv_sorts = (uu___87_5120.use_bv_sorts);
        qname_and_index = (uu___87_5120.qname_and_index);
        proof_ns = (uu___87_5120.proof_ns);
        synth = (uu___87_5120.synth);
        is_native_tactic = (uu___87_5120.is_native_tactic);
        identifier_info = (uu___87_5120.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___87_5120.dsenv);
        dep_graph = (uu___87_5120.dep_graph)
      }
let set_dep_graph: env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___88_5127 = e in
      {
        solver = (uu___88_5127.solver);
        range = (uu___88_5127.range);
        curmodule = (uu___88_5127.curmodule);
        gamma = (uu___88_5127.gamma);
        gamma_cache = (uu___88_5127.gamma_cache);
        modules = (uu___88_5127.modules);
        expected_typ = (uu___88_5127.expected_typ);
        sigtab = (uu___88_5127.sigtab);
        is_pattern = (uu___88_5127.is_pattern);
        instantiate_imp = (uu___88_5127.instantiate_imp);
        effects = (uu___88_5127.effects);
        generalize = (uu___88_5127.generalize);
        letrecs = (uu___88_5127.letrecs);
        top_level = (uu___88_5127.top_level);
        check_uvars = (uu___88_5127.check_uvars);
        use_eq = (uu___88_5127.use_eq);
        is_iface = (uu___88_5127.is_iface);
        admit = (uu___88_5127.admit);
        lax = (uu___88_5127.lax);
        lax_universes = (uu___88_5127.lax_universes);
        failhard = (uu___88_5127.failhard);
        nosynth = (uu___88_5127.nosynth);
        tc_term = (uu___88_5127.tc_term);
        type_of = (uu___88_5127.type_of);
        universe_of = (uu___88_5127.universe_of);
        use_bv_sorts = (uu___88_5127.use_bv_sorts);
        qname_and_index = (uu___88_5127.qname_and_index);
        proof_ns = (uu___88_5127.proof_ns);
        synth = (uu___88_5127.synth);
        is_native_tactic = (uu___88_5127.is_native_tactic);
        identifier_info = (uu___88_5127.identifier_info);
        tc_hooks = (uu___88_5127.tc_hooks);
        dsenv = (uu___88_5127.dsenv);
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
      | (NoDelta ,uu____5142) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5143,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5144,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5145 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5152 . Prims.unit -> 'Auu____5152 FStar_Util.smap =
  fun uu____5158  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5161 . Prims.unit -> 'Auu____5161 FStar_Util.smap =
  fun uu____5167  -> FStar_Util.smap_create (Prims.parse_int "100")
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
              let uu____5240 = new_gamma_cache () in
              let uu____5243 = new_sigtab () in
              let uu____5246 = FStar_Options.using_facts_from () in
              let uu____5247 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty in
              let uu____5250 = FStar_ToSyntax_Env.empty_env () in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5240;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5243;
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
                proof_ns = uu____5246;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5284  -> false);
                identifier_info = uu____5247;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5250;
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
  fun uu____5364  ->
    let uu____5365 = FStar_ST.op_Bang query_indices in
    match uu____5365 with
    | [] -> failwith "Empty query indices!"
    | uu____5415 ->
        let uu____5424 =
          let uu____5433 =
            let uu____5440 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5440 in
          let uu____5490 = FStar_ST.op_Bang query_indices in uu____5433 ::
            uu____5490 in
        FStar_ST.op_Colon_Equals query_indices uu____5424
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5577  ->
    let uu____5578 = FStar_ST.op_Bang query_indices in
    match uu____5578 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5691  ->
    match uu____5691 with
    | (l,n1) ->
        let uu____5698 = FStar_ST.op_Bang query_indices in
        (match uu____5698 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5809 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5826  ->
    let uu____5827 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5827
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5898 =
       let uu____5901 = FStar_ST.op_Bang stack in env :: uu____5901 in
     FStar_ST.op_Colon_Equals stack uu____5898);
    (let uu___89_5950 = env in
     let uu____5951 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5954 = FStar_Util.smap_copy (sigtab env) in
     let uu____5957 =
       let uu____5960 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5960 in
     {
       solver = (uu___89_5950.solver);
       range = (uu___89_5950.range);
       curmodule = (uu___89_5950.curmodule);
       gamma = (uu___89_5950.gamma);
       gamma_cache = uu____5951;
       modules = (uu___89_5950.modules);
       expected_typ = (uu___89_5950.expected_typ);
       sigtab = uu____5954;
       is_pattern = (uu___89_5950.is_pattern);
       instantiate_imp = (uu___89_5950.instantiate_imp);
       effects = (uu___89_5950.effects);
       generalize = (uu___89_5950.generalize);
       letrecs = (uu___89_5950.letrecs);
       top_level = (uu___89_5950.top_level);
       check_uvars = (uu___89_5950.check_uvars);
       use_eq = (uu___89_5950.use_eq);
       is_iface = (uu___89_5950.is_iface);
       admit = (uu___89_5950.admit);
       lax = (uu___89_5950.lax);
       lax_universes = (uu___89_5950.lax_universes);
       failhard = (uu___89_5950.failhard);
       nosynth = (uu___89_5950.nosynth);
       tc_term = (uu___89_5950.tc_term);
       type_of = (uu___89_5950.type_of);
       universe_of = (uu___89_5950.universe_of);
       use_bv_sorts = (uu___89_5950.use_bv_sorts);
       qname_and_index = (uu___89_5950.qname_and_index);
       proof_ns = (uu___89_5950.proof_ns);
       synth = (uu___89_5950.synth);
       is_native_tactic = (uu___89_5950.is_native_tactic);
       identifier_info = uu____5957;
       tc_hooks = (uu___89_5950.tc_hooks);
       dsenv = (uu___89_5950.dsenv);
       dep_graph = (uu___89_5950.dep_graph)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6004  ->
    let uu____6005 = FStar_ST.op_Bang stack in
    match uu____6005 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6059 -> failwith "Impossible: Too many pops"
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
        let uu____6098 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6124  ->
                  match uu____6124 with
                  | (m,uu____6130) -> FStar_Ident.lid_equals l m)) in
        (match uu____6098 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___90_6137 = env in
               {
                 solver = (uu___90_6137.solver);
                 range = (uu___90_6137.range);
                 curmodule = (uu___90_6137.curmodule);
                 gamma = (uu___90_6137.gamma);
                 gamma_cache = (uu___90_6137.gamma_cache);
                 modules = (uu___90_6137.modules);
                 expected_typ = (uu___90_6137.expected_typ);
                 sigtab = (uu___90_6137.sigtab);
                 is_pattern = (uu___90_6137.is_pattern);
                 instantiate_imp = (uu___90_6137.instantiate_imp);
                 effects = (uu___90_6137.effects);
                 generalize = (uu___90_6137.generalize);
                 letrecs = (uu___90_6137.letrecs);
                 top_level = (uu___90_6137.top_level);
                 check_uvars = (uu___90_6137.check_uvars);
                 use_eq = (uu___90_6137.use_eq);
                 is_iface = (uu___90_6137.is_iface);
                 admit = (uu___90_6137.admit);
                 lax = (uu___90_6137.lax);
                 lax_universes = (uu___90_6137.lax_universes);
                 failhard = (uu___90_6137.failhard);
                 nosynth = (uu___90_6137.nosynth);
                 tc_term = (uu___90_6137.tc_term);
                 type_of = (uu___90_6137.type_of);
                 universe_of = (uu___90_6137.universe_of);
                 use_bv_sorts = (uu___90_6137.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___90_6137.proof_ns);
                 synth = (uu___90_6137.synth);
                 is_native_tactic = (uu___90_6137.is_native_tactic);
                 identifier_info = (uu___90_6137.identifier_info);
                 tc_hooks = (uu___90_6137.tc_hooks);
                 dsenv = (uu___90_6137.dsenv);
                 dep_graph = (uu___90_6137.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6142,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___91_6150 = env in
               {
                 solver = (uu___91_6150.solver);
                 range = (uu___91_6150.range);
                 curmodule = (uu___91_6150.curmodule);
                 gamma = (uu___91_6150.gamma);
                 gamma_cache = (uu___91_6150.gamma_cache);
                 modules = (uu___91_6150.modules);
                 expected_typ = (uu___91_6150.expected_typ);
                 sigtab = (uu___91_6150.sigtab);
                 is_pattern = (uu___91_6150.is_pattern);
                 instantiate_imp = (uu___91_6150.instantiate_imp);
                 effects = (uu___91_6150.effects);
                 generalize = (uu___91_6150.generalize);
                 letrecs = (uu___91_6150.letrecs);
                 top_level = (uu___91_6150.top_level);
                 check_uvars = (uu___91_6150.check_uvars);
                 use_eq = (uu___91_6150.use_eq);
                 is_iface = (uu___91_6150.is_iface);
                 admit = (uu___91_6150.admit);
                 lax = (uu___91_6150.lax);
                 lax_universes = (uu___91_6150.lax_universes);
                 failhard = (uu___91_6150.failhard);
                 nosynth = (uu___91_6150.nosynth);
                 tc_term = (uu___91_6150.tc_term);
                 type_of = (uu___91_6150.type_of);
                 universe_of = (uu___91_6150.universe_of);
                 use_bv_sorts = (uu___91_6150.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___91_6150.proof_ns);
                 synth = (uu___91_6150.synth);
                 is_native_tactic = (uu___91_6150.is_native_tactic);
                 identifier_info = (uu___91_6150.identifier_info);
                 tc_hooks = (uu___91_6150.tc_hooks);
                 dsenv = (uu___91_6150.dsenv);
                 dep_graph = (uu___91_6150.dep_graph)
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
        (let uu___92_6168 = e in
         {
           solver = (uu___92_6168.solver);
           range = r;
           curmodule = (uu___92_6168.curmodule);
           gamma = (uu___92_6168.gamma);
           gamma_cache = (uu___92_6168.gamma_cache);
           modules = (uu___92_6168.modules);
           expected_typ = (uu___92_6168.expected_typ);
           sigtab = (uu___92_6168.sigtab);
           is_pattern = (uu___92_6168.is_pattern);
           instantiate_imp = (uu___92_6168.instantiate_imp);
           effects = (uu___92_6168.effects);
           generalize = (uu___92_6168.generalize);
           letrecs = (uu___92_6168.letrecs);
           top_level = (uu___92_6168.top_level);
           check_uvars = (uu___92_6168.check_uvars);
           use_eq = (uu___92_6168.use_eq);
           is_iface = (uu___92_6168.is_iface);
           admit = (uu___92_6168.admit);
           lax = (uu___92_6168.lax);
           lax_universes = (uu___92_6168.lax_universes);
           failhard = (uu___92_6168.failhard);
           nosynth = (uu___92_6168.nosynth);
           tc_term = (uu___92_6168.tc_term);
           type_of = (uu___92_6168.type_of);
           universe_of = (uu___92_6168.universe_of);
           use_bv_sorts = (uu___92_6168.use_bv_sorts);
           qname_and_index = (uu___92_6168.qname_and_index);
           proof_ns = (uu___92_6168.proof_ns);
           synth = (uu___92_6168.synth);
           is_native_tactic = (uu___92_6168.is_native_tactic);
           identifier_info = (uu___92_6168.identifier_info);
           tc_hooks = (uu___92_6168.tc_hooks);
           dsenv = (uu___92_6168.dsenv);
           dep_graph = (uu___92_6168.dep_graph)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6178 =
        let uu____6179 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6179 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6178
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6227 =
          let uu____6228 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6228 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6227
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6276 =
          let uu____6277 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6277 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6276
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6327 =
        let uu____6328 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6328 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6327
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___93_6381 = env in
      {
        solver = (uu___93_6381.solver);
        range = (uu___93_6381.range);
        curmodule = lid;
        gamma = (uu___93_6381.gamma);
        gamma_cache = (uu___93_6381.gamma_cache);
        modules = (uu___93_6381.modules);
        expected_typ = (uu___93_6381.expected_typ);
        sigtab = (uu___93_6381.sigtab);
        is_pattern = (uu___93_6381.is_pattern);
        instantiate_imp = (uu___93_6381.instantiate_imp);
        effects = (uu___93_6381.effects);
        generalize = (uu___93_6381.generalize);
        letrecs = (uu___93_6381.letrecs);
        top_level = (uu___93_6381.top_level);
        check_uvars = (uu___93_6381.check_uvars);
        use_eq = (uu___93_6381.use_eq);
        is_iface = (uu___93_6381.is_iface);
        admit = (uu___93_6381.admit);
        lax = (uu___93_6381.lax);
        lax_universes = (uu___93_6381.lax_universes);
        failhard = (uu___93_6381.failhard);
        nosynth = (uu___93_6381.nosynth);
        tc_term = (uu___93_6381.tc_term);
        type_of = (uu___93_6381.type_of);
        universe_of = (uu___93_6381.universe_of);
        use_bv_sorts = (uu___93_6381.use_bv_sorts);
        qname_and_index = (uu___93_6381.qname_and_index);
        proof_ns = (uu___93_6381.proof_ns);
        synth = (uu___93_6381.synth);
        is_native_tactic = (uu___93_6381.is_native_tactic);
        identifier_info = (uu___93_6381.identifier_info);
        tc_hooks = (uu___93_6381.tc_hooks);
        dsenv = (uu___93_6381.dsenv);
        dep_graph = (uu___93_6381.dep_graph)
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
    let uu____6407 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str in
    (FStar_Errors.Fatal_NameNotFound, uu____6407)
let variable_not_found:
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun v1  ->
    let uu____6415 =
      let uu____6416 = FStar_Syntax_Print.bv_to_string v1 in
      FStar_Util.format1 "Variable \"%s\" not found" uu____6416 in
    (FStar_Errors.Fatal_VariableNotFound, uu____6415)
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6419  ->
    let uu____6420 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6420
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
      | ((formals,t),uu____6458) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6482 = FStar_Syntax_Subst.subst vs t in (us, uu____6482)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___71_6495  ->
    match uu___71_6495 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6519  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6532 = inst_tscheme t in
      match uu____6532 with
      | (us,t1) ->
          let uu____6543 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6543)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6555  ->
          match uu____6555 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6570 =
                         let uu____6571 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6572 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6573 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6574 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6571 uu____6572 uu____6573 uu____6574 in
                       failwith uu____6570)
                    else ();
                    (let uu____6576 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6576))
               | uu____6583 ->
                   let uu____6584 =
                     let uu____6585 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6585 in
                   failwith uu____6584)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6589 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6593 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6597 -> false
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
             | ([],uu____6631) -> Maybe
             | (uu____6638,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6657 -> No in
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
          let uu____6762 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6762 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___72_6807  ->
                   match uu___72_6807 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____6850 =
                           let uu____6869 =
                             let uu____6884 = inst_tscheme t in
                             FStar_Util.Inl uu____6884 in
                           (uu____6869, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____6850
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6950,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6952);
                                     FStar_Syntax_Syntax.sigrng = uu____6953;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6954;
                                     FStar_Syntax_Syntax.sigmeta = uu____6955;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6956;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6976 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6976
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7022 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7029 -> cache t in
                       let uu____7030 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7030 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7105 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7105 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7191 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7271 = find_in_sigtab env lid in
         match uu____7271 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7370) ->
          add_sigelts env ses
      | uu____7379 ->
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
            | uu____7393 -> ()))
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
        (fun uu___73_7420  ->
           match uu___73_7420 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7438 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7471,lb::[]),uu____7473) ->
          let uu____7486 =
            let uu____7495 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7504 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7495, uu____7504) in
          FStar_Pervasives_Native.Some uu____7486
      | FStar_Syntax_Syntax.Sig_let ((uu____7517,lbs),uu____7519) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7555 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7567 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7567
                   then
                     let uu____7578 =
                       let uu____7587 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7596 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7587, uu____7596) in
                     FStar_Pervasives_Native.Some uu____7578
                   else FStar_Pervasives_Native.None)
      | uu____7618 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7651 =
          let uu____7660 =
            let uu____7665 =
              let uu____7666 =
                let uu____7669 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7669 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7666) in
            inst_tscheme uu____7665 in
          (uu____7660, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7651
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7689,uu____7690) ->
        let uu____7695 =
          let uu____7704 =
            let uu____7709 =
              let uu____7710 =
                let uu____7713 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7713 in
              (us, uu____7710) in
            inst_tscheme uu____7709 in
          (uu____7704, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7695
    | uu____7730 -> FStar_Pervasives_Native.None
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
      let mapper uu____7788 =
        match uu____7788 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____7884,uvs,t,uu____7887,uu____7888,uu____7889);
                    FStar_Syntax_Syntax.sigrng = uu____7890;
                    FStar_Syntax_Syntax.sigquals = uu____7891;
                    FStar_Syntax_Syntax.sigmeta = uu____7892;
                    FStar_Syntax_Syntax.sigattrs = uu____7893;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7914 =
                   let uu____7923 = inst_tscheme (uvs, t) in
                   (uu____7923, rng) in
                 FStar_Pervasives_Native.Some uu____7914
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7943;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7945;
                    FStar_Syntax_Syntax.sigattrs = uu____7946;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7963 =
                   let uu____7964 = in_cur_mod env l in uu____7964 = Yes in
                 if uu____7963
                 then
                   let uu____7975 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7975
                    then
                      let uu____7988 =
                        let uu____7997 = inst_tscheme (uvs, t) in
                        (uu____7997, rng) in
                      FStar_Pervasives_Native.Some uu____7988
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8024 =
                      let uu____8033 = inst_tscheme (uvs, t) in
                      (uu____8033, rng) in
                    FStar_Pervasives_Native.Some uu____8024)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8054,uu____8055);
                    FStar_Syntax_Syntax.sigrng = uu____8056;
                    FStar_Syntax_Syntax.sigquals = uu____8057;
                    FStar_Syntax_Syntax.sigmeta = uu____8058;
                    FStar_Syntax_Syntax.sigattrs = uu____8059;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8098 =
                        let uu____8107 = inst_tscheme (uvs, k) in
                        (uu____8107, rng) in
                      FStar_Pervasives_Native.Some uu____8098
                  | uu____8124 ->
                      let uu____8125 =
                        let uu____8134 =
                          let uu____8139 =
                            let uu____8140 =
                              let uu____8143 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8143 in
                            (uvs, uu____8140) in
                          inst_tscheme uu____8139 in
                        (uu____8134, rng) in
                      FStar_Pervasives_Native.Some uu____8125)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8164,uu____8165);
                    FStar_Syntax_Syntax.sigrng = uu____8166;
                    FStar_Syntax_Syntax.sigquals = uu____8167;
                    FStar_Syntax_Syntax.sigmeta = uu____8168;
                    FStar_Syntax_Syntax.sigattrs = uu____8169;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8209 =
                        let uu____8218 = inst_tscheme_with (uvs, k) us in
                        (uu____8218, rng) in
                      FStar_Pervasives_Native.Some uu____8209
                  | uu____8235 ->
                      let uu____8236 =
                        let uu____8245 =
                          let uu____8250 =
                            let uu____8251 =
                              let uu____8254 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8254 in
                            (uvs, uu____8251) in
                          inst_tscheme_with uu____8250 us in
                        (uu____8245, rng) in
                      FStar_Pervasives_Native.Some uu____8236)
             | FStar_Util.Inr se ->
                 let uu____8288 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8309;
                        FStar_Syntax_Syntax.sigrng = uu____8310;
                        FStar_Syntax_Syntax.sigquals = uu____8311;
                        FStar_Syntax_Syntax.sigmeta = uu____8312;
                        FStar_Syntax_Syntax.sigattrs = uu____8313;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8328 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8288
                   (FStar_Util.map_option
                      (fun uu____8376  ->
                         match uu____8376 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8407 =
        let uu____8418 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8418 mapper in
      match uu____8407 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___94_8511 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___94_8511.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___94_8511.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8536 = lookup_qname env l in
      match uu____8536 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8575 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8623 = try_lookup_bv env bv in
      match uu____8623 with
      | FStar_Pervasives_Native.None  ->
          let uu____8638 = variable_not_found bv in
          FStar_Errors.raise_error uu____8638 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8653 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8654 =
            let uu____8655 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____8655 in
          (uu____8653, uu____8654)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8672 = try_lookup_lid_aux env l in
      match uu____8672 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____8738 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____8738 in
          let uu____8739 =
            let uu____8748 =
              let uu____8753 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____8753) in
            (uu____8748, r1) in
          FStar_Pervasives_Native.Some uu____8739
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8780 = try_lookup_lid env l in
      match uu____8780 with
      | FStar_Pervasives_Native.None  ->
          let uu____8807 = name_not_found l in
          FStar_Errors.raise_error uu____8807 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___74_8847  ->
              match uu___74_8847 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____8849 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____8864 = lookup_qname env lid in
      match uu____8864 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8893,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8896;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8898;
              FStar_Syntax_Syntax.sigattrs = uu____8899;_},FStar_Pervasives_Native.None
            ),uu____8900)
          ->
          let uu____8949 =
            let uu____8960 =
              let uu____8965 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8965) in
            (uu____8960, q) in
          FStar_Pervasives_Native.Some uu____8949
      | uu____8982 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9019 = lookup_qname env lid in
      match uu____9019 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9044,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9047;
              FStar_Syntax_Syntax.sigquals = uu____9048;
              FStar_Syntax_Syntax.sigmeta = uu____9049;
              FStar_Syntax_Syntax.sigattrs = uu____9050;_},FStar_Pervasives_Native.None
            ),uu____9051)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9100 ->
          let uu____9121 = name_not_found lid in
          FStar_Errors.raise_error uu____9121 (FStar_Ident.range_of_lid lid)
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9140 = lookup_qname env lid in
      match uu____9140 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9165,uvs,t,uu____9168,uu____9169,uu____9170);
              FStar_Syntax_Syntax.sigrng = uu____9171;
              FStar_Syntax_Syntax.sigquals = uu____9172;
              FStar_Syntax_Syntax.sigmeta = uu____9173;
              FStar_Syntax_Syntax.sigattrs = uu____9174;_},FStar_Pervasives_Native.None
            ),uu____9175)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9228 ->
          let uu____9249 = name_not_found lid in
          FStar_Errors.raise_error uu____9249 (FStar_Ident.range_of_lid lid)
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9270 = lookup_qname env lid in
      match uu____9270 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9297,uu____9298,uu____9299,uu____9300,uu____9301,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9303;
              FStar_Syntax_Syntax.sigquals = uu____9304;
              FStar_Syntax_Syntax.sigmeta = uu____9305;
              FStar_Syntax_Syntax.sigattrs = uu____9306;_},uu____9307),uu____9308)
          -> (true, dcs)
      | uu____9369 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9398 = lookup_qname env lid in
      match uu____9398 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9419,uu____9420,uu____9421,l,uu____9423,uu____9424);
              FStar_Syntax_Syntax.sigrng = uu____9425;
              FStar_Syntax_Syntax.sigquals = uu____9426;
              FStar_Syntax_Syntax.sigmeta = uu____9427;
              FStar_Syntax_Syntax.sigattrs = uu____9428;_},uu____9429),uu____9430)
          -> l
      | uu____9485 ->
          let uu____9506 =
            let uu____9507 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9507 in
          failwith uu____9506
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
        let uu____9541 = lookup_qname env lid in
        match uu____9541 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9569) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9620,lbs),uu____9622) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9650 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9650
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9682 -> FStar_Pervasives_Native.None)
        | uu____9687 -> FStar_Pervasives_Native.None
let lookup_attrs_of_lid:
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9726 = lookup_qname env lid in
      match uu____9726 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____9752),uu____9753) ->
          FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
      | uu____9802 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9835 = lookup_qname env ftv in
      match uu____9835 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9859) ->
          let uu____9904 = effect_signature se in
          (match uu____9904 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9925,t),r) ->
               let uu____9940 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____9940)
      | uu____9941 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9968 = try_lookup_effect_lid env ftv in
      match uu____9968 with
      | FStar_Pervasives_Native.None  ->
          let uu____9971 = name_not_found ftv in
          FStar_Errors.raise_error uu____9971 (FStar_Ident.range_of_lid ftv)
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
        let uu____9992 = lookup_qname env lid0 in
        match uu____9992 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10023);
                FStar_Syntax_Syntax.sigrng = uu____10024;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10026;
                FStar_Syntax_Syntax.sigattrs = uu____10027;_},FStar_Pervasives_Native.None
              ),uu____10028)
            ->
            let lid1 =
              let uu____10082 =
                let uu____10083 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10083 in
              FStar_Ident.set_lid_range lid uu____10082 in
            let uu____10084 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___75_10088  ->
                      match uu___75_10088 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10089 -> false)) in
            if uu____10084
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10103 =
                      let uu____10104 =
                        let uu____10105 = get_range env in
                        FStar_Range.string_of_range uu____10105 in
                      let uu____10106 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10107 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10104 uu____10106 uu____10107 in
                    failwith uu____10103) in
               match (binders, univs1) with
               | ([],uu____10114) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10131,uu____10132::uu____10133::uu____10134) ->
                   let uu____10139 =
                     let uu____10140 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10141 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10140 uu____10141 in
                   failwith uu____10139
               | uu____10148 ->
                   let uu____10153 =
                     let uu____10158 =
                       let uu____10159 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10159) in
                     inst_tscheme_with uu____10158 insts in
                   (match uu____10153 with
                    | (uu____10170,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10173 =
                          let uu____10174 = FStar_Syntax_Subst.compress t1 in
                          uu____10174.FStar_Syntax_Syntax.n in
                        (match uu____10173 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10221 -> failwith "Impossible")))
        | uu____10228 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10268 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10268 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10281,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10288 = find1 l2 in
            (match uu____10288 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10295 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10295 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10299 = find1 l in
            (match uu____10299 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10313 = lookup_qname env l1 in
      match uu____10313 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10336;
              FStar_Syntax_Syntax.sigrng = uu____10337;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10339;
              FStar_Syntax_Syntax.sigattrs = uu____10340;_},uu____10341),uu____10342)
          -> q
      | uu____10393 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10426 =
          let uu____10427 =
            let uu____10428 = FStar_Util.string_of_int i in
            let uu____10429 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10428 uu____10429 in
          failwith uu____10427 in
        let uu____10430 = lookup_datacon env lid in
        match uu____10430 with
        | (uu____10435,t) ->
            let uu____10437 =
              let uu____10438 = FStar_Syntax_Subst.compress t in
              uu____10438.FStar_Syntax_Syntax.n in
            (match uu____10437 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10442) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10473 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10473
                      FStar_Pervasives_Native.fst)
             | uu____10482 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10489 = lookup_qname env l in
      match uu____10489 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10510,uu____10511,uu____10512);
              FStar_Syntax_Syntax.sigrng = uu____10513;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10515;
              FStar_Syntax_Syntax.sigattrs = uu____10516;_},uu____10517),uu____10518)
          ->
          FStar_Util.for_some
            (fun uu___76_10571  ->
               match uu___76_10571 with
               | FStar_Syntax_Syntax.Projector uu____10572 -> true
               | uu____10577 -> false) quals
      | uu____10578 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10605 = lookup_qname env lid in
      match uu____10605 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10626,uu____10627,uu____10628,uu____10629,uu____10630,uu____10631);
              FStar_Syntax_Syntax.sigrng = uu____10632;
              FStar_Syntax_Syntax.sigquals = uu____10633;
              FStar_Syntax_Syntax.sigmeta = uu____10634;
              FStar_Syntax_Syntax.sigattrs = uu____10635;_},uu____10636),uu____10637)
          -> true
      | uu____10692 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10719 = lookup_qname env lid in
      match uu____10719 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10740,uu____10741,uu____10742,uu____10743,uu____10744,uu____10745);
              FStar_Syntax_Syntax.sigrng = uu____10746;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10748;
              FStar_Syntax_Syntax.sigattrs = uu____10749;_},uu____10750),uu____10751)
          ->
          FStar_Util.for_some
            (fun uu___77_10812  ->
               match uu___77_10812 with
               | FStar_Syntax_Syntax.RecordType uu____10813 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10822 -> true
               | uu____10831 -> false) quals
      | uu____10832 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10859 = lookup_qname env lid in
      match uu____10859 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____10880,uu____10881);
              FStar_Syntax_Syntax.sigrng = uu____10882;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10884;
              FStar_Syntax_Syntax.sigattrs = uu____10885;_},uu____10886),uu____10887)
          ->
          FStar_Util.for_some
            (fun uu___78_10944  ->
               match uu___78_10944 with
               | FStar_Syntax_Syntax.Action uu____10945 -> true
               | uu____10946 -> false) quals
      | uu____10947 -> false
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
      let uu____10977 =
        let uu____10978 = FStar_Syntax_Util.un_uinst head1 in
        uu____10978.FStar_Syntax_Syntax.n in
      match uu____10977 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10982 -> false
let is_irreducible: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10989 = lookup_qname env l in
      match uu____10989 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____11011),uu____11012) ->
          FStar_Util.for_some
            (fun uu___79_11060  ->
               match uu___79_11060 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____11061 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____11062 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11147 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11163) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11180 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11187 ->
                 FStar_Pervasives_Native.Some true
             | uu____11204 -> FStar_Pervasives_Native.Some false) in
      let uu____11205 =
        let uu____11208 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11208 mapper in
      match uu____11205 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11254 = lookup_qname env lid in
      match uu____11254 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11275,uu____11276,tps,uu____11278,uu____11279,uu____11280);
              FStar_Syntax_Syntax.sigrng = uu____11281;
              FStar_Syntax_Syntax.sigquals = uu____11282;
              FStar_Syntax_Syntax.sigmeta = uu____11283;
              FStar_Syntax_Syntax.sigattrs = uu____11284;_},uu____11285),uu____11286)
          -> FStar_List.length tps
      | uu____11349 ->
          let uu____11370 = name_not_found lid in
          FStar_Errors.raise_error uu____11370 (FStar_Ident.range_of_lid lid)
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
           (fun uu____11414  ->
              match uu____11414 with
              | (d,uu____11422) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11433 = effect_decl_opt env l in
      match uu____11433 with
      | FStar_Pervasives_Native.None  ->
          let uu____11448 = name_not_found l in
          FStar_Errors.raise_error uu____11448 (FStar_Ident.range_of_lid l)
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun uu____11474  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11489  ->
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
            (let uu____11522 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11575  ->
                       match uu____11575 with
                       | (m1,m2,uu____11588,uu____11589,uu____11590) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11522 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11607 =
                   let uu____11612 =
                     let uu____11613 = FStar_Syntax_Print.lid_to_string l1 in
                     let uu____11614 = FStar_Syntax_Print.lid_to_string l2 in
                     FStar_Util.format2
                       "Effects %s and %s cannot be composed" uu____11613
                       uu____11614 in
                   (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____11612) in
                 FStar_Errors.raise_error uu____11607 env.range
             | FStar_Pervasives_Native.Some
                 (uu____11621,uu____11622,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11659 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11659)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11686 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11712  ->
                match uu____11712 with
                | (d,uu____11718) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11686 with
      | FStar_Pervasives_Native.None  ->
          let uu____11729 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11729
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11742 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11742 with
           | (uu____11753,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11763)::(wp,uu____11765)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11801 -> failwith "Impossible"))
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
                 let uu____11844 = get_range env in
                 let uu____11845 =
                   let uu____11848 =
                     let uu____11849 =
                       let uu____11864 =
                         let uu____11867 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11867] in
                       (null_wp, uu____11864) in
                     FStar_Syntax_Syntax.Tm_app uu____11849 in
                   FStar_Syntax_Syntax.mk uu____11848 in
                 uu____11845 FStar_Pervasives_Native.None uu____11844 in
               let uu____11873 =
                 let uu____11874 =
                   let uu____11883 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11883] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11874;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11873)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___95_11892 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___95_11892.order);
              joins = (uu___95_11892.joins)
            } in
          let uu___96_11901 = env in
          {
            solver = (uu___96_11901.solver);
            range = (uu___96_11901.range);
            curmodule = (uu___96_11901.curmodule);
            gamma = (uu___96_11901.gamma);
            gamma_cache = (uu___96_11901.gamma_cache);
            modules = (uu___96_11901.modules);
            expected_typ = (uu___96_11901.expected_typ);
            sigtab = (uu___96_11901.sigtab);
            is_pattern = (uu___96_11901.is_pattern);
            instantiate_imp = (uu___96_11901.instantiate_imp);
            effects;
            generalize = (uu___96_11901.generalize);
            letrecs = (uu___96_11901.letrecs);
            top_level = (uu___96_11901.top_level);
            check_uvars = (uu___96_11901.check_uvars);
            use_eq = (uu___96_11901.use_eq);
            is_iface = (uu___96_11901.is_iface);
            admit = (uu___96_11901.admit);
            lax = (uu___96_11901.lax);
            lax_universes = (uu___96_11901.lax_universes);
            failhard = (uu___96_11901.failhard);
            nosynth = (uu___96_11901.nosynth);
            tc_term = (uu___96_11901.tc_term);
            type_of = (uu___96_11901.type_of);
            universe_of = (uu___96_11901.universe_of);
            use_bv_sorts = (uu___96_11901.use_bv_sorts);
            qname_and_index = (uu___96_11901.qname_and_index);
            proof_ns = (uu___96_11901.proof_ns);
            synth = (uu___96_11901.synth);
            is_native_tactic = (uu___96_11901.is_native_tactic);
            identifier_info = (uu___96_11901.identifier_info);
            tc_hooks = (uu___96_11901.tc_hooks);
            dsenv = (uu___96_11901.dsenv);
            dep_graph = (uu___96_11901.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____11921 = (e1.mlift).mlift_wp u r wp1 in
                (e2.mlift).mlift_wp u r uu____11921 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12035 = (e1.mlift).mlift_wp u t wp in
                                let uu____12036 = l1 u t wp e in
                                l2 u t uu____12035 uu____12036))
                | uu____12037 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12085 = inst_tscheme_with lift_t [u] in
            match uu____12085 with
            | (uu____12092,lift_t1) ->
                let uu____12094 =
                  let uu____12097 =
                    let uu____12098 =
                      let uu____12113 =
                        let uu____12116 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12117 =
                          let uu____12120 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12120] in
                        uu____12116 :: uu____12117 in
                      (lift_t1, uu____12113) in
                    FStar_Syntax_Syntax.Tm_app uu____12098 in
                  FStar_Syntax_Syntax.mk uu____12097 in
                uu____12094 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____12170 = inst_tscheme_with lift_t [u] in
            match uu____12170 with
            | (uu____12177,lift_t1) ->
                let uu____12179 =
                  let uu____12182 =
                    let uu____12183 =
                      let uu____12198 =
                        let uu____12201 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12202 =
                          let uu____12205 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12206 =
                            let uu____12209 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12209] in
                          uu____12205 :: uu____12206 in
                        uu____12201 :: uu____12202 in
                      (lift_t1, uu____12198) in
                    FStar_Syntax_Syntax.Tm_app uu____12183 in
                  FStar_Syntax_Syntax.mk uu____12182 in
                uu____12179 FStar_Pervasives_Native.None
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
              let uu____12251 =
                let uu____12252 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12252
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12251 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12256 =
              let uu____12257 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp in
              FStar_Syntax_Print.term_to_string uu____12257 in
            let uu____12258 =
              let uu____12259 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12281 = l1 FStar_Syntax_Syntax.U_zero arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12281) in
              FStar_Util.dflt "none" uu____12259 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12256
              uu____12258 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12307  ->
                    match uu____12307 with
                    | (e,uu____12315) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12334 =
            match uu____12334 with
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
              let uu____12372 =
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
                                    (let uu____12393 =
                                       let uu____12402 =
                                         find_edge order1 (i, k) in
                                       let uu____12405 =
                                         find_edge order1 (k, j) in
                                       (uu____12402, uu____12405) in
                                     match uu____12393 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12420 =
                                           compose_edges e1 e2 in
                                         [uu____12420]
                                     | uu____12421 -> []))))) in
              FStar_List.append order1 uu____12372 in
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
                   let uu____12451 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12453 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12453
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12451
                   then
                     let uu____12458 =
                       let uu____12463 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____12463) in
                     let uu____12464 = get_range env in
                     FStar_Errors.raise_error uu____12458 uu____12464
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
                                            let uu____12589 =
                                              let uu____12598 =
                                                find_edge order2 (i, k) in
                                              let uu____12601 =
                                                find_edge order2 (j, k) in
                                              (uu____12598, uu____12601) in
                                            match uu____12589 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12643,uu____12644)
                                                     ->
                                                     let uu____12651 =
                                                       let uu____12656 =
                                                         let uu____12657 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12657 in
                                                       let uu____12660 =
                                                         let uu____12661 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12661 in
                                                       (uu____12656,
                                                         uu____12660) in
                                                     (match uu____12651 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
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
                                            | uu____12696 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___97_12769 = env.effects in
              { decls = (uu___97_12769.decls); order = order2; joins } in
            let uu___98_12770 = env in
            {
              solver = (uu___98_12770.solver);
              range = (uu___98_12770.range);
              curmodule = (uu___98_12770.curmodule);
              gamma = (uu___98_12770.gamma);
              gamma_cache = (uu___98_12770.gamma_cache);
              modules = (uu___98_12770.modules);
              expected_typ = (uu___98_12770.expected_typ);
              sigtab = (uu___98_12770.sigtab);
              is_pattern = (uu___98_12770.is_pattern);
              instantiate_imp = (uu___98_12770.instantiate_imp);
              effects;
              generalize = (uu___98_12770.generalize);
              letrecs = (uu___98_12770.letrecs);
              top_level = (uu___98_12770.top_level);
              check_uvars = (uu___98_12770.check_uvars);
              use_eq = (uu___98_12770.use_eq);
              is_iface = (uu___98_12770.is_iface);
              admit = (uu___98_12770.admit);
              lax = (uu___98_12770.lax);
              lax_universes = (uu___98_12770.lax_universes);
              failhard = (uu___98_12770.failhard);
              nosynth = (uu___98_12770.nosynth);
              tc_term = (uu___98_12770.tc_term);
              type_of = (uu___98_12770.type_of);
              universe_of = (uu___98_12770.universe_of);
              use_bv_sorts = (uu___98_12770.use_bv_sorts);
              qname_and_index = (uu___98_12770.qname_and_index);
              proof_ns = (uu___98_12770.proof_ns);
              synth = (uu___98_12770.synth);
              is_native_tactic = (uu___98_12770.is_native_tactic);
              identifier_info = (uu___98_12770.identifier_info);
              tc_hooks = (uu___98_12770.tc_hooks);
              dsenv = (uu___98_12770.dsenv);
              dep_graph = (uu___98_12770.dep_graph)
            }))
      | uu____12771 -> env
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
        | uu____12795 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12803 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12803 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12820 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12820 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12838 =
                     let uu____12843 =
                       let uu____12844 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____12849 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1")) in
                       let uu____12856 =
                         let uu____12857 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____12857 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____12844 uu____12849 uu____12856 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____12843) in
                   FStar_Errors.raise_error uu____12838
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____12862 =
                     let uu____12871 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12871 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12888  ->
                        fun uu____12889  ->
                          match (uu____12888, uu____12889) with
                          | ((x,uu____12911),(t,uu____12913)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12862 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12932 =
                     let uu___99_12933 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___99_12933.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___99_12933.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___99_12933.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___99_12933.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12932
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
          let uu____12955 = effect_decl_opt env effect_name in
          match uu____12955 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12988 =
                only_reifiable &&
                  (let uu____12990 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____12990) in
              if uu____12988
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13006 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13025 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13054 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13054
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13055 = get_range env in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____13055 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13065 =
                       let uu____13068 = get_range env in
                       let uu____13069 =
                         let uu____13072 =
                           let uu____13073 =
                             let uu____13088 =
                               let uu____13091 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13091; wp] in
                             (repr, uu____13088) in
                           FStar_Syntax_Syntax.Tm_app uu____13073 in
                         FStar_Syntax_Syntax.mk uu____13072 in
                       uu____13069 FStar_Pervasives_Native.None uu____13068 in
                     FStar_Pervasives_Native.Some uu____13065)
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
          let uu____13137 =
            let uu____13142 =
              let uu____13143 = FStar_Ident.string_of_lid l in
              FStar_Util.format1 "Effect %s cannot be reified" uu____13143 in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____13142) in
          let uu____13144 = get_range env in
          FStar_Errors.raise_error uu____13137 uu____13144 in
        let uu____13145 = effect_repr_aux true env c u_c in
        match uu____13145 with
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
      | uu____13179 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13186 =
        let uu____13187 = FStar_Syntax_Subst.compress t in
        uu____13187.FStar_Syntax_Syntax.n in
      match uu____13186 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13190,c) ->
          is_reifiable_comp env c
      | uu____13208 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13230)::uu____13231 -> x :: rest
        | (Binding_sig_inst uu____13240)::uu____13241 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13256 = push1 x rest1 in local :: uu____13256 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___100_13260 = env in
       let uu____13261 = push1 s env.gamma in
       {
         solver = (uu___100_13260.solver);
         range = (uu___100_13260.range);
         curmodule = (uu___100_13260.curmodule);
         gamma = uu____13261;
         gamma_cache = (uu___100_13260.gamma_cache);
         modules = (uu___100_13260.modules);
         expected_typ = (uu___100_13260.expected_typ);
         sigtab = (uu___100_13260.sigtab);
         is_pattern = (uu___100_13260.is_pattern);
         instantiate_imp = (uu___100_13260.instantiate_imp);
         effects = (uu___100_13260.effects);
         generalize = (uu___100_13260.generalize);
         letrecs = (uu___100_13260.letrecs);
         top_level = (uu___100_13260.top_level);
         check_uvars = (uu___100_13260.check_uvars);
         use_eq = (uu___100_13260.use_eq);
         is_iface = (uu___100_13260.is_iface);
         admit = (uu___100_13260.admit);
         lax = (uu___100_13260.lax);
         lax_universes = (uu___100_13260.lax_universes);
         failhard = (uu___100_13260.failhard);
         nosynth = (uu___100_13260.nosynth);
         tc_term = (uu___100_13260.tc_term);
         type_of = (uu___100_13260.type_of);
         universe_of = (uu___100_13260.universe_of);
         use_bv_sorts = (uu___100_13260.use_bv_sorts);
         qname_and_index = (uu___100_13260.qname_and_index);
         proof_ns = (uu___100_13260.proof_ns);
         synth = (uu___100_13260.synth);
         is_native_tactic = (uu___100_13260.is_native_tactic);
         identifier_info = (uu___100_13260.identifier_info);
         tc_hooks = (uu___100_13260.tc_hooks);
         dsenv = (uu___100_13260.dsenv);
         dep_graph = (uu___100_13260.dep_graph)
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
      let uu___101_13291 = env in
      {
        solver = (uu___101_13291.solver);
        range = (uu___101_13291.range);
        curmodule = (uu___101_13291.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___101_13291.gamma_cache);
        modules = (uu___101_13291.modules);
        expected_typ = (uu___101_13291.expected_typ);
        sigtab = (uu___101_13291.sigtab);
        is_pattern = (uu___101_13291.is_pattern);
        instantiate_imp = (uu___101_13291.instantiate_imp);
        effects = (uu___101_13291.effects);
        generalize = (uu___101_13291.generalize);
        letrecs = (uu___101_13291.letrecs);
        top_level = (uu___101_13291.top_level);
        check_uvars = (uu___101_13291.check_uvars);
        use_eq = (uu___101_13291.use_eq);
        is_iface = (uu___101_13291.is_iface);
        admit = (uu___101_13291.admit);
        lax = (uu___101_13291.lax);
        lax_universes = (uu___101_13291.lax_universes);
        failhard = (uu___101_13291.failhard);
        nosynth = (uu___101_13291.nosynth);
        tc_term = (uu___101_13291.tc_term);
        type_of = (uu___101_13291.type_of);
        universe_of = (uu___101_13291.universe_of);
        use_bv_sorts = (uu___101_13291.use_bv_sorts);
        qname_and_index = (uu___101_13291.qname_and_index);
        proof_ns = (uu___101_13291.proof_ns);
        synth = (uu___101_13291.synth);
        is_native_tactic = (uu___101_13291.is_native_tactic);
        identifier_info = (uu___101_13291.identifier_info);
        tc_hooks = (uu___101_13291.tc_hooks);
        dsenv = (uu___101_13291.dsenv);
        dep_graph = (uu___101_13291.dep_graph)
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
            (let uu___102_13322 = env in
             {
               solver = (uu___102_13322.solver);
               range = (uu___102_13322.range);
               curmodule = (uu___102_13322.curmodule);
               gamma = rest;
               gamma_cache = (uu___102_13322.gamma_cache);
               modules = (uu___102_13322.modules);
               expected_typ = (uu___102_13322.expected_typ);
               sigtab = (uu___102_13322.sigtab);
               is_pattern = (uu___102_13322.is_pattern);
               instantiate_imp = (uu___102_13322.instantiate_imp);
               effects = (uu___102_13322.effects);
               generalize = (uu___102_13322.generalize);
               letrecs = (uu___102_13322.letrecs);
               top_level = (uu___102_13322.top_level);
               check_uvars = (uu___102_13322.check_uvars);
               use_eq = (uu___102_13322.use_eq);
               is_iface = (uu___102_13322.is_iface);
               admit = (uu___102_13322.admit);
               lax = (uu___102_13322.lax);
               lax_universes = (uu___102_13322.lax_universes);
               failhard = (uu___102_13322.failhard);
               nosynth = (uu___102_13322.nosynth);
               tc_term = (uu___102_13322.tc_term);
               type_of = (uu___102_13322.type_of);
               universe_of = (uu___102_13322.universe_of);
               use_bv_sorts = (uu___102_13322.use_bv_sorts);
               qname_and_index = (uu___102_13322.qname_and_index);
               proof_ns = (uu___102_13322.proof_ns);
               synth = (uu___102_13322.synth);
               is_native_tactic = (uu___102_13322.is_native_tactic);
               identifier_info = (uu___102_13322.identifier_info);
               tc_hooks = (uu___102_13322.tc_hooks);
               dsenv = (uu___102_13322.dsenv);
               dep_graph = (uu___102_13322.dep_graph)
             }))
    | uu____13323 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13345  ->
             match uu____13345 with | (x,uu____13351) -> push_bv env1 x) env
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
            let uu___103_13379 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___103_13379.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___103_13379.FStar_Syntax_Syntax.index);
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
      (let uu___104_13409 = env in
       {
         solver = (uu___104_13409.solver);
         range = (uu___104_13409.range);
         curmodule = (uu___104_13409.curmodule);
         gamma = [];
         gamma_cache = (uu___104_13409.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___104_13409.sigtab);
         is_pattern = (uu___104_13409.is_pattern);
         instantiate_imp = (uu___104_13409.instantiate_imp);
         effects = (uu___104_13409.effects);
         generalize = (uu___104_13409.generalize);
         letrecs = (uu___104_13409.letrecs);
         top_level = (uu___104_13409.top_level);
         check_uvars = (uu___104_13409.check_uvars);
         use_eq = (uu___104_13409.use_eq);
         is_iface = (uu___104_13409.is_iface);
         admit = (uu___104_13409.admit);
         lax = (uu___104_13409.lax);
         lax_universes = (uu___104_13409.lax_universes);
         failhard = (uu___104_13409.failhard);
         nosynth = (uu___104_13409.nosynth);
         tc_term = (uu___104_13409.tc_term);
         type_of = (uu___104_13409.type_of);
         universe_of = (uu___104_13409.universe_of);
         use_bv_sorts = (uu___104_13409.use_bv_sorts);
         qname_and_index = (uu___104_13409.qname_and_index);
         proof_ns = (uu___104_13409.proof_ns);
         synth = (uu___104_13409.synth);
         is_native_tactic = (uu___104_13409.is_native_tactic);
         identifier_info = (uu___104_13409.identifier_info);
         tc_hooks = (uu___104_13409.tc_hooks);
         dsenv = (uu___104_13409.dsenv);
         dep_graph = (uu___104_13409.dep_graph)
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
        let uu____13441 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13441 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13469 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13469)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___105_13482 = env in
      {
        solver = (uu___105_13482.solver);
        range = (uu___105_13482.range);
        curmodule = (uu___105_13482.curmodule);
        gamma = (uu___105_13482.gamma);
        gamma_cache = (uu___105_13482.gamma_cache);
        modules = (uu___105_13482.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___105_13482.sigtab);
        is_pattern = (uu___105_13482.is_pattern);
        instantiate_imp = (uu___105_13482.instantiate_imp);
        effects = (uu___105_13482.effects);
        generalize = (uu___105_13482.generalize);
        letrecs = (uu___105_13482.letrecs);
        top_level = (uu___105_13482.top_level);
        check_uvars = (uu___105_13482.check_uvars);
        use_eq = false;
        is_iface = (uu___105_13482.is_iface);
        admit = (uu___105_13482.admit);
        lax = (uu___105_13482.lax);
        lax_universes = (uu___105_13482.lax_universes);
        failhard = (uu___105_13482.failhard);
        nosynth = (uu___105_13482.nosynth);
        tc_term = (uu___105_13482.tc_term);
        type_of = (uu___105_13482.type_of);
        universe_of = (uu___105_13482.universe_of);
        use_bv_sorts = (uu___105_13482.use_bv_sorts);
        qname_and_index = (uu___105_13482.qname_and_index);
        proof_ns = (uu___105_13482.proof_ns);
        synth = (uu___105_13482.synth);
        is_native_tactic = (uu___105_13482.is_native_tactic);
        identifier_info = (uu___105_13482.identifier_info);
        tc_hooks = (uu___105_13482.tc_hooks);
        dsenv = (uu___105_13482.dsenv);
        dep_graph = (uu___105_13482.dep_graph)
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
    let uu____13506 = expected_typ env_ in
    ((let uu___106_13512 = env_ in
      {
        solver = (uu___106_13512.solver);
        range = (uu___106_13512.range);
        curmodule = (uu___106_13512.curmodule);
        gamma = (uu___106_13512.gamma);
        gamma_cache = (uu___106_13512.gamma_cache);
        modules = (uu___106_13512.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___106_13512.sigtab);
        is_pattern = (uu___106_13512.is_pattern);
        instantiate_imp = (uu___106_13512.instantiate_imp);
        effects = (uu___106_13512.effects);
        generalize = (uu___106_13512.generalize);
        letrecs = (uu___106_13512.letrecs);
        top_level = (uu___106_13512.top_level);
        check_uvars = (uu___106_13512.check_uvars);
        use_eq = false;
        is_iface = (uu___106_13512.is_iface);
        admit = (uu___106_13512.admit);
        lax = (uu___106_13512.lax);
        lax_universes = (uu___106_13512.lax_universes);
        failhard = (uu___106_13512.failhard);
        nosynth = (uu___106_13512.nosynth);
        tc_term = (uu___106_13512.tc_term);
        type_of = (uu___106_13512.type_of);
        universe_of = (uu___106_13512.universe_of);
        use_bv_sorts = (uu___106_13512.use_bv_sorts);
        qname_and_index = (uu___106_13512.qname_and_index);
        proof_ns = (uu___106_13512.proof_ns);
        synth = (uu___106_13512.synth);
        is_native_tactic = (uu___106_13512.is_native_tactic);
        identifier_info = (uu___106_13512.identifier_info);
        tc_hooks = (uu___106_13512.tc_hooks);
        dsenv = (uu___106_13512.dsenv);
        dep_graph = (uu___106_13512.dep_graph)
      }), uu____13506)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13525 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___80_13535  ->
                    match uu___80_13535 with
                    | Binding_sig (uu____13538,se) -> [se]
                    | uu____13544 -> [])) in
          FStar_All.pipe_right uu____13525 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___107_13551 = env in
       {
         solver = (uu___107_13551.solver);
         range = (uu___107_13551.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___107_13551.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___107_13551.expected_typ);
         sigtab = (uu___107_13551.sigtab);
         is_pattern = (uu___107_13551.is_pattern);
         instantiate_imp = (uu___107_13551.instantiate_imp);
         effects = (uu___107_13551.effects);
         generalize = (uu___107_13551.generalize);
         letrecs = (uu___107_13551.letrecs);
         top_level = (uu___107_13551.top_level);
         check_uvars = (uu___107_13551.check_uvars);
         use_eq = (uu___107_13551.use_eq);
         is_iface = (uu___107_13551.is_iface);
         admit = (uu___107_13551.admit);
         lax = (uu___107_13551.lax);
         lax_universes = (uu___107_13551.lax_universes);
         failhard = (uu___107_13551.failhard);
         nosynth = (uu___107_13551.nosynth);
         tc_term = (uu___107_13551.tc_term);
         type_of = (uu___107_13551.type_of);
         universe_of = (uu___107_13551.universe_of);
         use_bv_sorts = (uu___107_13551.use_bv_sorts);
         qname_and_index = (uu___107_13551.qname_and_index);
         proof_ns = (uu___107_13551.proof_ns);
         synth = (uu___107_13551.synth);
         is_native_tactic = (uu___107_13551.is_native_tactic);
         identifier_info = (uu___107_13551.identifier_info);
         tc_hooks = (uu___107_13551.tc_hooks);
         dsenv = (uu___107_13551.dsenv);
         dep_graph = (uu___107_13551.dep_graph)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13632)::tl1 -> aux out tl1
      | (Binding_lid (uu____13636,(uu____13637,t)))::tl1 ->
          let uu____13652 =
            let uu____13659 = FStar_Syntax_Free.uvars t in
            ext out uu____13659 in
          aux uu____13652 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13666;
            FStar_Syntax_Syntax.index = uu____13667;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13674 =
            let uu____13681 = FStar_Syntax_Free.uvars t in
            ext out uu____13681 in
          aux uu____13674 tl1
      | (Binding_sig uu____13688)::uu____13689 -> out
      | (Binding_sig_inst uu____13698)::uu____13699 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13754)::tl1 -> aux out tl1
      | (Binding_univ uu____13766)::tl1 -> aux out tl1
      | (Binding_lid (uu____13770,(uu____13771,t)))::tl1 ->
          let uu____13786 =
            let uu____13789 = FStar_Syntax_Free.univs t in
            ext out uu____13789 in
          aux uu____13786 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13792;
            FStar_Syntax_Syntax.index = uu____13793;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13800 =
            let uu____13803 = FStar_Syntax_Free.univs t in
            ext out uu____13803 in
          aux uu____13800 tl1
      | (Binding_sig uu____13806)::uu____13807 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13860)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13876 = FStar_Util.fifo_set_add uname out in
          aux uu____13876 tl1
      | (Binding_lid (uu____13879,(uu____13880,t)))::tl1 ->
          let uu____13895 =
            let uu____13898 = FStar_Syntax_Free.univnames t in
            ext out uu____13898 in
          aux uu____13895 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13901;
            FStar_Syntax_Syntax.index = uu____13902;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13909 =
            let uu____13912 = FStar_Syntax_Free.univnames t in
            ext out uu____13912 in
          aux uu____13909 tl1
      | (Binding_sig uu____13915)::uu____13916 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___81_13940  ->
            match uu___81_13940 with
            | Binding_var x -> [x]
            | Binding_lid uu____13944 -> []
            | Binding_sig uu____13949 -> []
            | Binding_univ uu____13956 -> []
            | Binding_sig_inst uu____13957 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____13973 =
      let uu____13976 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____13976
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____13973 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____13998 =
      let uu____13999 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___82_14009  ->
                match uu___82_14009 with
                | Binding_var x ->
                    let uu____14011 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14011
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14014) ->
                    let uu____14015 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14015
                | Binding_sig (ls,uu____14017) ->
                    let uu____14022 =
                      let uu____14023 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14023
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14022
                | Binding_sig_inst (ls,uu____14033,uu____14034) ->
                    let uu____14039 =
                      let uu____14040 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14040
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14039)) in
      FStar_All.pipe_right uu____13999 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____13998 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14057 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14057
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14085  ->
                 fun uu____14086  ->
                   match (uu____14085, uu____14086) with
                   | ((b1,uu____14104),(b2,uu____14106)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___83_14148  ->
    match uu___83_14148 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14149 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___84_14167  ->
             match uu___84_14167 with
             | Binding_sig (lids,uu____14173) -> FStar_List.append lids keys
             | uu____14178 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14184  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14218) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14237,uu____14238) -> false in
      let uu____14247 =
        FStar_List.tryFind
          (fun uu____14265  ->
             match uu____14265 with | (p,uu____14273) -> list_prefix p path)
          env.proof_ns in
      match uu____14247 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14284,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14302 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14302
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___108_14314 = e in
        {
          solver = (uu___108_14314.solver);
          range = (uu___108_14314.range);
          curmodule = (uu___108_14314.curmodule);
          gamma = (uu___108_14314.gamma);
          gamma_cache = (uu___108_14314.gamma_cache);
          modules = (uu___108_14314.modules);
          expected_typ = (uu___108_14314.expected_typ);
          sigtab = (uu___108_14314.sigtab);
          is_pattern = (uu___108_14314.is_pattern);
          instantiate_imp = (uu___108_14314.instantiate_imp);
          effects = (uu___108_14314.effects);
          generalize = (uu___108_14314.generalize);
          letrecs = (uu___108_14314.letrecs);
          top_level = (uu___108_14314.top_level);
          check_uvars = (uu___108_14314.check_uvars);
          use_eq = (uu___108_14314.use_eq);
          is_iface = (uu___108_14314.is_iface);
          admit = (uu___108_14314.admit);
          lax = (uu___108_14314.lax);
          lax_universes = (uu___108_14314.lax_universes);
          failhard = (uu___108_14314.failhard);
          nosynth = (uu___108_14314.nosynth);
          tc_term = (uu___108_14314.tc_term);
          type_of = (uu___108_14314.type_of);
          universe_of = (uu___108_14314.universe_of);
          use_bv_sorts = (uu___108_14314.use_bv_sorts);
          qname_and_index = (uu___108_14314.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___108_14314.synth);
          is_native_tactic = (uu___108_14314.is_native_tactic);
          identifier_info = (uu___108_14314.identifier_info);
          tc_hooks = (uu___108_14314.tc_hooks);
          dsenv = (uu___108_14314.dsenv);
          dep_graph = (uu___108_14314.dep_graph)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___109_14340 = e in
      {
        solver = (uu___109_14340.solver);
        range = (uu___109_14340.range);
        curmodule = (uu___109_14340.curmodule);
        gamma = (uu___109_14340.gamma);
        gamma_cache = (uu___109_14340.gamma_cache);
        modules = (uu___109_14340.modules);
        expected_typ = (uu___109_14340.expected_typ);
        sigtab = (uu___109_14340.sigtab);
        is_pattern = (uu___109_14340.is_pattern);
        instantiate_imp = (uu___109_14340.instantiate_imp);
        effects = (uu___109_14340.effects);
        generalize = (uu___109_14340.generalize);
        letrecs = (uu___109_14340.letrecs);
        top_level = (uu___109_14340.top_level);
        check_uvars = (uu___109_14340.check_uvars);
        use_eq = (uu___109_14340.use_eq);
        is_iface = (uu___109_14340.is_iface);
        admit = (uu___109_14340.admit);
        lax = (uu___109_14340.lax);
        lax_universes = (uu___109_14340.lax_universes);
        failhard = (uu___109_14340.failhard);
        nosynth = (uu___109_14340.nosynth);
        tc_term = (uu___109_14340.tc_term);
        type_of = (uu___109_14340.type_of);
        universe_of = (uu___109_14340.universe_of);
        use_bv_sorts = (uu___109_14340.use_bv_sorts);
        qname_and_index = (uu___109_14340.qname_and_index);
        proof_ns = ns;
        synth = (uu___109_14340.synth);
        is_native_tactic = (uu___109_14340.is_native_tactic);
        identifier_info = (uu___109_14340.identifier_info);
        tc_hooks = (uu___109_14340.tc_hooks);
        dsenv = (uu___109_14340.dsenv);
        dep_graph = (uu___109_14340.dep_graph)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14351 = FStar_Syntax_Free.names t in
      let uu____14354 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14351 uu____14354
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14371 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14371
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14377 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14377
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14392 =
      match uu____14392 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14408 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14408) in
    let uu____14410 =
      let uu____14413 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14413 FStar_List.rev in
    FStar_All.pipe_right uu____14410 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14430  -> ());
    push = (fun uu____14432  -> ());
    pop = (fun uu____14434  -> ());
    encode_modul = (fun uu____14437  -> fun uu____14438  -> ());
    encode_sig = (fun uu____14441  -> fun uu____14442  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14448 =
             let uu____14455 = FStar_Options.peek () in (e, g, uu____14455) in
           [uu____14448]);
    solve = (fun uu____14471  -> fun uu____14472  -> fun uu____14473  -> ());
    finish = (fun uu____14479  -> ());
    refresh = (fun uu____14481  -> ())
  }