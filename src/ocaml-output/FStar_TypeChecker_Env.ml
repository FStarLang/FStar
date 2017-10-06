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
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4781  -> fun uu____4782  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___126_4795 = env in
      {
        solver = (uu___126_4795.solver);
        range = (uu___126_4795.range);
        curmodule = (uu___126_4795.curmodule);
        gamma = (uu___126_4795.gamma);
        gamma_cache = (uu___126_4795.gamma_cache);
        modules = (uu___126_4795.modules);
        expected_typ = (uu___126_4795.expected_typ);
        sigtab = (uu___126_4795.sigtab);
        is_pattern = (uu___126_4795.is_pattern);
        instantiate_imp = (uu___126_4795.instantiate_imp);
        effects = (uu___126_4795.effects);
        generalize = (uu___126_4795.generalize);
        letrecs = (uu___126_4795.letrecs);
        top_level = (uu___126_4795.top_level);
        check_uvars = (uu___126_4795.check_uvars);
        use_eq = (uu___126_4795.use_eq);
        is_iface = (uu___126_4795.is_iface);
        admit = (uu___126_4795.admit);
        lax = (uu___126_4795.lax);
        lax_universes = (uu___126_4795.lax_universes);
        failhard = (uu___126_4795.failhard);
        nosynth = (uu___126_4795.nosynth);
        tc_term = (uu___126_4795.tc_term);
        type_of = (uu___126_4795.type_of);
        universe_of = (uu___126_4795.universe_of);
        use_bv_sorts = (uu___126_4795.use_bv_sorts);
        qname_and_index = (uu___126_4795.qname_and_index);
        proof_ns = (uu___126_4795.proof_ns);
        synth = (uu___126_4795.synth);
        is_native_tactic = (uu___126_4795.is_native_tactic);
        identifier_info = (uu___126_4795.identifier_info);
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
      | (NoDelta ,uu____4810) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4811,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4812,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4813 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4822 . Prims.unit -> 'Auu____4822 FStar_Util.smap =
  fun uu____4828  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4833 . Prims.unit -> 'Auu____4833 FStar_Util.smap =
  fun uu____4839  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____4914 = new_gamma_cache () in
            let uu____4917 = new_sigtab () in
            let uu____4920 =
              let uu____4921 = FStar_Options.using_facts_from () in
              match uu____4921 with
              | FStar_Pervasives_Native.Some ns ->
                  let uu____4931 =
                    let uu____4940 =
                      FStar_List.map
                        (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                    FStar_List.append uu____4940 [([], false)] in
                  [uu____4931]
              | FStar_Pervasives_Native.None  -> [[]] in
            let uu____5013 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____4914;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____4917;
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
              proof_ns = uu____4920;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5047  -> false);
              identifier_info = uu____5013;
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
  fun uu____5118  ->
    let uu____5119 = FStar_ST.op_Bang query_indices in
    match uu____5119 with
    | [] -> failwith "Empty query indices!"
    | uu____5196 ->
        let uu____5205 =
          let uu____5214 =
            let uu____5221 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5221 in
          let uu____5298 = FStar_ST.op_Bang query_indices in uu____5214 ::
            uu____5298 in
        FStar_ST.op_Colon_Equals query_indices uu____5205
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5440  ->
    let uu____5441 = FStar_ST.op_Bang query_indices in
    match uu____5441 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5609  ->
    match uu____5609 with
    | (l,n1) ->
        let uu____5616 = FStar_ST.op_Bang query_indices in
        (match uu____5616 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5781 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5799  ->
    let uu____5800 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5800
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5895 =
       let uu____5898 = FStar_ST.op_Bang stack in env :: uu____5898 in
     FStar_ST.op_Colon_Equals stack uu____5895);
    (let uu___127_6001 = env in
     let uu____6002 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6005 = FStar_Util.smap_copy (sigtab env) in
     let uu____6008 =
       let uu____6011 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6011 in
     {
       solver = (uu___127_6001.solver);
       range = (uu___127_6001.range);
       curmodule = (uu___127_6001.curmodule);
       gamma = (uu___127_6001.gamma);
       gamma_cache = uu____6002;
       modules = (uu___127_6001.modules);
       expected_typ = (uu___127_6001.expected_typ);
       sigtab = uu____6005;
       is_pattern = (uu___127_6001.is_pattern);
       instantiate_imp = (uu___127_6001.instantiate_imp);
       effects = (uu___127_6001.effects);
       generalize = (uu___127_6001.generalize);
       letrecs = (uu___127_6001.letrecs);
       top_level = (uu___127_6001.top_level);
       check_uvars = (uu___127_6001.check_uvars);
       use_eq = (uu___127_6001.use_eq);
       is_iface = (uu___127_6001.is_iface);
       admit = (uu___127_6001.admit);
       lax = (uu___127_6001.lax);
       lax_universes = (uu___127_6001.lax_universes);
       failhard = (uu___127_6001.failhard);
       nosynth = (uu___127_6001.nosynth);
       tc_term = (uu___127_6001.tc_term);
       type_of = (uu___127_6001.type_of);
       universe_of = (uu___127_6001.universe_of);
       use_bv_sorts = (uu___127_6001.use_bv_sorts);
       qname_and_index = (uu___127_6001.qname_and_index);
       proof_ns = (uu___127_6001.proof_ns);
       synth = (uu___127_6001.synth);
       is_native_tactic = (uu___127_6001.is_native_tactic);
       identifier_info = uu____6008;
       tc_hooks = (uu___127_6001.tc_hooks)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6075  ->
    let uu____6076 = FStar_ST.op_Bang stack in
    match uu____6076 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6184 -> failwith "Impossible: Too many pops"
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
        let uu____6232 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6258  ->
                  match uu____6258 with
                  | (m,uu____6264) -> FStar_Ident.lid_equals l m)) in
        (match uu____6232 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___128_6271 = env in
               {
                 solver = (uu___128_6271.solver);
                 range = (uu___128_6271.range);
                 curmodule = (uu___128_6271.curmodule);
                 gamma = (uu___128_6271.gamma);
                 gamma_cache = (uu___128_6271.gamma_cache);
                 modules = (uu___128_6271.modules);
                 expected_typ = (uu___128_6271.expected_typ);
                 sigtab = (uu___128_6271.sigtab);
                 is_pattern = (uu___128_6271.is_pattern);
                 instantiate_imp = (uu___128_6271.instantiate_imp);
                 effects = (uu___128_6271.effects);
                 generalize = (uu___128_6271.generalize);
                 letrecs = (uu___128_6271.letrecs);
                 top_level = (uu___128_6271.top_level);
                 check_uvars = (uu___128_6271.check_uvars);
                 use_eq = (uu___128_6271.use_eq);
                 is_iface = (uu___128_6271.is_iface);
                 admit = (uu___128_6271.admit);
                 lax = (uu___128_6271.lax);
                 lax_universes = (uu___128_6271.lax_universes);
                 failhard = (uu___128_6271.failhard);
                 nosynth = (uu___128_6271.nosynth);
                 tc_term = (uu___128_6271.tc_term);
                 type_of = (uu___128_6271.type_of);
                 universe_of = (uu___128_6271.universe_of);
                 use_bv_sorts = (uu___128_6271.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___128_6271.proof_ns);
                 synth = (uu___128_6271.synth);
                 is_native_tactic = (uu___128_6271.is_native_tactic);
                 identifier_info = (uu___128_6271.identifier_info);
                 tc_hooks = (uu___128_6271.tc_hooks)
               }))
         | FStar_Pervasives_Native.Some (uu____6276,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___129_6284 = env in
               {
                 solver = (uu___129_6284.solver);
                 range = (uu___129_6284.range);
                 curmodule = (uu___129_6284.curmodule);
                 gamma = (uu___129_6284.gamma);
                 gamma_cache = (uu___129_6284.gamma_cache);
                 modules = (uu___129_6284.modules);
                 expected_typ = (uu___129_6284.expected_typ);
                 sigtab = (uu___129_6284.sigtab);
                 is_pattern = (uu___129_6284.is_pattern);
                 instantiate_imp = (uu___129_6284.instantiate_imp);
                 effects = (uu___129_6284.effects);
                 generalize = (uu___129_6284.generalize);
                 letrecs = (uu___129_6284.letrecs);
                 top_level = (uu___129_6284.top_level);
                 check_uvars = (uu___129_6284.check_uvars);
                 use_eq = (uu___129_6284.use_eq);
                 is_iface = (uu___129_6284.is_iface);
                 admit = (uu___129_6284.admit);
                 lax = (uu___129_6284.lax);
                 lax_universes = (uu___129_6284.lax_universes);
                 failhard = (uu___129_6284.failhard);
                 nosynth = (uu___129_6284.nosynth);
                 tc_term = (uu___129_6284.tc_term);
                 type_of = (uu___129_6284.type_of);
                 universe_of = (uu___129_6284.universe_of);
                 use_bv_sorts = (uu___129_6284.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___129_6284.proof_ns);
                 synth = (uu___129_6284.synth);
                 is_native_tactic = (uu___129_6284.is_native_tactic);
                 identifier_info = (uu___129_6284.identifier_info);
                 tc_hooks = (uu___129_6284.tc_hooks)
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
        (let uu___130_6306 = e in
         {
           solver = (uu___130_6306.solver);
           range = r;
           curmodule = (uu___130_6306.curmodule);
           gamma = (uu___130_6306.gamma);
           gamma_cache = (uu___130_6306.gamma_cache);
           modules = (uu___130_6306.modules);
           expected_typ = (uu___130_6306.expected_typ);
           sigtab = (uu___130_6306.sigtab);
           is_pattern = (uu___130_6306.is_pattern);
           instantiate_imp = (uu___130_6306.instantiate_imp);
           effects = (uu___130_6306.effects);
           generalize = (uu___130_6306.generalize);
           letrecs = (uu___130_6306.letrecs);
           top_level = (uu___130_6306.top_level);
           check_uvars = (uu___130_6306.check_uvars);
           use_eq = (uu___130_6306.use_eq);
           is_iface = (uu___130_6306.is_iface);
           admit = (uu___130_6306.admit);
           lax = (uu___130_6306.lax);
           lax_universes = (uu___130_6306.lax_universes);
           failhard = (uu___130_6306.failhard);
           nosynth = (uu___130_6306.nosynth);
           tc_term = (uu___130_6306.tc_term);
           type_of = (uu___130_6306.type_of);
           universe_of = (uu___130_6306.universe_of);
           use_bv_sorts = (uu___130_6306.use_bv_sorts);
           qname_and_index = (uu___130_6306.qname_and_index);
           proof_ns = (uu___130_6306.proof_ns);
           synth = (uu___130_6306.synth);
           is_native_tactic = (uu___130_6306.is_native_tactic);
           identifier_info = (uu___130_6306.identifier_info);
           tc_hooks = (uu___130_6306.tc_hooks)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6319 =
        let uu____6320 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6320 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6319
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6425 =
          let uu____6426 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6426 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6425
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6531 =
          let uu____6532 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6532 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6531
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6638 =
        let uu____6639 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6639 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6638
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___131_6750 = env in
      {
        solver = (uu___131_6750.solver);
        range = (uu___131_6750.range);
        curmodule = lid;
        gamma = (uu___131_6750.gamma);
        gamma_cache = (uu___131_6750.gamma_cache);
        modules = (uu___131_6750.modules);
        expected_typ = (uu___131_6750.expected_typ);
        sigtab = (uu___131_6750.sigtab);
        is_pattern = (uu___131_6750.is_pattern);
        instantiate_imp = (uu___131_6750.instantiate_imp);
        effects = (uu___131_6750.effects);
        generalize = (uu___131_6750.generalize);
        letrecs = (uu___131_6750.letrecs);
        top_level = (uu___131_6750.top_level);
        check_uvars = (uu___131_6750.check_uvars);
        use_eq = (uu___131_6750.use_eq);
        is_iface = (uu___131_6750.is_iface);
        admit = (uu___131_6750.admit);
        lax = (uu___131_6750.lax);
        lax_universes = (uu___131_6750.lax_universes);
        failhard = (uu___131_6750.failhard);
        nosynth = (uu___131_6750.nosynth);
        tc_term = (uu___131_6750.tc_term);
        type_of = (uu___131_6750.type_of);
        universe_of = (uu___131_6750.universe_of);
        use_bv_sorts = (uu___131_6750.use_bv_sorts);
        qname_and_index = (uu___131_6750.qname_and_index);
        proof_ns = (uu___131_6750.proof_ns);
        synth = (uu___131_6750.synth);
        is_native_tactic = (uu___131_6750.is_native_tactic);
        identifier_info = (uu___131_6750.identifier_info);
        tc_hooks = (uu___131_6750.tc_hooks)
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
    let uu____6781 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6781
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6785  ->
    let uu____6786 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6786
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
      | ((formals,t),uu____6826) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6850 = FStar_Syntax_Subst.subst vs t in (us, uu____6850)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___113_6864  ->
    match uu___113_6864 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6888  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6903 = inst_tscheme t in
      match uu____6903 with
      | (us,t1) ->
          let uu____6914 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6914)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6930  ->
          match uu____6930 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6945 =
                         let uu____6946 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6947 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6948 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6949 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6946 uu____6947 uu____6948 uu____6949 in
                       failwith uu____6945)
                    else ();
                    (let uu____6951 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6951))
               | uu____6958 ->
                   let uu____6959 =
                     let uu____6960 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6960 in
                   failwith uu____6959)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6965 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6970 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6975 -> false
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
             | ([],uu____7011) -> Maybe
             | (uu____7018,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7037 -> No in
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
          let uu____7144 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7144 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___114_7189  ->
                   match uu___114_7189 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7232 =
                           let uu____7251 =
                             let uu____7266 = inst_tscheme t in
                             FStar_Util.Inl uu____7266 in
                           (uu____7251, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7232
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7332,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7334);
                                     FStar_Syntax_Syntax.sigrng = uu____7335;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7336;
                                     FStar_Syntax_Syntax.sigmeta = uu____7337;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7338;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7358 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7358
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7404 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7411 -> cache t in
                       let uu____7412 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7412 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7487 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7487 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7573 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7653 = find_in_sigtab env lid in
         match uu____7653 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7752) ->
          add_sigelts env ses
      | uu____7761 ->
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
            | uu____7775 -> ()))
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
        (fun uu___115_7804  ->
           match uu___115_7804 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7822 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7857,lb::[]),uu____7859) ->
          let uu____7872 =
            let uu____7881 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7890 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7881, uu____7890) in
          FStar_Pervasives_Native.Some uu____7872
      | FStar_Syntax_Syntax.Sig_let ((uu____7903,lbs),uu____7905) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7941 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7953 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7953
                   then
                     let uu____7964 =
                       let uu____7973 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7982 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7973, uu____7982) in
                     FStar_Pervasives_Native.Some uu____7964
                   else FStar_Pervasives_Native.None)
      | uu____8004 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8038 =
          let uu____8047 =
            let uu____8052 =
              let uu____8053 =
                let uu____8056 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8056 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8053) in
            inst_tscheme uu____8052 in
          (uu____8047, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8038
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8076,uu____8077) ->
        let uu____8082 =
          let uu____8091 =
            let uu____8096 =
              let uu____8097 =
                let uu____8100 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8100 in
              (us, uu____8097) in
            inst_tscheme uu____8096 in
          (uu____8091, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8082
    | uu____8117 -> FStar_Pervasives_Native.None
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
      let mapper uu____8177 =
        match uu____8177 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8273,uvs,t,uu____8276,uu____8277,uu____8278);
                    FStar_Syntax_Syntax.sigrng = uu____8279;
                    FStar_Syntax_Syntax.sigquals = uu____8280;
                    FStar_Syntax_Syntax.sigmeta = uu____8281;
                    FStar_Syntax_Syntax.sigattrs = uu____8282;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8303 =
                   let uu____8312 = inst_tscheme (uvs, t) in
                   (uu____8312, rng) in
                 FStar_Pervasives_Native.Some uu____8303
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8332;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8334;
                    FStar_Syntax_Syntax.sigattrs = uu____8335;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8352 =
                   let uu____8353 = in_cur_mod env l in uu____8353 = Yes in
                 if uu____8352
                 then
                   let uu____8364 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8364
                    then
                      let uu____8377 =
                        let uu____8386 = inst_tscheme (uvs, t) in
                        (uu____8386, rng) in
                      FStar_Pervasives_Native.Some uu____8377
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8413 =
                      let uu____8422 = inst_tscheme (uvs, t) in
                      (uu____8422, rng) in
                    FStar_Pervasives_Native.Some uu____8413)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8443,uu____8444);
                    FStar_Syntax_Syntax.sigrng = uu____8445;
                    FStar_Syntax_Syntax.sigquals = uu____8446;
                    FStar_Syntax_Syntax.sigmeta = uu____8447;
                    FStar_Syntax_Syntax.sigattrs = uu____8448;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8487 =
                        let uu____8496 = inst_tscheme (uvs, k) in
                        (uu____8496, rng) in
                      FStar_Pervasives_Native.Some uu____8487
                  | uu____8513 ->
                      let uu____8514 =
                        let uu____8523 =
                          let uu____8528 =
                            let uu____8529 =
                              let uu____8532 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8532 in
                            (uvs, uu____8529) in
                          inst_tscheme uu____8528 in
                        (uu____8523, rng) in
                      FStar_Pervasives_Native.Some uu____8514)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8553,uu____8554);
                    FStar_Syntax_Syntax.sigrng = uu____8555;
                    FStar_Syntax_Syntax.sigquals = uu____8556;
                    FStar_Syntax_Syntax.sigmeta = uu____8557;
                    FStar_Syntax_Syntax.sigattrs = uu____8558;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8598 =
                        let uu____8607 = inst_tscheme_with (uvs, k) us in
                        (uu____8607, rng) in
                      FStar_Pervasives_Native.Some uu____8598
                  | uu____8624 ->
                      let uu____8625 =
                        let uu____8634 =
                          let uu____8639 =
                            let uu____8640 =
                              let uu____8643 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8643 in
                            (uvs, uu____8640) in
                          inst_tscheme_with uu____8639 us in
                        (uu____8634, rng) in
                      FStar_Pervasives_Native.Some uu____8625)
             | FStar_Util.Inr se ->
                 let uu____8677 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8698;
                        FStar_Syntax_Syntax.sigrng = uu____8699;
                        FStar_Syntax_Syntax.sigquals = uu____8700;
                        FStar_Syntax_Syntax.sigmeta = uu____8701;
                        FStar_Syntax_Syntax.sigattrs = uu____8702;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8717 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8677
                   (FStar_Util.map_option
                      (fun uu____8765  ->
                         match uu____8765 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8796 =
        let uu____8807 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8807 mapper in
      match uu____8796 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___132_8900 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___132_8900.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___132_8900.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8927 = lookup_qname env l in
      match uu____8927 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8966 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9016 = try_lookup_bv env bv in
      match uu____9016 with
      | FStar_Pervasives_Native.None  ->
          let uu____9031 =
            let uu____9032 =
              let uu____9037 = variable_not_found bv in (uu____9037, bvr) in
            FStar_Errors.Error uu____9032 in
          FStar_Exn.raise uu____9031
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9048 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9049 = FStar_Range.set_use_range r bvr in
          (uu____9048, uu____9049)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9068 = try_lookup_lid_aux env l in
      match uu____9068 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____9134 =
            let uu____9143 =
              let uu____9148 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____9148) in
            (uu____9143, r1) in
          FStar_Pervasives_Native.Some uu____9134
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9177 = try_lookup_lid env l in
      match uu____9177 with
      | FStar_Pervasives_Native.None  ->
          let uu____9204 =
            let uu____9205 =
              let uu____9210 = name_not_found l in
              (uu____9210, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9205 in
          FStar_Exn.raise uu____9204
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___116_9248  ->
              match uu___116_9248 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9250 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9267 = lookup_qname env lid in
      match uu____9267 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9296,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9299;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9301;
              FStar_Syntax_Syntax.sigattrs = uu____9302;_},FStar_Pervasives_Native.None
            ),uu____9303)
          ->
          let uu____9352 =
            let uu____9363 =
              let uu____9368 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9368) in
            (uu____9363, q) in
          FStar_Pervasives_Native.Some uu____9352
      | uu____9385 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9424 = lookup_qname env lid in
      match uu____9424 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9449,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9452;
              FStar_Syntax_Syntax.sigquals = uu____9453;
              FStar_Syntax_Syntax.sigmeta = uu____9454;
              FStar_Syntax_Syntax.sigattrs = uu____9455;_},FStar_Pervasives_Native.None
            ),uu____9456)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9505 ->
          let uu____9526 =
            let uu____9527 =
              let uu____9532 = name_not_found lid in
              (uu____9532, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9527 in
          FStar_Exn.raise uu____9526
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9549 = lookup_qname env lid in
      match uu____9549 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9574,uvs,t,uu____9577,uu____9578,uu____9579);
              FStar_Syntax_Syntax.sigrng = uu____9580;
              FStar_Syntax_Syntax.sigquals = uu____9581;
              FStar_Syntax_Syntax.sigmeta = uu____9582;
              FStar_Syntax_Syntax.sigattrs = uu____9583;_},FStar_Pervasives_Native.None
            ),uu____9584)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9637 ->
          let uu____9658 =
            let uu____9659 =
              let uu____9664 = name_not_found lid in
              (uu____9664, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9659 in
          FStar_Exn.raise uu____9658
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9683 = lookup_qname env lid in
      match uu____9683 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9710,uu____9711,uu____9712,uu____9713,uu____9714,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9716;
              FStar_Syntax_Syntax.sigquals = uu____9717;
              FStar_Syntax_Syntax.sigmeta = uu____9718;
              FStar_Syntax_Syntax.sigattrs = uu____9719;_},uu____9720),uu____9721)
          -> (true, dcs)
      | uu____9782 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9813 = lookup_qname env lid in
      match uu____9813 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9834,uu____9835,uu____9836,l,uu____9838,uu____9839);
              FStar_Syntax_Syntax.sigrng = uu____9840;
              FStar_Syntax_Syntax.sigquals = uu____9841;
              FStar_Syntax_Syntax.sigmeta = uu____9842;
              FStar_Syntax_Syntax.sigattrs = uu____9843;_},uu____9844),uu____9845)
          -> l
      | uu____9900 ->
          let uu____9921 =
            let uu____9922 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9922 in
          failwith uu____9921
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
        let uu____9959 = lookup_qname env lid in
        match uu____9959 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9987) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10038,lbs),uu____10040)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10068 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10068
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10100 -> FStar_Pervasives_Native.None)
        | uu____10105 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10142 = lookup_qname env ftv in
      match uu____10142 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10166) ->
          let uu____10211 = effect_signature se in
          (match uu____10211 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10232,t),r) ->
               let uu____10247 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10247)
      | uu____10248 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10277 = try_lookup_effect_lid env ftv in
      match uu____10277 with
      | FStar_Pervasives_Native.None  ->
          let uu____10280 =
            let uu____10281 =
              let uu____10286 = name_not_found ftv in
              (uu____10286, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10281 in
          FStar_Exn.raise uu____10280
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
        let uu____10306 = lookup_qname env lid0 in
        match uu____10306 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10337);
                FStar_Syntax_Syntax.sigrng = uu____10338;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10340;
                FStar_Syntax_Syntax.sigattrs = uu____10341;_},FStar_Pervasives_Native.None
              ),uu____10342)
            ->
            let lid1 =
              let uu____10396 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____10396 in
            let uu____10397 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_10401  ->
                      match uu___117_10401 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10402 -> false)) in
            if uu____10397
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10416 =
                      let uu____10417 =
                        let uu____10418 = get_range env in
                        FStar_Range.string_of_range uu____10418 in
                      let uu____10419 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10420 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10417 uu____10419 uu____10420 in
                    failwith uu____10416) in
               match (binders, univs1) with
               | ([],uu____10427) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10444,uu____10445::uu____10446::uu____10447) ->
                   let uu____10452 =
                     let uu____10453 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10454 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10453 uu____10454 in
                   failwith uu____10452
               | uu____10461 ->
                   let uu____10466 =
                     let uu____10471 =
                       let uu____10472 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10472) in
                     inst_tscheme_with uu____10471 insts in
                   (match uu____10466 with
                    | (uu____10483,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10486 =
                          let uu____10487 = FStar_Syntax_Subst.compress t1 in
                          uu____10487.FStar_Syntax_Syntax.n in
                        (match uu____10486 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10534 -> failwith "Impossible")))
        | uu____10541 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10583 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10583 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10596,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10603 = find1 l2 in
            (match uu____10603 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10610 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10610 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10614 = find1 l in
            (match uu____10614 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10630 = lookup_qname env l1 in
      match uu____10630 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10653;
              FStar_Syntax_Syntax.sigrng = uu____10654;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10656;
              FStar_Syntax_Syntax.sigattrs = uu____10657;_},uu____10658),uu____10659)
          -> q
      | uu____10710 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10746 =
          let uu____10747 =
            let uu____10748 = FStar_Util.string_of_int i in
            let uu____10749 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10748 uu____10749 in
          failwith uu____10747 in
        let uu____10750 = lookup_datacon env lid in
        match uu____10750 with
        | (uu____10755,t) ->
            let uu____10757 =
              let uu____10758 = FStar_Syntax_Subst.compress t in
              uu____10758.FStar_Syntax_Syntax.n in
            (match uu____10757 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10762) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10793 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10793
                      FStar_Pervasives_Native.fst)
             | uu____10802 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10811 = lookup_qname env l in
      match uu____10811 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10832,uu____10833,uu____10834);
              FStar_Syntax_Syntax.sigrng = uu____10835;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10837;
              FStar_Syntax_Syntax.sigattrs = uu____10838;_},uu____10839),uu____10840)
          ->
          FStar_Util.for_some
            (fun uu___118_10893  ->
               match uu___118_10893 with
               | FStar_Syntax_Syntax.Projector uu____10894 -> true
               | uu____10899 -> false) quals
      | uu____10900 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10929 = lookup_qname env lid in
      match uu____10929 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10950,uu____10951,uu____10952,uu____10953,uu____10954,uu____10955);
              FStar_Syntax_Syntax.sigrng = uu____10956;
              FStar_Syntax_Syntax.sigquals = uu____10957;
              FStar_Syntax_Syntax.sigmeta = uu____10958;
              FStar_Syntax_Syntax.sigattrs = uu____10959;_},uu____10960),uu____10961)
          -> true
      | uu____11016 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11045 = lookup_qname env lid in
      match uu____11045 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11066,uu____11067,uu____11068,uu____11069,uu____11070,uu____11071);
              FStar_Syntax_Syntax.sigrng = uu____11072;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11074;
              FStar_Syntax_Syntax.sigattrs = uu____11075;_},uu____11076),uu____11077)
          ->
          FStar_Util.for_some
            (fun uu___119_11138  ->
               match uu___119_11138 with
               | FStar_Syntax_Syntax.RecordType uu____11139 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11148 -> true
               | uu____11157 -> false) quals
      | uu____11158 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11187 = lookup_qname env lid in
      match uu____11187 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11208,uu____11209);
              FStar_Syntax_Syntax.sigrng = uu____11210;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11212;
              FStar_Syntax_Syntax.sigattrs = uu____11213;_},uu____11214),uu____11215)
          ->
          FStar_Util.for_some
            (fun uu___120_11272  ->
               match uu___120_11272 with
               | FStar_Syntax_Syntax.Action uu____11273 -> true
               | uu____11274 -> false) quals
      | uu____11275 -> false
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
      let uu____11307 =
        let uu____11308 = FStar_Syntax_Util.un_uinst head1 in
        uu____11308.FStar_Syntax_Syntax.n in
      match uu____11307 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11312 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11379 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11395) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11412 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11419 ->
                 FStar_Pervasives_Native.Some true
             | uu____11436 -> FStar_Pervasives_Native.Some false) in
      let uu____11437 =
        let uu____11440 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11440 mapper in
      match uu____11437 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11488 = lookup_qname env lid in
      match uu____11488 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11509,uu____11510,tps,uu____11512,uu____11513,uu____11514);
              FStar_Syntax_Syntax.sigrng = uu____11515;
              FStar_Syntax_Syntax.sigquals = uu____11516;
              FStar_Syntax_Syntax.sigmeta = uu____11517;
              FStar_Syntax_Syntax.sigattrs = uu____11518;_},uu____11519),uu____11520)
          -> FStar_List.length tps
      | uu____11583 ->
          let uu____11604 =
            let uu____11605 =
              let uu____11610 = name_not_found lid in
              (uu____11610, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11605 in
          FStar_Exn.raise uu____11604
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
           (fun uu____11652  ->
              match uu____11652 with
              | (d,uu____11660) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11673 = effect_decl_opt env l in
      match uu____11673 with
      | FStar_Pervasives_Native.None  ->
          let uu____11688 =
            let uu____11689 =
              let uu____11694 = name_not_found l in
              (uu____11694, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11689 in
          FStar_Exn.raise uu____11688
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
            (let uu____11760 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11813  ->
                       match uu____11813 with
                       | (m1,m2,uu____11826,uu____11827,uu____11828) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11760 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11845 =
                   let uu____11846 =
                     let uu____11851 =
                       let uu____11852 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11853 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11852
                         uu____11853 in
                     (uu____11851, (env.range)) in
                   FStar_Errors.Error uu____11846 in
                 FStar_Exn.raise uu____11845
             | FStar_Pervasives_Native.Some
                 (uu____11860,uu____11861,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11904 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11904)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11931 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11957  ->
                match uu____11957 with
                | (d,uu____11963) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11931 with
      | FStar_Pervasives_Native.None  ->
          let uu____11974 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11974
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11987 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11987 with
           | (uu____11998,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12008)::(wp,uu____12010)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12046 -> failwith "Impossible"))
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
                 let uu____12095 = get_range env in
                 let uu____12096 =
                   let uu____12099 =
                     let uu____12100 =
                       let uu____12115 =
                         let uu____12118 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12118] in
                       (null_wp, uu____12115) in
                     FStar_Syntax_Syntax.Tm_app uu____12100 in
                   FStar_Syntax_Syntax.mk uu____12099 in
                 uu____12096 FStar_Pervasives_Native.None uu____12095 in
               let uu____12124 =
                 let uu____12125 =
                   let uu____12134 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12134] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12125;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12124)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___133_12145 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___133_12145.order);
              joins = (uu___133_12145.joins)
            } in
          let uu___134_12154 = env in
          {
            solver = (uu___134_12154.solver);
            range = (uu___134_12154.range);
            curmodule = (uu___134_12154.curmodule);
            gamma = (uu___134_12154.gamma);
            gamma_cache = (uu___134_12154.gamma_cache);
            modules = (uu___134_12154.modules);
            expected_typ = (uu___134_12154.expected_typ);
            sigtab = (uu___134_12154.sigtab);
            is_pattern = (uu___134_12154.is_pattern);
            instantiate_imp = (uu___134_12154.instantiate_imp);
            effects;
            generalize = (uu___134_12154.generalize);
            letrecs = (uu___134_12154.letrecs);
            top_level = (uu___134_12154.top_level);
            check_uvars = (uu___134_12154.check_uvars);
            use_eq = (uu___134_12154.use_eq);
            is_iface = (uu___134_12154.is_iface);
            admit = (uu___134_12154.admit);
            lax = (uu___134_12154.lax);
            lax_universes = (uu___134_12154.lax_universes);
            failhard = (uu___134_12154.failhard);
            nosynth = (uu___134_12154.nosynth);
            tc_term = (uu___134_12154.tc_term);
            type_of = (uu___134_12154.type_of);
            universe_of = (uu___134_12154.universe_of);
            use_bv_sorts = (uu___134_12154.use_bv_sorts);
            qname_and_index = (uu___134_12154.qname_and_index);
            proof_ns = (uu___134_12154.proof_ns);
            synth = (uu___134_12154.synth);
            is_native_tactic = (uu___134_12154.is_native_tactic);
            identifier_info = (uu___134_12154.identifier_info);
            tc_hooks = (uu___134_12154.tc_hooks)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12171 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12171 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12261 = (e1.mlift).mlift_wp t wp in
                              let uu____12262 = l1 t wp e in
                              l2 t uu____12261 uu____12262))
                | uu____12263 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12302 = inst_tscheme lift_t in
            match uu____12302 with
            | (uu____12309,lift_t1) ->
                let uu____12311 =
                  let uu____12314 =
                    let uu____12315 =
                      let uu____12330 =
                        let uu____12333 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12334 =
                          let uu____12337 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12337] in
                        uu____12333 :: uu____12334 in
                      (lift_t1, uu____12330) in
                    FStar_Syntax_Syntax.Tm_app uu____12315 in
                  FStar_Syntax_Syntax.mk uu____12314 in
                uu____12311 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12378 = inst_tscheme lift_t in
            match uu____12378 with
            | (uu____12385,lift_t1) ->
                let uu____12387 =
                  let uu____12390 =
                    let uu____12391 =
                      let uu____12406 =
                        let uu____12409 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12410 =
                          let uu____12413 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12414 =
                            let uu____12417 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12417] in
                          uu____12413 :: uu____12414 in
                        uu____12409 :: uu____12410 in
                      (lift_t1, uu____12406) in
                    FStar_Syntax_Syntax.Tm_app uu____12391 in
                  FStar_Syntax_Syntax.mk uu____12390 in
                uu____12387 FStar_Pervasives_Native.None
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
              let uu____12455 =
                let uu____12456 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12456
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12455 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12460 =
              let uu____12461 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12461 in
            let uu____12462 =
              let uu____12463 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12481 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12481) in
              FStar_Util.dflt "none" uu____12463 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12460
              uu____12462 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12507  ->
                    match uu____12507 with
                    | (e,uu____12515) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12534 =
            match uu____12534 with
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
              let uu____12572 =
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
                                    (let uu____12593 =
                                       let uu____12602 =
                                         find_edge order1 (i, k) in
                                       let uu____12605 =
                                         find_edge order1 (k, j) in
                                       (uu____12602, uu____12605) in
                                     match uu____12593 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12620 =
                                           compose_edges e1 e2 in
                                         [uu____12620]
                                     | uu____12621 -> []))))) in
              FStar_List.append order1 uu____12572 in
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
                   let uu____12650 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12652 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12652
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12650
                   then
                     let uu____12657 =
                       let uu____12658 =
                         let uu____12663 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12664 = get_range env in
                         (uu____12663, uu____12664) in
                       FStar_Errors.Error uu____12658 in
                     FStar_Exn.raise uu____12657
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
                                            let uu____12789 =
                                              let uu____12798 =
                                                find_edge order2 (i, k) in
                                              let uu____12801 =
                                                find_edge order2 (j, k) in
                                              (uu____12798, uu____12801) in
                                            match uu____12789 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12843,uu____12844)
                                                     ->
                                                     let uu____12851 =
                                                       let uu____12856 =
                                                         let uu____12857 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12857 in
                                                       let uu____12860 =
                                                         let uu____12861 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12861 in
                                                       (uu____12856,
                                                         uu____12860) in
                                                     (match uu____12851 with
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
                                            | uu____12896 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___135_12969 = env.effects in
              { decls = (uu___135_12969.decls); order = order2; joins } in
            let uu___136_12970 = env in
            {
              solver = (uu___136_12970.solver);
              range = (uu___136_12970.range);
              curmodule = (uu___136_12970.curmodule);
              gamma = (uu___136_12970.gamma);
              gamma_cache = (uu___136_12970.gamma_cache);
              modules = (uu___136_12970.modules);
              expected_typ = (uu___136_12970.expected_typ);
              sigtab = (uu___136_12970.sigtab);
              is_pattern = (uu___136_12970.is_pattern);
              instantiate_imp = (uu___136_12970.instantiate_imp);
              effects;
              generalize = (uu___136_12970.generalize);
              letrecs = (uu___136_12970.letrecs);
              top_level = (uu___136_12970.top_level);
              check_uvars = (uu___136_12970.check_uvars);
              use_eq = (uu___136_12970.use_eq);
              is_iface = (uu___136_12970.is_iface);
              admit = (uu___136_12970.admit);
              lax = (uu___136_12970.lax);
              lax_universes = (uu___136_12970.lax_universes);
              failhard = (uu___136_12970.failhard);
              nosynth = (uu___136_12970.nosynth);
              tc_term = (uu___136_12970.tc_term);
              type_of = (uu___136_12970.type_of);
              universe_of = (uu___136_12970.universe_of);
              use_bv_sorts = (uu___136_12970.use_bv_sorts);
              qname_and_index = (uu___136_12970.qname_and_index);
              proof_ns = (uu___136_12970.proof_ns);
              synth = (uu___136_12970.synth);
              is_native_tactic = (uu___136_12970.is_native_tactic);
              identifier_info = (uu___136_12970.identifier_info);
              tc_hooks = (uu___136_12970.tc_hooks)
            }))
      | uu____12971 -> env
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
        | uu____12997 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13007 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13007 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13024 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13024 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13042 =
                     let uu____13043 =
                       let uu____13048 =
                         let uu____13049 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13054 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13061 =
                           let uu____13062 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13062 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13049 uu____13054 uu____13061 in
                       (uu____13048, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13043 in
                   FStar_Exn.raise uu____13042)
                else ();
                (let inst1 =
                   let uu____13067 =
                     let uu____13076 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13076 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13093  ->
                        fun uu____13094  ->
                          match (uu____13093, uu____13094) with
                          | ((x,uu____13116),(t,uu____13118)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13067 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13137 =
                     let uu___137_13138 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___137_13138.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___137_13138.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___137_13138.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___137_13138.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13137
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
          let uu____13164 = effect_decl_opt env effect_name in
          match uu____13164 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13197 =
                only_reifiable &&
                  (let uu____13199 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13199) in
              if uu____13197
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13215 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13234 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13263 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13263
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13264 =
                             let uu____13265 =
                               let uu____13270 = get_range env in
                               (message, uu____13270) in
                             FStar_Errors.Error uu____13265 in
                           FStar_Exn.raise uu____13264 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13280 =
                       let uu____13283 = get_range env in
                       let uu____13284 =
                         let uu____13287 =
                           let uu____13288 =
                             let uu____13303 =
                               let uu____13306 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13306; wp] in
                             (repr, uu____13303) in
                           FStar_Syntax_Syntax.Tm_app uu____13288 in
                         FStar_Syntax_Syntax.mk uu____13287 in
                       uu____13284 FStar_Pervasives_Native.None uu____13283 in
                     FStar_Pervasives_Native.Some uu____13280)
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
          let uu____13358 =
            let uu____13359 =
              let uu____13364 =
                let uu____13365 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13365 in
              let uu____13366 = get_range env in (uu____13364, uu____13366) in
            FStar_Errors.Error uu____13359 in
          FStar_Exn.raise uu____13358 in
        let uu____13367 = effect_repr_aux true env c u_c in
        match uu____13367 with
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
      | uu____13407 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13416 =
        let uu____13417 = FStar_Syntax_Subst.compress t in
        uu____13417.FStar_Syntax_Syntax.n in
      match uu____13416 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13420,c) ->
          is_reifiable_comp env c
      | uu____13438 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13462)::uu____13463 -> x :: rest
        | (Binding_sig_inst uu____13472)::uu____13473 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13488 = push1 x rest1 in local :: uu____13488 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___138_13492 = env in
       let uu____13493 = push1 s env.gamma in
       {
         solver = (uu___138_13492.solver);
         range = (uu___138_13492.range);
         curmodule = (uu___138_13492.curmodule);
         gamma = uu____13493;
         gamma_cache = (uu___138_13492.gamma_cache);
         modules = (uu___138_13492.modules);
         expected_typ = (uu___138_13492.expected_typ);
         sigtab = (uu___138_13492.sigtab);
         is_pattern = (uu___138_13492.is_pattern);
         instantiate_imp = (uu___138_13492.instantiate_imp);
         effects = (uu___138_13492.effects);
         generalize = (uu___138_13492.generalize);
         letrecs = (uu___138_13492.letrecs);
         top_level = (uu___138_13492.top_level);
         check_uvars = (uu___138_13492.check_uvars);
         use_eq = (uu___138_13492.use_eq);
         is_iface = (uu___138_13492.is_iface);
         admit = (uu___138_13492.admit);
         lax = (uu___138_13492.lax);
         lax_universes = (uu___138_13492.lax_universes);
         failhard = (uu___138_13492.failhard);
         nosynth = (uu___138_13492.nosynth);
         tc_term = (uu___138_13492.tc_term);
         type_of = (uu___138_13492.type_of);
         universe_of = (uu___138_13492.universe_of);
         use_bv_sorts = (uu___138_13492.use_bv_sorts);
         qname_and_index = (uu___138_13492.qname_and_index);
         proof_ns = (uu___138_13492.proof_ns);
         synth = (uu___138_13492.synth);
         is_native_tactic = (uu___138_13492.is_native_tactic);
         identifier_info = (uu___138_13492.identifier_info);
         tc_hooks = (uu___138_13492.tc_hooks)
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
      let uu___139_13530 = env in
      {
        solver = (uu___139_13530.solver);
        range = (uu___139_13530.range);
        curmodule = (uu___139_13530.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___139_13530.gamma_cache);
        modules = (uu___139_13530.modules);
        expected_typ = (uu___139_13530.expected_typ);
        sigtab = (uu___139_13530.sigtab);
        is_pattern = (uu___139_13530.is_pattern);
        instantiate_imp = (uu___139_13530.instantiate_imp);
        effects = (uu___139_13530.effects);
        generalize = (uu___139_13530.generalize);
        letrecs = (uu___139_13530.letrecs);
        top_level = (uu___139_13530.top_level);
        check_uvars = (uu___139_13530.check_uvars);
        use_eq = (uu___139_13530.use_eq);
        is_iface = (uu___139_13530.is_iface);
        admit = (uu___139_13530.admit);
        lax = (uu___139_13530.lax);
        lax_universes = (uu___139_13530.lax_universes);
        failhard = (uu___139_13530.failhard);
        nosynth = (uu___139_13530.nosynth);
        tc_term = (uu___139_13530.tc_term);
        type_of = (uu___139_13530.type_of);
        universe_of = (uu___139_13530.universe_of);
        use_bv_sorts = (uu___139_13530.use_bv_sorts);
        qname_and_index = (uu___139_13530.qname_and_index);
        proof_ns = (uu___139_13530.proof_ns);
        synth = (uu___139_13530.synth);
        is_native_tactic = (uu___139_13530.is_native_tactic);
        identifier_info = (uu___139_13530.identifier_info);
        tc_hooks = (uu___139_13530.tc_hooks)
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
            (let uu___140_13564 = env in
             {
               solver = (uu___140_13564.solver);
               range = (uu___140_13564.range);
               curmodule = (uu___140_13564.curmodule);
               gamma = rest;
               gamma_cache = (uu___140_13564.gamma_cache);
               modules = (uu___140_13564.modules);
               expected_typ = (uu___140_13564.expected_typ);
               sigtab = (uu___140_13564.sigtab);
               is_pattern = (uu___140_13564.is_pattern);
               instantiate_imp = (uu___140_13564.instantiate_imp);
               effects = (uu___140_13564.effects);
               generalize = (uu___140_13564.generalize);
               letrecs = (uu___140_13564.letrecs);
               top_level = (uu___140_13564.top_level);
               check_uvars = (uu___140_13564.check_uvars);
               use_eq = (uu___140_13564.use_eq);
               is_iface = (uu___140_13564.is_iface);
               admit = (uu___140_13564.admit);
               lax = (uu___140_13564.lax);
               lax_universes = (uu___140_13564.lax_universes);
               failhard = (uu___140_13564.failhard);
               nosynth = (uu___140_13564.nosynth);
               tc_term = (uu___140_13564.tc_term);
               type_of = (uu___140_13564.type_of);
               universe_of = (uu___140_13564.universe_of);
               use_bv_sorts = (uu___140_13564.use_bv_sorts);
               qname_and_index = (uu___140_13564.qname_and_index);
               proof_ns = (uu___140_13564.proof_ns);
               synth = (uu___140_13564.synth);
               is_native_tactic = (uu___140_13564.is_native_tactic);
               identifier_info = (uu___140_13564.identifier_info);
               tc_hooks = (uu___140_13564.tc_hooks)
             }))
    | uu____13565 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13589  ->
             match uu____13589 with | (x,uu____13595) -> push_bv env1 x) env
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
            let uu___141_13625 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___141_13625.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___141_13625.FStar_Syntax_Syntax.index);
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
      (let uu___142_13660 = env in
       {
         solver = (uu___142_13660.solver);
         range = (uu___142_13660.range);
         curmodule = (uu___142_13660.curmodule);
         gamma = [];
         gamma_cache = (uu___142_13660.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___142_13660.sigtab);
         is_pattern = (uu___142_13660.is_pattern);
         instantiate_imp = (uu___142_13660.instantiate_imp);
         effects = (uu___142_13660.effects);
         generalize = (uu___142_13660.generalize);
         letrecs = (uu___142_13660.letrecs);
         top_level = (uu___142_13660.top_level);
         check_uvars = (uu___142_13660.check_uvars);
         use_eq = (uu___142_13660.use_eq);
         is_iface = (uu___142_13660.is_iface);
         admit = (uu___142_13660.admit);
         lax = (uu___142_13660.lax);
         lax_universes = (uu___142_13660.lax_universes);
         failhard = (uu___142_13660.failhard);
         nosynth = (uu___142_13660.nosynth);
         tc_term = (uu___142_13660.tc_term);
         type_of = (uu___142_13660.type_of);
         universe_of = (uu___142_13660.universe_of);
         use_bv_sorts = (uu___142_13660.use_bv_sorts);
         qname_and_index = (uu___142_13660.qname_and_index);
         proof_ns = (uu___142_13660.proof_ns);
         synth = (uu___142_13660.synth);
         is_native_tactic = (uu___142_13660.is_native_tactic);
         identifier_info = (uu___142_13660.identifier_info);
         tc_hooks = (uu___142_13660.tc_hooks)
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
        let uu____13697 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13697 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13725 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13725)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___143_13740 = env in
      {
        solver = (uu___143_13740.solver);
        range = (uu___143_13740.range);
        curmodule = (uu___143_13740.curmodule);
        gamma = (uu___143_13740.gamma);
        gamma_cache = (uu___143_13740.gamma_cache);
        modules = (uu___143_13740.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___143_13740.sigtab);
        is_pattern = (uu___143_13740.is_pattern);
        instantiate_imp = (uu___143_13740.instantiate_imp);
        effects = (uu___143_13740.effects);
        generalize = (uu___143_13740.generalize);
        letrecs = (uu___143_13740.letrecs);
        top_level = (uu___143_13740.top_level);
        check_uvars = (uu___143_13740.check_uvars);
        use_eq = false;
        is_iface = (uu___143_13740.is_iface);
        admit = (uu___143_13740.admit);
        lax = (uu___143_13740.lax);
        lax_universes = (uu___143_13740.lax_universes);
        failhard = (uu___143_13740.failhard);
        nosynth = (uu___143_13740.nosynth);
        tc_term = (uu___143_13740.tc_term);
        type_of = (uu___143_13740.type_of);
        universe_of = (uu___143_13740.universe_of);
        use_bv_sorts = (uu___143_13740.use_bv_sorts);
        qname_and_index = (uu___143_13740.qname_and_index);
        proof_ns = (uu___143_13740.proof_ns);
        synth = (uu___143_13740.synth);
        is_native_tactic = (uu___143_13740.is_native_tactic);
        identifier_info = (uu___143_13740.identifier_info);
        tc_hooks = (uu___143_13740.tc_hooks)
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
    let uu____13766 = expected_typ env_ in
    ((let uu___144_13772 = env_ in
      {
        solver = (uu___144_13772.solver);
        range = (uu___144_13772.range);
        curmodule = (uu___144_13772.curmodule);
        gamma = (uu___144_13772.gamma);
        gamma_cache = (uu___144_13772.gamma_cache);
        modules = (uu___144_13772.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___144_13772.sigtab);
        is_pattern = (uu___144_13772.is_pattern);
        instantiate_imp = (uu___144_13772.instantiate_imp);
        effects = (uu___144_13772.effects);
        generalize = (uu___144_13772.generalize);
        letrecs = (uu___144_13772.letrecs);
        top_level = (uu___144_13772.top_level);
        check_uvars = (uu___144_13772.check_uvars);
        use_eq = false;
        is_iface = (uu___144_13772.is_iface);
        admit = (uu___144_13772.admit);
        lax = (uu___144_13772.lax);
        lax_universes = (uu___144_13772.lax_universes);
        failhard = (uu___144_13772.failhard);
        nosynth = (uu___144_13772.nosynth);
        tc_term = (uu___144_13772.tc_term);
        type_of = (uu___144_13772.type_of);
        universe_of = (uu___144_13772.universe_of);
        use_bv_sorts = (uu___144_13772.use_bv_sorts);
        qname_and_index = (uu___144_13772.qname_and_index);
        proof_ns = (uu___144_13772.proof_ns);
        synth = (uu___144_13772.synth);
        is_native_tactic = (uu___144_13772.is_native_tactic);
        identifier_info = (uu___144_13772.identifier_info);
        tc_hooks = (uu___144_13772.tc_hooks)
      }), uu____13766)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13787 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___121_13797  ->
                    match uu___121_13797 with
                    | Binding_sig (uu____13800,se) -> [se]
                    | uu____13806 -> [])) in
          FStar_All.pipe_right uu____13787 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___145_13813 = env in
       {
         solver = (uu___145_13813.solver);
         range = (uu___145_13813.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___145_13813.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___145_13813.expected_typ);
         sigtab = (uu___145_13813.sigtab);
         is_pattern = (uu___145_13813.is_pattern);
         instantiate_imp = (uu___145_13813.instantiate_imp);
         effects = (uu___145_13813.effects);
         generalize = (uu___145_13813.generalize);
         letrecs = (uu___145_13813.letrecs);
         top_level = (uu___145_13813.top_level);
         check_uvars = (uu___145_13813.check_uvars);
         use_eq = (uu___145_13813.use_eq);
         is_iface = (uu___145_13813.is_iface);
         admit = (uu___145_13813.admit);
         lax = (uu___145_13813.lax);
         lax_universes = (uu___145_13813.lax_universes);
         failhard = (uu___145_13813.failhard);
         nosynth = (uu___145_13813.nosynth);
         tc_term = (uu___145_13813.tc_term);
         type_of = (uu___145_13813.type_of);
         universe_of = (uu___145_13813.universe_of);
         use_bv_sorts = (uu___145_13813.use_bv_sorts);
         qname_and_index = (uu___145_13813.qname_and_index);
         proof_ns = (uu___145_13813.proof_ns);
         synth = (uu___145_13813.synth);
         is_native_tactic = (uu___145_13813.is_native_tactic);
         identifier_info = (uu___145_13813.identifier_info);
         tc_hooks = (uu___145_13813.tc_hooks)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13895)::tl1 -> aux out tl1
      | (Binding_lid (uu____13899,(uu____13900,t)))::tl1 ->
          let uu____13915 =
            let uu____13922 = FStar_Syntax_Free.uvars t in
            ext out uu____13922 in
          aux uu____13915 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13929;
            FStar_Syntax_Syntax.index = uu____13930;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13937 =
            let uu____13944 = FStar_Syntax_Free.uvars t in
            ext out uu____13944 in
          aux uu____13937 tl1
      | (Binding_sig uu____13951)::uu____13952 -> out
      | (Binding_sig_inst uu____13961)::uu____13962 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14018)::tl1 -> aux out tl1
      | (Binding_univ uu____14030)::tl1 -> aux out tl1
      | (Binding_lid (uu____14034,(uu____14035,t)))::tl1 ->
          let uu____14050 =
            let uu____14053 = FStar_Syntax_Free.univs t in
            ext out uu____14053 in
          aux uu____14050 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14056;
            FStar_Syntax_Syntax.index = uu____14057;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14064 =
            let uu____14067 = FStar_Syntax_Free.univs t in
            ext out uu____14067 in
          aux uu____14064 tl1
      | (Binding_sig uu____14070)::uu____14071 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14125)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14141 = FStar_Util.fifo_set_add uname out in
          aux uu____14141 tl1
      | (Binding_lid (uu____14144,(uu____14145,t)))::tl1 ->
          let uu____14160 =
            let uu____14163 = FStar_Syntax_Free.univnames t in
            ext out uu____14163 in
          aux uu____14160 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14166;
            FStar_Syntax_Syntax.index = uu____14167;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14174 =
            let uu____14177 = FStar_Syntax_Free.univnames t in
            ext out uu____14177 in
          aux uu____14174 tl1
      | (Binding_sig uu____14180)::uu____14181 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___122_14206  ->
            match uu___122_14206 with
            | Binding_var x -> [x]
            | Binding_lid uu____14210 -> []
            | Binding_sig uu____14215 -> []
            | Binding_univ uu____14222 -> []
            | Binding_sig_inst uu____14223 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14240 =
      let uu____14243 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14243
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14240 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14268 =
      let uu____14269 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___123_14279  ->
                match uu___123_14279 with
                | Binding_var x ->
                    let uu____14281 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14281
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14284) ->
                    let uu____14285 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14285
                | Binding_sig (ls,uu____14287) ->
                    let uu____14292 =
                      let uu____14293 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14293
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14292
                | Binding_sig_inst (ls,uu____14303,uu____14304) ->
                    let uu____14309 =
                      let uu____14310 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14310
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14309)) in
      FStar_All.pipe_right uu____14269 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14268 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14329 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14329
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14357  ->
                 fun uu____14358  ->
                   match (uu____14357, uu____14358) with
                   | ((b1,uu____14376),(b2,uu____14378)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___124_14425  ->
    match uu___124_14425 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14426 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___125_14445  ->
             match uu___125_14445 with
             | Binding_sig (lids,uu____14451) -> FStar_List.append lids keys
             | uu____14456 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14462  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14498) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14517,uu____14518) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____14555 = list_prefix p path1 in
            if uu____14555 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14569 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14569
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___146_14599 = e in
            {
              solver = (uu___146_14599.solver);
              range = (uu___146_14599.range);
              curmodule = (uu___146_14599.curmodule);
              gamma = (uu___146_14599.gamma);
              gamma_cache = (uu___146_14599.gamma_cache);
              modules = (uu___146_14599.modules);
              expected_typ = (uu___146_14599.expected_typ);
              sigtab = (uu___146_14599.sigtab);
              is_pattern = (uu___146_14599.is_pattern);
              instantiate_imp = (uu___146_14599.instantiate_imp);
              effects = (uu___146_14599.effects);
              generalize = (uu___146_14599.generalize);
              letrecs = (uu___146_14599.letrecs);
              top_level = (uu___146_14599.top_level);
              check_uvars = (uu___146_14599.check_uvars);
              use_eq = (uu___146_14599.use_eq);
              is_iface = (uu___146_14599.is_iface);
              admit = (uu___146_14599.admit);
              lax = (uu___146_14599.lax);
              lax_universes = (uu___146_14599.lax_universes);
              failhard = (uu___146_14599.failhard);
              nosynth = (uu___146_14599.nosynth);
              tc_term = (uu___146_14599.tc_term);
              type_of = (uu___146_14599.type_of);
              universe_of = (uu___146_14599.universe_of);
              use_bv_sorts = (uu___146_14599.use_bv_sorts);
              qname_and_index = (uu___146_14599.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___146_14599.synth);
              is_native_tactic = (uu___146_14599.is_native_tactic);
              identifier_info = (uu___146_14599.identifier_info);
              tc_hooks = (uu___146_14599.tc_hooks)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___147_14626 = e in
    {
      solver = (uu___147_14626.solver);
      range = (uu___147_14626.range);
      curmodule = (uu___147_14626.curmodule);
      gamma = (uu___147_14626.gamma);
      gamma_cache = (uu___147_14626.gamma_cache);
      modules = (uu___147_14626.modules);
      expected_typ = (uu___147_14626.expected_typ);
      sigtab = (uu___147_14626.sigtab);
      is_pattern = (uu___147_14626.is_pattern);
      instantiate_imp = (uu___147_14626.instantiate_imp);
      effects = (uu___147_14626.effects);
      generalize = (uu___147_14626.generalize);
      letrecs = (uu___147_14626.letrecs);
      top_level = (uu___147_14626.top_level);
      check_uvars = (uu___147_14626.check_uvars);
      use_eq = (uu___147_14626.use_eq);
      is_iface = (uu___147_14626.is_iface);
      admit = (uu___147_14626.admit);
      lax = (uu___147_14626.lax);
      lax_universes = (uu___147_14626.lax_universes);
      failhard = (uu___147_14626.failhard);
      nosynth = (uu___147_14626.nosynth);
      tc_term = (uu___147_14626.tc_term);
      type_of = (uu___147_14626.type_of);
      universe_of = (uu___147_14626.universe_of);
      use_bv_sorts = (uu___147_14626.use_bv_sorts);
      qname_and_index = (uu___147_14626.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___147_14626.synth);
      is_native_tactic = (uu___147_14626.is_native_tactic);
      identifier_info = (uu___147_14626.identifier_info);
      tc_hooks = (uu___147_14626.tc_hooks)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14641::rest ->
        let uu___148_14645 = e in
        {
          solver = (uu___148_14645.solver);
          range = (uu___148_14645.range);
          curmodule = (uu___148_14645.curmodule);
          gamma = (uu___148_14645.gamma);
          gamma_cache = (uu___148_14645.gamma_cache);
          modules = (uu___148_14645.modules);
          expected_typ = (uu___148_14645.expected_typ);
          sigtab = (uu___148_14645.sigtab);
          is_pattern = (uu___148_14645.is_pattern);
          instantiate_imp = (uu___148_14645.instantiate_imp);
          effects = (uu___148_14645.effects);
          generalize = (uu___148_14645.generalize);
          letrecs = (uu___148_14645.letrecs);
          top_level = (uu___148_14645.top_level);
          check_uvars = (uu___148_14645.check_uvars);
          use_eq = (uu___148_14645.use_eq);
          is_iface = (uu___148_14645.is_iface);
          admit = (uu___148_14645.admit);
          lax = (uu___148_14645.lax);
          lax_universes = (uu___148_14645.lax_universes);
          failhard = (uu___148_14645.failhard);
          nosynth = (uu___148_14645.nosynth);
          tc_term = (uu___148_14645.tc_term);
          type_of = (uu___148_14645.type_of);
          universe_of = (uu___148_14645.universe_of);
          use_bv_sorts = (uu___148_14645.use_bv_sorts);
          qname_and_index = (uu___148_14645.qname_and_index);
          proof_ns = rest;
          synth = (uu___148_14645.synth);
          is_native_tactic = (uu___148_14645.is_native_tactic);
          identifier_info = (uu___148_14645.identifier_info);
          tc_hooks = (uu___148_14645.tc_hooks)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___149_14658 = e in
      {
        solver = (uu___149_14658.solver);
        range = (uu___149_14658.range);
        curmodule = (uu___149_14658.curmodule);
        gamma = (uu___149_14658.gamma);
        gamma_cache = (uu___149_14658.gamma_cache);
        modules = (uu___149_14658.modules);
        expected_typ = (uu___149_14658.expected_typ);
        sigtab = (uu___149_14658.sigtab);
        is_pattern = (uu___149_14658.is_pattern);
        instantiate_imp = (uu___149_14658.instantiate_imp);
        effects = (uu___149_14658.effects);
        generalize = (uu___149_14658.generalize);
        letrecs = (uu___149_14658.letrecs);
        top_level = (uu___149_14658.top_level);
        check_uvars = (uu___149_14658.check_uvars);
        use_eq = (uu___149_14658.use_eq);
        is_iface = (uu___149_14658.is_iface);
        admit = (uu___149_14658.admit);
        lax = (uu___149_14658.lax);
        lax_universes = (uu___149_14658.lax_universes);
        failhard = (uu___149_14658.failhard);
        nosynth = (uu___149_14658.nosynth);
        tc_term = (uu___149_14658.tc_term);
        type_of = (uu___149_14658.type_of);
        universe_of = (uu___149_14658.universe_of);
        use_bv_sorts = (uu___149_14658.use_bv_sorts);
        qname_and_index = (uu___149_14658.qname_and_index);
        proof_ns = ns;
        synth = (uu___149_14658.synth);
        is_native_tactic = (uu___149_14658.is_native_tactic);
        identifier_info = (uu___149_14658.identifier_info);
        tc_hooks = (uu___149_14658.tc_hooks)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14687 =
        FStar_List.map
          (fun fpns  ->
             let uu____14709 =
               let uu____14710 =
                 let uu____14711 =
                   FStar_List.map
                     (fun uu____14723  ->
                        match uu____14723 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14711 in
               Prims.strcat uu____14710 "]" in
             Prims.strcat "[" uu____14709) pns in
      FStar_String.concat ";" uu____14687 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14739  -> ());
    push = (fun uu____14741  -> ());
    pop = (fun uu____14743  -> ());
    encode_modul = (fun uu____14746  -> fun uu____14747  -> ());
    encode_sig = (fun uu____14750  -> fun uu____14751  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14757 =
             let uu____14764 = FStar_Options.peek () in (e, g, uu____14764) in
           [uu____14757]);
    solve = (fun uu____14780  -> fun uu____14781  -> fun uu____14782  -> ());
    finish = (fun uu____14788  -> ());
    refresh = (fun uu____14790  -> ())
  }