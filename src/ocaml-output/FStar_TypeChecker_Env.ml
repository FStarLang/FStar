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
  tc_hooks: tcenv_hooks;
  dsenv: FStar_ToSyntax_Env.env;}[@@deriving show]
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__solver
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__range
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__curmodule
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__gamma
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__gamma_cache
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__modules
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__expected_typ
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__sigtab
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__is_pattern
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__instantiate_imp
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__effects
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__generalize
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__letrecs
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__top_level
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__check_uvars
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__use_eq
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__is_iface
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__admit
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__lax
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__lax_universes
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__failhard
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__nosynth
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__tc_term
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__type_of
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__universe_of
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__use_bv_sorts
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__qname_and_index
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__proof_ns
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__synth
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__is_native_tactic
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__identifier_info
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__tc_hooks
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__dsenv
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
let rename_gamma:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___133_5059  ->
              match uu___133_5059 with
              | Binding_var x ->
                  let y =
                    let uu____5062 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____5062 in
                  let uu____5063 =
                    let uu____5064 = FStar_Syntax_Subst.compress y in
                    uu____5064.FStar_Syntax_Syntax.n in
                  (match uu____5063 with
                   | FStar_Syntax_Syntax.Tm_name y1 -> Binding_var y1
                   | uu____5068 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___147_5078 = env in
      let uu____5079 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___147_5078.solver);
        range = (uu___147_5078.range);
        curmodule = (uu___147_5078.curmodule);
        gamma = uu____5079;
        gamma_cache = (uu___147_5078.gamma_cache);
        modules = (uu___147_5078.modules);
        expected_typ = (uu___147_5078.expected_typ);
        sigtab = (uu___147_5078.sigtab);
        is_pattern = (uu___147_5078.is_pattern);
        instantiate_imp = (uu___147_5078.instantiate_imp);
        effects = (uu___147_5078.effects);
        generalize = (uu___147_5078.generalize);
        letrecs = (uu___147_5078.letrecs);
        top_level = (uu___147_5078.top_level);
        check_uvars = (uu___147_5078.check_uvars);
        use_eq = (uu___147_5078.use_eq);
        is_iface = (uu___147_5078.is_iface);
        admit = (uu___147_5078.admit);
        lax = (uu___147_5078.lax);
        lax_universes = (uu___147_5078.lax_universes);
        failhard = (uu___147_5078.failhard);
        nosynth = (uu___147_5078.nosynth);
        tc_term = (uu___147_5078.tc_term);
        type_of = (uu___147_5078.type_of);
        universe_of = (uu___147_5078.universe_of);
        use_bv_sorts = (uu___147_5078.use_bv_sorts);
        qname_and_index = (uu___147_5078.qname_and_index);
        proof_ns = (uu___147_5078.proof_ns);
        synth = (uu___147_5078.synth);
        is_native_tactic = (uu___147_5078.is_native_tactic);
        identifier_info = (uu___147_5078.identifier_info);
        tc_hooks = (uu___147_5078.tc_hooks);
        dsenv = (uu___147_5078.dsenv)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5086  -> fun uu____5087  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___148_5100 = env in
      {
        solver = (uu___148_5100.solver);
        range = (uu___148_5100.range);
        curmodule = (uu___148_5100.curmodule);
        gamma = (uu___148_5100.gamma);
        gamma_cache = (uu___148_5100.gamma_cache);
        modules = (uu___148_5100.modules);
        expected_typ = (uu___148_5100.expected_typ);
        sigtab = (uu___148_5100.sigtab);
        is_pattern = (uu___148_5100.is_pattern);
        instantiate_imp = (uu___148_5100.instantiate_imp);
        effects = (uu___148_5100.effects);
        generalize = (uu___148_5100.generalize);
        letrecs = (uu___148_5100.letrecs);
        top_level = (uu___148_5100.top_level);
        check_uvars = (uu___148_5100.check_uvars);
        use_eq = (uu___148_5100.use_eq);
        is_iface = (uu___148_5100.is_iface);
        admit = (uu___148_5100.admit);
        lax = (uu___148_5100.lax);
        lax_universes = (uu___148_5100.lax_universes);
        failhard = (uu___148_5100.failhard);
        nosynth = (uu___148_5100.nosynth);
        tc_term = (uu___148_5100.tc_term);
        type_of = (uu___148_5100.type_of);
        universe_of = (uu___148_5100.universe_of);
        use_bv_sorts = (uu___148_5100.use_bv_sorts);
        qname_and_index = (uu___148_5100.qname_and_index);
        proof_ns = (uu___148_5100.proof_ns);
        synth = (uu___148_5100.synth);
        is_native_tactic = (uu___148_5100.is_native_tactic);
        identifier_info = (uu___148_5100.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___148_5100.dsenv)
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
      | (NoDelta ,uu____5115) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5116,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5117,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5118 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5127 . Prims.unit -> 'Auu____5127 FStar_Util.smap =
  fun uu____5133  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5138 . Prims.unit -> 'Auu____5138 FStar_Util.smap =
  fun uu____5144  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____5219 = new_gamma_cache () in
            let uu____5222 = new_sigtab () in
            let uu____5225 =
              let uu____5226 = FStar_Options.using_facts_from () in
              match uu____5226 with
              | FStar_Pervasives_Native.Some ns ->
                  let uu____5236 =
                    let uu____5245 =
                      FStar_List.map
                        (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                    FStar_List.append uu____5245 [([], false)] in
                  [uu____5236]
              | FStar_Pervasives_Native.None  -> [[]] in
            let uu____5318 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            let uu____5321 = FStar_ToSyntax_Env.empty_env () in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____5219;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____5222;
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
              proof_ns = uu____5225;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5353  -> false);
              identifier_info = uu____5318;
              tc_hooks = default_tc_hooks;
              dsenv = uu____5321
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
  fun uu____5424  ->
    let uu____5425 = FStar_ST.op_Bang query_indices in
    match uu____5425 with
    | [] -> failwith "Empty query indices!"
    | uu____5502 ->
        let uu____5511 =
          let uu____5520 =
            let uu____5527 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5527 in
          let uu____5604 = FStar_ST.op_Bang query_indices in uu____5520 ::
            uu____5604 in
        FStar_ST.op_Colon_Equals query_indices uu____5511
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5746  ->
    let uu____5747 = FStar_ST.op_Bang query_indices in
    match uu____5747 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5915  ->
    match uu____5915 with
    | (l,n1) ->
        let uu____5922 = FStar_ST.op_Bang query_indices in
        (match uu____5922 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6087 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6105  ->
    let uu____6106 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____6106
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6201 =
       let uu____6204 = FStar_ST.op_Bang stack in env :: uu____6204 in
     FStar_ST.op_Colon_Equals stack uu____6201);
    (let uu___149_6307 = env in
     let uu____6308 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6311 = FStar_Util.smap_copy (sigtab env) in
     let uu____6314 =
       let uu____6317 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6317 in
     {
       solver = (uu___149_6307.solver);
       range = (uu___149_6307.range);
       curmodule = (uu___149_6307.curmodule);
       gamma = (uu___149_6307.gamma);
       gamma_cache = uu____6308;
       modules = (uu___149_6307.modules);
       expected_typ = (uu___149_6307.expected_typ);
       sigtab = uu____6311;
       is_pattern = (uu___149_6307.is_pattern);
       instantiate_imp = (uu___149_6307.instantiate_imp);
       effects = (uu___149_6307.effects);
       generalize = (uu___149_6307.generalize);
       letrecs = (uu___149_6307.letrecs);
       top_level = (uu___149_6307.top_level);
       check_uvars = (uu___149_6307.check_uvars);
       use_eq = (uu___149_6307.use_eq);
       is_iface = (uu___149_6307.is_iface);
       admit = (uu___149_6307.admit);
       lax = (uu___149_6307.lax);
       lax_universes = (uu___149_6307.lax_universes);
       failhard = (uu___149_6307.failhard);
       nosynth = (uu___149_6307.nosynth);
       tc_term = (uu___149_6307.tc_term);
       type_of = (uu___149_6307.type_of);
       universe_of = (uu___149_6307.universe_of);
       use_bv_sorts = (uu___149_6307.use_bv_sorts);
       qname_and_index = (uu___149_6307.qname_and_index);
       proof_ns = (uu___149_6307.proof_ns);
       synth = (uu___149_6307.synth);
       is_native_tactic = (uu___149_6307.is_native_tactic);
       identifier_info = uu____6314;
       tc_hooks = (uu___149_6307.tc_hooks);
       dsenv = (uu___149_6307.dsenv)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6381  ->
    let uu____6382 = FStar_ST.op_Bang stack in
    match uu____6382 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6490 -> failwith "Impossible: Too many pops"
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
        let uu____6534 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6560  ->
                  match uu____6560 with
                  | (m,uu____6566) -> FStar_Ident.lid_equals l m)) in
        (match uu____6534 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___150_6573 = env in
               {
                 solver = (uu___150_6573.solver);
                 range = (uu___150_6573.range);
                 curmodule = (uu___150_6573.curmodule);
                 gamma = (uu___150_6573.gamma);
                 gamma_cache = (uu___150_6573.gamma_cache);
                 modules = (uu___150_6573.modules);
                 expected_typ = (uu___150_6573.expected_typ);
                 sigtab = (uu___150_6573.sigtab);
                 is_pattern = (uu___150_6573.is_pattern);
                 instantiate_imp = (uu___150_6573.instantiate_imp);
                 effects = (uu___150_6573.effects);
                 generalize = (uu___150_6573.generalize);
                 letrecs = (uu___150_6573.letrecs);
                 top_level = (uu___150_6573.top_level);
                 check_uvars = (uu___150_6573.check_uvars);
                 use_eq = (uu___150_6573.use_eq);
                 is_iface = (uu___150_6573.is_iface);
                 admit = (uu___150_6573.admit);
                 lax = (uu___150_6573.lax);
                 lax_universes = (uu___150_6573.lax_universes);
                 failhard = (uu___150_6573.failhard);
                 nosynth = (uu___150_6573.nosynth);
                 tc_term = (uu___150_6573.tc_term);
                 type_of = (uu___150_6573.type_of);
                 universe_of = (uu___150_6573.universe_of);
                 use_bv_sorts = (uu___150_6573.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___150_6573.proof_ns);
                 synth = (uu___150_6573.synth);
                 is_native_tactic = (uu___150_6573.is_native_tactic);
                 identifier_info = (uu___150_6573.identifier_info);
                 tc_hooks = (uu___150_6573.tc_hooks);
                 dsenv = (uu___150_6573.dsenv)
               }))
         | FStar_Pervasives_Native.Some (uu____6578,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___151_6586 = env in
               {
                 solver = (uu___151_6586.solver);
                 range = (uu___151_6586.range);
                 curmodule = (uu___151_6586.curmodule);
                 gamma = (uu___151_6586.gamma);
                 gamma_cache = (uu___151_6586.gamma_cache);
                 modules = (uu___151_6586.modules);
                 expected_typ = (uu___151_6586.expected_typ);
                 sigtab = (uu___151_6586.sigtab);
                 is_pattern = (uu___151_6586.is_pattern);
                 instantiate_imp = (uu___151_6586.instantiate_imp);
                 effects = (uu___151_6586.effects);
                 generalize = (uu___151_6586.generalize);
                 letrecs = (uu___151_6586.letrecs);
                 top_level = (uu___151_6586.top_level);
                 check_uvars = (uu___151_6586.check_uvars);
                 use_eq = (uu___151_6586.use_eq);
                 is_iface = (uu___151_6586.is_iface);
                 admit = (uu___151_6586.admit);
                 lax = (uu___151_6586.lax);
                 lax_universes = (uu___151_6586.lax_universes);
                 failhard = (uu___151_6586.failhard);
                 nosynth = (uu___151_6586.nosynth);
                 tc_term = (uu___151_6586.tc_term);
                 type_of = (uu___151_6586.type_of);
                 universe_of = (uu___151_6586.universe_of);
                 use_bv_sorts = (uu___151_6586.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___151_6586.proof_ns);
                 synth = (uu___151_6586.synth);
                 is_native_tactic = (uu___151_6586.is_native_tactic);
                 identifier_info = (uu___151_6586.identifier_info);
                 tc_hooks = (uu___151_6586.tc_hooks);
                 dsenv = (uu___151_6586.dsenv)
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
        (let uu___152_6608 = e in
         {
           solver = (uu___152_6608.solver);
           range = r;
           curmodule = (uu___152_6608.curmodule);
           gamma = (uu___152_6608.gamma);
           gamma_cache = (uu___152_6608.gamma_cache);
           modules = (uu___152_6608.modules);
           expected_typ = (uu___152_6608.expected_typ);
           sigtab = (uu___152_6608.sigtab);
           is_pattern = (uu___152_6608.is_pattern);
           instantiate_imp = (uu___152_6608.instantiate_imp);
           effects = (uu___152_6608.effects);
           generalize = (uu___152_6608.generalize);
           letrecs = (uu___152_6608.letrecs);
           top_level = (uu___152_6608.top_level);
           check_uvars = (uu___152_6608.check_uvars);
           use_eq = (uu___152_6608.use_eq);
           is_iface = (uu___152_6608.is_iface);
           admit = (uu___152_6608.admit);
           lax = (uu___152_6608.lax);
           lax_universes = (uu___152_6608.lax_universes);
           failhard = (uu___152_6608.failhard);
           nosynth = (uu___152_6608.nosynth);
           tc_term = (uu___152_6608.tc_term);
           type_of = (uu___152_6608.type_of);
           universe_of = (uu___152_6608.universe_of);
           use_bv_sorts = (uu___152_6608.use_bv_sorts);
           qname_and_index = (uu___152_6608.qname_and_index);
           proof_ns = (uu___152_6608.proof_ns);
           synth = (uu___152_6608.synth);
           is_native_tactic = (uu___152_6608.is_native_tactic);
           identifier_info = (uu___152_6608.identifier_info);
           tc_hooks = (uu___152_6608.tc_hooks);
           dsenv = (uu___152_6608.dsenv)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6621 =
        let uu____6622 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6622 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6621
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6727 =
          let uu____6728 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6728 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6727
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6833 =
          let uu____6834 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6834 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6833
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6940 =
        let uu____6941 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6941 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6940
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___153_7052 = env in
      {
        solver = (uu___153_7052.solver);
        range = (uu___153_7052.range);
        curmodule = lid;
        gamma = (uu___153_7052.gamma);
        gamma_cache = (uu___153_7052.gamma_cache);
        modules = (uu___153_7052.modules);
        expected_typ = (uu___153_7052.expected_typ);
        sigtab = (uu___153_7052.sigtab);
        is_pattern = (uu___153_7052.is_pattern);
        instantiate_imp = (uu___153_7052.instantiate_imp);
        effects = (uu___153_7052.effects);
        generalize = (uu___153_7052.generalize);
        letrecs = (uu___153_7052.letrecs);
        top_level = (uu___153_7052.top_level);
        check_uvars = (uu___153_7052.check_uvars);
        use_eq = (uu___153_7052.use_eq);
        is_iface = (uu___153_7052.is_iface);
        admit = (uu___153_7052.admit);
        lax = (uu___153_7052.lax);
        lax_universes = (uu___153_7052.lax_universes);
        failhard = (uu___153_7052.failhard);
        nosynth = (uu___153_7052.nosynth);
        tc_term = (uu___153_7052.tc_term);
        type_of = (uu___153_7052.type_of);
        universe_of = (uu___153_7052.universe_of);
        use_bv_sorts = (uu___153_7052.use_bv_sorts);
        qname_and_index = (uu___153_7052.qname_and_index);
        proof_ns = (uu___153_7052.proof_ns);
        synth = (uu___153_7052.synth);
        is_native_tactic = (uu___153_7052.is_native_tactic);
        identifier_info = (uu___153_7052.identifier_info);
        tc_hooks = (uu___153_7052.tc_hooks);
        dsenv = (uu___153_7052.dsenv)
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
    let uu____7083 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____7083
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7087  ->
    let uu____7088 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____7088
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
      | ((formals,t),uu____7128) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____7152 = FStar_Syntax_Subst.subst vs t in (us, uu____7152)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___134_7166  ->
    match uu___134_7166 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7190  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7205 = inst_tscheme t in
      match uu____7205 with
      | (us,t1) ->
          let uu____7216 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7216)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7232  ->
          match uu____7232 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7247 =
                         let uu____7248 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7249 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7250 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7251 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7248 uu____7249 uu____7250 uu____7251 in
                       failwith uu____7247)
                    else ();
                    (let uu____7253 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7253))
               | uu____7260 ->
                   let uu____7261 =
                     let uu____7262 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7262 in
                   failwith uu____7261)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7267 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7272 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7277 -> false
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
             | ([],uu____7313) -> Maybe
             | (uu____7320,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7339 -> No in
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
          let uu____7446 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7446 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___135_7491  ->
                   match uu___135_7491 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7534 =
                           let uu____7553 =
                             let uu____7568 = inst_tscheme t in
                             FStar_Util.Inl uu____7568 in
                           (uu____7553, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7534
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7634,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7636);
                                     FStar_Syntax_Syntax.sigrng = uu____7637;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7638;
                                     FStar_Syntax_Syntax.sigmeta = uu____7639;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7640;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7660 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7660
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7706 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7713 -> cache t in
                       let uu____7714 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7714 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7789 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7789 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7875 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7955 = find_in_sigtab env lid in
         match uu____7955 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8054) ->
          add_sigelts env ses
      | uu____8063 ->
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
            | uu____8077 -> ()))
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
        (fun uu___136_8106  ->
           match uu___136_8106 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8124 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____8159,lb::[]),uu____8161) ->
          let uu____8174 =
            let uu____8183 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8192 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8183, uu____8192) in
          FStar_Pervasives_Native.Some uu____8174
      | FStar_Syntax_Syntax.Sig_let ((uu____8205,lbs),uu____8207) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8243 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8255 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8255
                   then
                     let uu____8266 =
                       let uu____8275 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8284 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8275, uu____8284) in
                     FStar_Pervasives_Native.Some uu____8266
                   else FStar_Pervasives_Native.None)
      | uu____8306 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8340 =
          let uu____8349 =
            let uu____8354 =
              let uu____8355 =
                let uu____8358 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8358 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8355) in
            inst_tscheme uu____8354 in
          (uu____8349, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8340
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8378,uu____8379) ->
        let uu____8384 =
          let uu____8393 =
            let uu____8398 =
              let uu____8399 =
                let uu____8402 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8402 in
              (us, uu____8399) in
            inst_tscheme uu____8398 in
          (uu____8393, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8384
    | uu____8419 -> FStar_Pervasives_Native.None
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
      let mapper uu____8479 =
        match uu____8479 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8575,uvs,t,uu____8578,uu____8579,uu____8580);
                    FStar_Syntax_Syntax.sigrng = uu____8581;
                    FStar_Syntax_Syntax.sigquals = uu____8582;
                    FStar_Syntax_Syntax.sigmeta = uu____8583;
                    FStar_Syntax_Syntax.sigattrs = uu____8584;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8605 =
                   let uu____8614 = inst_tscheme (uvs, t) in
                   (uu____8614, rng) in
                 FStar_Pervasives_Native.Some uu____8605
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8634;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8636;
                    FStar_Syntax_Syntax.sigattrs = uu____8637;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8654 =
                   let uu____8655 = in_cur_mod env l in uu____8655 = Yes in
                 if uu____8654
                 then
                   let uu____8666 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8666
                    then
                      let uu____8679 =
                        let uu____8688 = inst_tscheme (uvs, t) in
                        (uu____8688, rng) in
                      FStar_Pervasives_Native.Some uu____8679
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8715 =
                      let uu____8724 = inst_tscheme (uvs, t) in
                      (uu____8724, rng) in
                    FStar_Pervasives_Native.Some uu____8715)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8745,uu____8746);
                    FStar_Syntax_Syntax.sigrng = uu____8747;
                    FStar_Syntax_Syntax.sigquals = uu____8748;
                    FStar_Syntax_Syntax.sigmeta = uu____8749;
                    FStar_Syntax_Syntax.sigattrs = uu____8750;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8789 =
                        let uu____8798 = inst_tscheme (uvs, k) in
                        (uu____8798, rng) in
                      FStar_Pervasives_Native.Some uu____8789
                  | uu____8815 ->
                      let uu____8816 =
                        let uu____8825 =
                          let uu____8830 =
                            let uu____8831 =
                              let uu____8834 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8834 in
                            (uvs, uu____8831) in
                          inst_tscheme uu____8830 in
                        (uu____8825, rng) in
                      FStar_Pervasives_Native.Some uu____8816)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8855,uu____8856);
                    FStar_Syntax_Syntax.sigrng = uu____8857;
                    FStar_Syntax_Syntax.sigquals = uu____8858;
                    FStar_Syntax_Syntax.sigmeta = uu____8859;
                    FStar_Syntax_Syntax.sigattrs = uu____8860;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8900 =
                        let uu____8909 = inst_tscheme_with (uvs, k) us in
                        (uu____8909, rng) in
                      FStar_Pervasives_Native.Some uu____8900
                  | uu____8926 ->
                      let uu____8927 =
                        let uu____8936 =
                          let uu____8941 =
                            let uu____8942 =
                              let uu____8945 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8945 in
                            (uvs, uu____8942) in
                          inst_tscheme_with uu____8941 us in
                        (uu____8936, rng) in
                      FStar_Pervasives_Native.Some uu____8927)
             | FStar_Util.Inr se ->
                 let uu____8979 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____9000;
                        FStar_Syntax_Syntax.sigrng = uu____9001;
                        FStar_Syntax_Syntax.sigquals = uu____9002;
                        FStar_Syntax_Syntax.sigmeta = uu____9003;
                        FStar_Syntax_Syntax.sigattrs = uu____9004;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____9019 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8979
                   (FStar_Util.map_option
                      (fun uu____9067  ->
                         match uu____9067 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____9098 =
        let uu____9109 = lookup_qname env lid in
        FStar_Util.bind_opt uu____9109 mapper in
      match uu____9098 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___154_9202 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___154_9202.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___154_9202.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9229 = lookup_qname env l in
      match uu____9229 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9268 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9318 = try_lookup_bv env bv in
      match uu____9318 with
      | FStar_Pervasives_Native.None  ->
          let uu____9333 =
            let uu____9334 =
              let uu____9339 = variable_not_found bv in (uu____9339, bvr) in
            FStar_Errors.Error uu____9334 in
          FStar_Exn.raise uu____9333
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9350 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9351 = FStar_Range.set_use_range r bvr in
          (uu____9350, uu____9351)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9370 = try_lookup_lid_aux env l in
      match uu____9370 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____9436 =
            let uu____9445 =
              let uu____9450 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____9450) in
            (uu____9445, r1) in
          FStar_Pervasives_Native.Some uu____9436
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9479 = try_lookup_lid env l in
      match uu____9479 with
      | FStar_Pervasives_Native.None  ->
          let uu____9506 =
            let uu____9507 =
              let uu____9512 = name_not_found l in
              (uu____9512, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9507 in
          FStar_Exn.raise uu____9506
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___137_9550  ->
              match uu___137_9550 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9552 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9569 = lookup_qname env lid in
      match uu____9569 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9598,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9601;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9603;
              FStar_Syntax_Syntax.sigattrs = uu____9604;_},FStar_Pervasives_Native.None
            ),uu____9605)
          ->
          let uu____9654 =
            let uu____9665 =
              let uu____9670 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9670) in
            (uu____9665, q) in
          FStar_Pervasives_Native.Some uu____9654
      | uu____9687 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9726 = lookup_qname env lid in
      match uu____9726 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9751,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9754;
              FStar_Syntax_Syntax.sigquals = uu____9755;
              FStar_Syntax_Syntax.sigmeta = uu____9756;
              FStar_Syntax_Syntax.sigattrs = uu____9757;_},FStar_Pervasives_Native.None
            ),uu____9758)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9807 ->
          let uu____9828 =
            let uu____9829 =
              let uu____9834 = name_not_found lid in
              (uu____9834, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9829 in
          FStar_Exn.raise uu____9828
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9851 = lookup_qname env lid in
      match uu____9851 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9876,uvs,t,uu____9879,uu____9880,uu____9881);
              FStar_Syntax_Syntax.sigrng = uu____9882;
              FStar_Syntax_Syntax.sigquals = uu____9883;
              FStar_Syntax_Syntax.sigmeta = uu____9884;
              FStar_Syntax_Syntax.sigattrs = uu____9885;_},FStar_Pervasives_Native.None
            ),uu____9886)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9939 ->
          let uu____9960 =
            let uu____9961 =
              let uu____9966 = name_not_found lid in
              (uu____9966, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9961 in
          FStar_Exn.raise uu____9960
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9985 = lookup_qname env lid in
      match uu____9985 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10012,uu____10013,uu____10014,uu____10015,uu____10016,dcs);
              FStar_Syntax_Syntax.sigrng = uu____10018;
              FStar_Syntax_Syntax.sigquals = uu____10019;
              FStar_Syntax_Syntax.sigmeta = uu____10020;
              FStar_Syntax_Syntax.sigattrs = uu____10021;_},uu____10022),uu____10023)
          -> (true, dcs)
      | uu____10084 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____10115 = lookup_qname env lid in
      match uu____10115 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10136,uu____10137,uu____10138,l,uu____10140,uu____10141);
              FStar_Syntax_Syntax.sigrng = uu____10142;
              FStar_Syntax_Syntax.sigquals = uu____10143;
              FStar_Syntax_Syntax.sigmeta = uu____10144;
              FStar_Syntax_Syntax.sigattrs = uu____10145;_},uu____10146),uu____10147)
          -> l
      | uu____10202 ->
          let uu____10223 =
            let uu____10224 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10224 in
          failwith uu____10223
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
        let uu____10261 = lookup_qname env lid in
        match uu____10261 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10289)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10340,lbs),uu____10342)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10370 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10370
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10402 -> FStar_Pervasives_Native.None)
        | uu____10407 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10444 = lookup_qname env ftv in
      match uu____10444 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10468) ->
          let uu____10513 = effect_signature se in
          (match uu____10513 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10534,t),r) ->
               let uu____10549 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10549)
      | uu____10550 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10579 = try_lookup_effect_lid env ftv in
      match uu____10579 with
      | FStar_Pervasives_Native.None  ->
          let uu____10582 =
            let uu____10583 =
              let uu____10588 = name_not_found ftv in
              (uu____10588, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10583 in
          FStar_Exn.raise uu____10582
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
        let uu____10608 = lookup_qname env lid0 in
        match uu____10608 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10639);
                FStar_Syntax_Syntax.sigrng = uu____10640;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10642;
                FStar_Syntax_Syntax.sigattrs = uu____10643;_},FStar_Pervasives_Native.None
              ),uu____10644)
            ->
            let lid1 =
              let uu____10698 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____10698 in
            let uu____10699 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___138_10703  ->
                      match uu___138_10703 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10704 -> false)) in
            if uu____10699
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10718 =
                      let uu____10719 =
                        let uu____10720 = get_range env in
                        FStar_Range.string_of_range uu____10720 in
                      let uu____10721 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10722 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10719 uu____10721 uu____10722 in
                    failwith uu____10718) in
               match (binders, univs1) with
               | ([],uu____10729) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10746,uu____10747::uu____10748::uu____10749) ->
                   let uu____10754 =
                     let uu____10755 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10756 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10755 uu____10756 in
                   failwith uu____10754
               | uu____10763 ->
                   let uu____10768 =
                     let uu____10773 =
                       let uu____10774 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10774) in
                     inst_tscheme_with uu____10773 insts in
                   (match uu____10768 with
                    | (uu____10785,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10788 =
                          let uu____10789 = FStar_Syntax_Subst.compress t1 in
                          uu____10789.FStar_Syntax_Syntax.n in
                        (match uu____10788 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10836 -> failwith "Impossible")))
        | uu____10843 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10885 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10885 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10898,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10905 = find1 l2 in
            (match uu____10905 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10912 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10912 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10916 = find1 l in
            (match uu____10916 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10932 = lookup_qname env l1 in
      match uu____10932 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10955;
              FStar_Syntax_Syntax.sigrng = uu____10956;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10958;
              FStar_Syntax_Syntax.sigattrs = uu____10959;_},uu____10960),uu____10961)
          -> q
      | uu____11012 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____11048 =
          let uu____11049 =
            let uu____11050 = FStar_Util.string_of_int i in
            let uu____11051 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____11050 uu____11051 in
          failwith uu____11049 in
        let uu____11052 = lookup_datacon env lid in
        match uu____11052 with
        | (uu____11057,t) ->
            let uu____11059 =
              let uu____11060 = FStar_Syntax_Subst.compress t in
              uu____11060.FStar_Syntax_Syntax.n in
            (match uu____11059 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11064) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____11095 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____11095
                      FStar_Pervasives_Native.fst)
             | uu____11104 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11113 = lookup_qname env l in
      match uu____11113 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11134,uu____11135,uu____11136);
              FStar_Syntax_Syntax.sigrng = uu____11137;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11139;
              FStar_Syntax_Syntax.sigattrs = uu____11140;_},uu____11141),uu____11142)
          ->
          FStar_Util.for_some
            (fun uu___139_11195  ->
               match uu___139_11195 with
               | FStar_Syntax_Syntax.Projector uu____11196 -> true
               | uu____11201 -> false) quals
      | uu____11202 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11231 = lookup_qname env lid in
      match uu____11231 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11252,uu____11253,uu____11254,uu____11255,uu____11256,uu____11257);
              FStar_Syntax_Syntax.sigrng = uu____11258;
              FStar_Syntax_Syntax.sigquals = uu____11259;
              FStar_Syntax_Syntax.sigmeta = uu____11260;
              FStar_Syntax_Syntax.sigattrs = uu____11261;_},uu____11262),uu____11263)
          -> true
      | uu____11318 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11347 = lookup_qname env lid in
      match uu____11347 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11368,uu____11369,uu____11370,uu____11371,uu____11372,uu____11373);
              FStar_Syntax_Syntax.sigrng = uu____11374;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11376;
              FStar_Syntax_Syntax.sigattrs = uu____11377;_},uu____11378),uu____11379)
          ->
          FStar_Util.for_some
            (fun uu___140_11440  ->
               match uu___140_11440 with
               | FStar_Syntax_Syntax.RecordType uu____11441 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11450 -> true
               | uu____11459 -> false) quals
      | uu____11460 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11489 = lookup_qname env lid in
      match uu____11489 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11510,uu____11511);
              FStar_Syntax_Syntax.sigrng = uu____11512;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11514;
              FStar_Syntax_Syntax.sigattrs = uu____11515;_},uu____11516),uu____11517)
          ->
          FStar_Util.for_some
            (fun uu___141_11574  ->
               match uu___141_11574 with
               | FStar_Syntax_Syntax.Action uu____11575 -> true
               | uu____11576 -> false) quals
      | uu____11577 -> false
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
      let uu____11609 =
        let uu____11610 = FStar_Syntax_Util.un_uinst head1 in
        uu____11610.FStar_Syntax_Syntax.n in
      match uu____11609 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11614 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11681 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11697) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11714 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11721 ->
                 FStar_Pervasives_Native.Some true
             | uu____11738 -> FStar_Pervasives_Native.Some false) in
      let uu____11739 =
        let uu____11742 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11742 mapper in
      match uu____11739 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11790 = lookup_qname env lid in
      match uu____11790 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11811,uu____11812,tps,uu____11814,uu____11815,uu____11816);
              FStar_Syntax_Syntax.sigrng = uu____11817;
              FStar_Syntax_Syntax.sigquals = uu____11818;
              FStar_Syntax_Syntax.sigmeta = uu____11819;
              FStar_Syntax_Syntax.sigattrs = uu____11820;_},uu____11821),uu____11822)
          -> FStar_List.length tps
      | uu____11885 ->
          let uu____11906 =
            let uu____11907 =
              let uu____11912 = name_not_found lid in
              (uu____11912, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11907 in
          FStar_Exn.raise uu____11906
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
           (fun uu____11954  ->
              match uu____11954 with
              | (d,uu____11962) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11975 = effect_decl_opt env l in
      match uu____11975 with
      | FStar_Pervasives_Native.None  ->
          let uu____11990 =
            let uu____11991 =
              let uu____11996 = name_not_found l in
              (uu____11996, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11991 in
          FStar_Exn.raise uu____11990
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
            (let uu____12062 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____12115  ->
                       match uu____12115 with
                       | (m1,m2,uu____12128,uu____12129,uu____12130) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____12062 with
             | FStar_Pervasives_Native.None  ->
                 let uu____12147 =
                   let uu____12148 =
                     let uu____12153 =
                       let uu____12154 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____12155 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____12154
                         uu____12155 in
                     (uu____12153, (env.range)) in
                   FStar_Errors.Error uu____12148 in
                 FStar_Exn.raise uu____12147
             | FStar_Pervasives_Native.Some
                 (uu____12162,uu____12163,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____12206 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12206)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12233 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12259  ->
                match uu____12259 with
                | (d,uu____12265) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12233 with
      | FStar_Pervasives_Native.None  ->
          let uu____12276 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12276
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12289 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12289 with
           | (uu____12300,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12310)::(wp,uu____12312)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12348 -> failwith "Impossible"))
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
                 let uu____12397 = get_range env in
                 let uu____12398 =
                   let uu____12401 =
                     let uu____12402 =
                       let uu____12417 =
                         let uu____12420 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12420] in
                       (null_wp, uu____12417) in
                     FStar_Syntax_Syntax.Tm_app uu____12402 in
                   FStar_Syntax_Syntax.mk uu____12401 in
                 uu____12398 FStar_Pervasives_Native.None uu____12397 in
               let uu____12426 =
                 let uu____12427 =
                   let uu____12436 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12436] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12427;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12426)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___155_12447 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___155_12447.order);
              joins = (uu___155_12447.joins)
            } in
          let uu___156_12456 = env in
          {
            solver = (uu___156_12456.solver);
            range = (uu___156_12456.range);
            curmodule = (uu___156_12456.curmodule);
            gamma = (uu___156_12456.gamma);
            gamma_cache = (uu___156_12456.gamma_cache);
            modules = (uu___156_12456.modules);
            expected_typ = (uu___156_12456.expected_typ);
            sigtab = (uu___156_12456.sigtab);
            is_pattern = (uu___156_12456.is_pattern);
            instantiate_imp = (uu___156_12456.instantiate_imp);
            effects;
            generalize = (uu___156_12456.generalize);
            letrecs = (uu___156_12456.letrecs);
            top_level = (uu___156_12456.top_level);
            check_uvars = (uu___156_12456.check_uvars);
            use_eq = (uu___156_12456.use_eq);
            is_iface = (uu___156_12456.is_iface);
            admit = (uu___156_12456.admit);
            lax = (uu___156_12456.lax);
            lax_universes = (uu___156_12456.lax_universes);
            failhard = (uu___156_12456.failhard);
            nosynth = (uu___156_12456.nosynth);
            tc_term = (uu___156_12456.tc_term);
            type_of = (uu___156_12456.type_of);
            universe_of = (uu___156_12456.universe_of);
            use_bv_sorts = (uu___156_12456.use_bv_sorts);
            qname_and_index = (uu___156_12456.qname_and_index);
            proof_ns = (uu___156_12456.proof_ns);
            synth = (uu___156_12456.synth);
            is_native_tactic = (uu___156_12456.is_native_tactic);
            identifier_info = (uu___156_12456.identifier_info);
            tc_hooks = (uu___156_12456.tc_hooks);
            dsenv = (uu___156_12456.dsenv)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12473 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12473 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12563 = (e1.mlift).mlift_wp t wp in
                              let uu____12564 = l1 t wp e in
                              l2 t uu____12563 uu____12564))
                | uu____12565 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12604 = inst_tscheme lift_t in
            match uu____12604 with
            | (uu____12611,lift_t1) ->
                let uu____12613 =
                  let uu____12616 =
                    let uu____12617 =
                      let uu____12632 =
                        let uu____12635 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12636 =
                          let uu____12639 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12639] in
                        uu____12635 :: uu____12636 in
                      (lift_t1, uu____12632) in
                    FStar_Syntax_Syntax.Tm_app uu____12617 in
                  FStar_Syntax_Syntax.mk uu____12616 in
                uu____12613 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12680 = inst_tscheme lift_t in
            match uu____12680 with
            | (uu____12687,lift_t1) ->
                let uu____12689 =
                  let uu____12692 =
                    let uu____12693 =
                      let uu____12708 =
                        let uu____12711 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12712 =
                          let uu____12715 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12716 =
                            let uu____12719 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12719] in
                          uu____12715 :: uu____12716 in
                        uu____12711 :: uu____12712 in
                      (lift_t1, uu____12708) in
                    FStar_Syntax_Syntax.Tm_app uu____12693 in
                  FStar_Syntax_Syntax.mk uu____12692 in
                uu____12689 FStar_Pervasives_Native.None
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
              let uu____12757 =
                let uu____12758 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12758
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12757 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12762 =
              let uu____12763 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12763 in
            let uu____12764 =
              let uu____12765 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12783 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12783) in
              FStar_Util.dflt "none" uu____12765 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12762
              uu____12764 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12809  ->
                    match uu____12809 with
                    | (e,uu____12817) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12836 =
            match uu____12836 with
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
              let uu____12874 =
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
                                    (let uu____12895 =
                                       let uu____12904 =
                                         find_edge order1 (i, k) in
                                       let uu____12907 =
                                         find_edge order1 (k, j) in
                                       (uu____12904, uu____12907) in
                                     match uu____12895 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12922 =
                                           compose_edges e1 e2 in
                                         [uu____12922]
                                     | uu____12923 -> []))))) in
              FStar_List.append order1 uu____12874 in
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
                   let uu____12952 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12954 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12954
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12952
                   then
                     let uu____12959 =
                       let uu____12960 =
                         let uu____12965 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12966 = get_range env in
                         (uu____12965, uu____12966) in
                       FStar_Errors.Error uu____12960 in
                     FStar_Exn.raise uu____12959
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
                                            let uu____13091 =
                                              let uu____13100 =
                                                find_edge order2 (i, k) in
                                              let uu____13103 =
                                                find_edge order2 (j, k) in
                                              (uu____13100, uu____13103) in
                                            match uu____13091 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13145,uu____13146)
                                                     ->
                                                     let uu____13153 =
                                                       let uu____13158 =
                                                         let uu____13159 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____13159 in
                                                       let uu____13162 =
                                                         let uu____13163 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____13163 in
                                                       (uu____13158,
                                                         uu____13162) in
                                                     (match uu____13153 with
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
                                            | uu____13198 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___157_13271 = env.effects in
              { decls = (uu___157_13271.decls); order = order2; joins } in
            let uu___158_13272 = env in
            {
              solver = (uu___158_13272.solver);
              range = (uu___158_13272.range);
              curmodule = (uu___158_13272.curmodule);
              gamma = (uu___158_13272.gamma);
              gamma_cache = (uu___158_13272.gamma_cache);
              modules = (uu___158_13272.modules);
              expected_typ = (uu___158_13272.expected_typ);
              sigtab = (uu___158_13272.sigtab);
              is_pattern = (uu___158_13272.is_pattern);
              instantiate_imp = (uu___158_13272.instantiate_imp);
              effects;
              generalize = (uu___158_13272.generalize);
              letrecs = (uu___158_13272.letrecs);
              top_level = (uu___158_13272.top_level);
              check_uvars = (uu___158_13272.check_uvars);
              use_eq = (uu___158_13272.use_eq);
              is_iface = (uu___158_13272.is_iface);
              admit = (uu___158_13272.admit);
              lax = (uu___158_13272.lax);
              lax_universes = (uu___158_13272.lax_universes);
              failhard = (uu___158_13272.failhard);
              nosynth = (uu___158_13272.nosynth);
              tc_term = (uu___158_13272.tc_term);
              type_of = (uu___158_13272.type_of);
              universe_of = (uu___158_13272.universe_of);
              use_bv_sorts = (uu___158_13272.use_bv_sorts);
              qname_and_index = (uu___158_13272.qname_and_index);
              proof_ns = (uu___158_13272.proof_ns);
              synth = (uu___158_13272.synth);
              is_native_tactic = (uu___158_13272.is_native_tactic);
              identifier_info = (uu___158_13272.identifier_info);
              tc_hooks = (uu___158_13272.tc_hooks);
              dsenv = (uu___158_13272.dsenv)
            }))
      | uu____13273 -> env
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
        | uu____13299 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13309 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13309 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13326 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13326 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13344 =
                     let uu____13345 =
                       let uu____13350 =
                         let uu____13351 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13356 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13363 =
                           let uu____13364 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13364 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13351 uu____13356 uu____13363 in
                       (uu____13350, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13345 in
                   FStar_Exn.raise uu____13344)
                else ();
                (let inst1 =
                   let uu____13369 =
                     let uu____13378 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13378 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13395  ->
                        fun uu____13396  ->
                          match (uu____13395, uu____13396) with
                          | ((x,uu____13418),(t,uu____13420)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13369 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13439 =
                     let uu___159_13440 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___159_13440.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___159_13440.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___159_13440.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___159_13440.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13439
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
          let uu____13466 = effect_decl_opt env effect_name in
          match uu____13466 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13499 =
                only_reifiable &&
                  (let uu____13501 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13501) in
              if uu____13499
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13517 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13536 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13565 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13565
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13566 =
                             let uu____13567 =
                               let uu____13572 = get_range env in
                               (message, uu____13572) in
                             FStar_Errors.Error uu____13567 in
                           FStar_Exn.raise uu____13566 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13582 =
                       let uu____13585 = get_range env in
                       let uu____13586 =
                         let uu____13589 =
                           let uu____13590 =
                             let uu____13605 =
                               let uu____13608 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13608; wp] in
                             (repr, uu____13605) in
                           FStar_Syntax_Syntax.Tm_app uu____13590 in
                         FStar_Syntax_Syntax.mk uu____13589 in
                       uu____13586 FStar_Pervasives_Native.None uu____13585 in
                     FStar_Pervasives_Native.Some uu____13582)
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
          let uu____13660 =
            let uu____13661 =
              let uu____13666 =
                let uu____13667 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13667 in
              let uu____13668 = get_range env in (uu____13666, uu____13668) in
            FStar_Errors.Error uu____13661 in
          FStar_Exn.raise uu____13660 in
        let uu____13669 = effect_repr_aux true env c u_c in
        match uu____13669 with
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
      | uu____13709 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13718 =
        let uu____13719 = FStar_Syntax_Subst.compress t in
        uu____13719.FStar_Syntax_Syntax.n in
      match uu____13718 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13722,c) ->
          is_reifiable_comp env c
      | uu____13740 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13764)::uu____13765 -> x :: rest
        | (Binding_sig_inst uu____13774)::uu____13775 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13790 = push1 x rest1 in local :: uu____13790 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___160_13794 = env in
       let uu____13795 = push1 s env.gamma in
       {
         solver = (uu___160_13794.solver);
         range = (uu___160_13794.range);
         curmodule = (uu___160_13794.curmodule);
         gamma = uu____13795;
         gamma_cache = (uu___160_13794.gamma_cache);
         modules = (uu___160_13794.modules);
         expected_typ = (uu___160_13794.expected_typ);
         sigtab = (uu___160_13794.sigtab);
         is_pattern = (uu___160_13794.is_pattern);
         instantiate_imp = (uu___160_13794.instantiate_imp);
         effects = (uu___160_13794.effects);
         generalize = (uu___160_13794.generalize);
         letrecs = (uu___160_13794.letrecs);
         top_level = (uu___160_13794.top_level);
         check_uvars = (uu___160_13794.check_uvars);
         use_eq = (uu___160_13794.use_eq);
         is_iface = (uu___160_13794.is_iface);
         admit = (uu___160_13794.admit);
         lax = (uu___160_13794.lax);
         lax_universes = (uu___160_13794.lax_universes);
         failhard = (uu___160_13794.failhard);
         nosynth = (uu___160_13794.nosynth);
         tc_term = (uu___160_13794.tc_term);
         type_of = (uu___160_13794.type_of);
         universe_of = (uu___160_13794.universe_of);
         use_bv_sorts = (uu___160_13794.use_bv_sorts);
         qname_and_index = (uu___160_13794.qname_and_index);
         proof_ns = (uu___160_13794.proof_ns);
         synth = (uu___160_13794.synth);
         is_native_tactic = (uu___160_13794.is_native_tactic);
         identifier_info = (uu___160_13794.identifier_info);
         tc_hooks = (uu___160_13794.tc_hooks);
         dsenv = (uu___160_13794.dsenv)
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
      let uu___161_13832 = env in
      {
        solver = (uu___161_13832.solver);
        range = (uu___161_13832.range);
        curmodule = (uu___161_13832.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___161_13832.gamma_cache);
        modules = (uu___161_13832.modules);
        expected_typ = (uu___161_13832.expected_typ);
        sigtab = (uu___161_13832.sigtab);
        is_pattern = (uu___161_13832.is_pattern);
        instantiate_imp = (uu___161_13832.instantiate_imp);
        effects = (uu___161_13832.effects);
        generalize = (uu___161_13832.generalize);
        letrecs = (uu___161_13832.letrecs);
        top_level = (uu___161_13832.top_level);
        check_uvars = (uu___161_13832.check_uvars);
        use_eq = (uu___161_13832.use_eq);
        is_iface = (uu___161_13832.is_iface);
        admit = (uu___161_13832.admit);
        lax = (uu___161_13832.lax);
        lax_universes = (uu___161_13832.lax_universes);
        failhard = (uu___161_13832.failhard);
        nosynth = (uu___161_13832.nosynth);
        tc_term = (uu___161_13832.tc_term);
        type_of = (uu___161_13832.type_of);
        universe_of = (uu___161_13832.universe_of);
        use_bv_sorts = (uu___161_13832.use_bv_sorts);
        qname_and_index = (uu___161_13832.qname_and_index);
        proof_ns = (uu___161_13832.proof_ns);
        synth = (uu___161_13832.synth);
        is_native_tactic = (uu___161_13832.is_native_tactic);
        identifier_info = (uu___161_13832.identifier_info);
        tc_hooks = (uu___161_13832.tc_hooks);
        dsenv = (uu___161_13832.dsenv)
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
            (let uu___162_13866 = env in
             {
               solver = (uu___162_13866.solver);
               range = (uu___162_13866.range);
               curmodule = (uu___162_13866.curmodule);
               gamma = rest;
               gamma_cache = (uu___162_13866.gamma_cache);
               modules = (uu___162_13866.modules);
               expected_typ = (uu___162_13866.expected_typ);
               sigtab = (uu___162_13866.sigtab);
               is_pattern = (uu___162_13866.is_pattern);
               instantiate_imp = (uu___162_13866.instantiate_imp);
               effects = (uu___162_13866.effects);
               generalize = (uu___162_13866.generalize);
               letrecs = (uu___162_13866.letrecs);
               top_level = (uu___162_13866.top_level);
               check_uvars = (uu___162_13866.check_uvars);
               use_eq = (uu___162_13866.use_eq);
               is_iface = (uu___162_13866.is_iface);
               admit = (uu___162_13866.admit);
               lax = (uu___162_13866.lax);
               lax_universes = (uu___162_13866.lax_universes);
               failhard = (uu___162_13866.failhard);
               nosynth = (uu___162_13866.nosynth);
               tc_term = (uu___162_13866.tc_term);
               type_of = (uu___162_13866.type_of);
               universe_of = (uu___162_13866.universe_of);
               use_bv_sorts = (uu___162_13866.use_bv_sorts);
               qname_and_index = (uu___162_13866.qname_and_index);
               proof_ns = (uu___162_13866.proof_ns);
               synth = (uu___162_13866.synth);
               is_native_tactic = (uu___162_13866.is_native_tactic);
               identifier_info = (uu___162_13866.identifier_info);
               tc_hooks = (uu___162_13866.tc_hooks);
               dsenv = (uu___162_13866.dsenv)
             }))
    | uu____13867 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13891  ->
             match uu____13891 with | (x,uu____13897) -> push_bv env1 x) env
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
            let uu___163_13927 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___163_13927.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___163_13927.FStar_Syntax_Syntax.index);
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
      (let uu___164_13962 = env in
       {
         solver = (uu___164_13962.solver);
         range = (uu___164_13962.range);
         curmodule = (uu___164_13962.curmodule);
         gamma = [];
         gamma_cache = (uu___164_13962.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___164_13962.sigtab);
         is_pattern = (uu___164_13962.is_pattern);
         instantiate_imp = (uu___164_13962.instantiate_imp);
         effects = (uu___164_13962.effects);
         generalize = (uu___164_13962.generalize);
         letrecs = (uu___164_13962.letrecs);
         top_level = (uu___164_13962.top_level);
         check_uvars = (uu___164_13962.check_uvars);
         use_eq = (uu___164_13962.use_eq);
         is_iface = (uu___164_13962.is_iface);
         admit = (uu___164_13962.admit);
         lax = (uu___164_13962.lax);
         lax_universes = (uu___164_13962.lax_universes);
         failhard = (uu___164_13962.failhard);
         nosynth = (uu___164_13962.nosynth);
         tc_term = (uu___164_13962.tc_term);
         type_of = (uu___164_13962.type_of);
         universe_of = (uu___164_13962.universe_of);
         use_bv_sorts = (uu___164_13962.use_bv_sorts);
         qname_and_index = (uu___164_13962.qname_and_index);
         proof_ns = (uu___164_13962.proof_ns);
         synth = (uu___164_13962.synth);
         is_native_tactic = (uu___164_13962.is_native_tactic);
         identifier_info = (uu___164_13962.identifier_info);
         tc_hooks = (uu___164_13962.tc_hooks);
         dsenv = (uu___164_13962.dsenv)
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
        let uu____13999 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13999 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____14027 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____14027)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___165_14042 = env in
      {
        solver = (uu___165_14042.solver);
        range = (uu___165_14042.range);
        curmodule = (uu___165_14042.curmodule);
        gamma = (uu___165_14042.gamma);
        gamma_cache = (uu___165_14042.gamma_cache);
        modules = (uu___165_14042.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___165_14042.sigtab);
        is_pattern = (uu___165_14042.is_pattern);
        instantiate_imp = (uu___165_14042.instantiate_imp);
        effects = (uu___165_14042.effects);
        generalize = (uu___165_14042.generalize);
        letrecs = (uu___165_14042.letrecs);
        top_level = (uu___165_14042.top_level);
        check_uvars = (uu___165_14042.check_uvars);
        use_eq = false;
        is_iface = (uu___165_14042.is_iface);
        admit = (uu___165_14042.admit);
        lax = (uu___165_14042.lax);
        lax_universes = (uu___165_14042.lax_universes);
        failhard = (uu___165_14042.failhard);
        nosynth = (uu___165_14042.nosynth);
        tc_term = (uu___165_14042.tc_term);
        type_of = (uu___165_14042.type_of);
        universe_of = (uu___165_14042.universe_of);
        use_bv_sorts = (uu___165_14042.use_bv_sorts);
        qname_and_index = (uu___165_14042.qname_and_index);
        proof_ns = (uu___165_14042.proof_ns);
        synth = (uu___165_14042.synth);
        is_native_tactic = (uu___165_14042.is_native_tactic);
        identifier_info = (uu___165_14042.identifier_info);
        tc_hooks = (uu___165_14042.tc_hooks);
        dsenv = (uu___165_14042.dsenv)
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
    let uu____14068 = expected_typ env_ in
    ((let uu___166_14074 = env_ in
      {
        solver = (uu___166_14074.solver);
        range = (uu___166_14074.range);
        curmodule = (uu___166_14074.curmodule);
        gamma = (uu___166_14074.gamma);
        gamma_cache = (uu___166_14074.gamma_cache);
        modules = (uu___166_14074.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___166_14074.sigtab);
        is_pattern = (uu___166_14074.is_pattern);
        instantiate_imp = (uu___166_14074.instantiate_imp);
        effects = (uu___166_14074.effects);
        generalize = (uu___166_14074.generalize);
        letrecs = (uu___166_14074.letrecs);
        top_level = (uu___166_14074.top_level);
        check_uvars = (uu___166_14074.check_uvars);
        use_eq = false;
        is_iface = (uu___166_14074.is_iface);
        admit = (uu___166_14074.admit);
        lax = (uu___166_14074.lax);
        lax_universes = (uu___166_14074.lax_universes);
        failhard = (uu___166_14074.failhard);
        nosynth = (uu___166_14074.nosynth);
        tc_term = (uu___166_14074.tc_term);
        type_of = (uu___166_14074.type_of);
        universe_of = (uu___166_14074.universe_of);
        use_bv_sorts = (uu___166_14074.use_bv_sorts);
        qname_and_index = (uu___166_14074.qname_and_index);
        proof_ns = (uu___166_14074.proof_ns);
        synth = (uu___166_14074.synth);
        is_native_tactic = (uu___166_14074.is_native_tactic);
        identifier_info = (uu___166_14074.identifier_info);
        tc_hooks = (uu___166_14074.tc_hooks);
        dsenv = (uu___166_14074.dsenv)
      }), uu____14068)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____14089 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___142_14099  ->
                    match uu___142_14099 with
                    | Binding_sig (uu____14102,se) -> [se]
                    | uu____14108 -> [])) in
          FStar_All.pipe_right uu____14089 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___167_14115 = env in
       {
         solver = (uu___167_14115.solver);
         range = (uu___167_14115.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___167_14115.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___167_14115.expected_typ);
         sigtab = (uu___167_14115.sigtab);
         is_pattern = (uu___167_14115.is_pattern);
         instantiate_imp = (uu___167_14115.instantiate_imp);
         effects = (uu___167_14115.effects);
         generalize = (uu___167_14115.generalize);
         letrecs = (uu___167_14115.letrecs);
         top_level = (uu___167_14115.top_level);
         check_uvars = (uu___167_14115.check_uvars);
         use_eq = (uu___167_14115.use_eq);
         is_iface = (uu___167_14115.is_iface);
         admit = (uu___167_14115.admit);
         lax = (uu___167_14115.lax);
         lax_universes = (uu___167_14115.lax_universes);
         failhard = (uu___167_14115.failhard);
         nosynth = (uu___167_14115.nosynth);
         tc_term = (uu___167_14115.tc_term);
         type_of = (uu___167_14115.type_of);
         universe_of = (uu___167_14115.universe_of);
         use_bv_sorts = (uu___167_14115.use_bv_sorts);
         qname_and_index = (uu___167_14115.qname_and_index);
         proof_ns = (uu___167_14115.proof_ns);
         synth = (uu___167_14115.synth);
         is_native_tactic = (uu___167_14115.is_native_tactic);
         identifier_info = (uu___167_14115.identifier_info);
         tc_hooks = (uu___167_14115.tc_hooks);
         dsenv = (uu___167_14115.dsenv)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14197)::tl1 -> aux out tl1
      | (Binding_lid (uu____14201,(uu____14202,t)))::tl1 ->
          let uu____14217 =
            let uu____14224 = FStar_Syntax_Free.uvars t in
            ext out uu____14224 in
          aux uu____14217 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14231;
            FStar_Syntax_Syntax.index = uu____14232;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14239 =
            let uu____14246 = FStar_Syntax_Free.uvars t in
            ext out uu____14246 in
          aux uu____14239 tl1
      | (Binding_sig uu____14253)::uu____14254 -> out
      | (Binding_sig_inst uu____14263)::uu____14264 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14320)::tl1 -> aux out tl1
      | (Binding_univ uu____14332)::tl1 -> aux out tl1
      | (Binding_lid (uu____14336,(uu____14337,t)))::tl1 ->
          let uu____14352 =
            let uu____14355 = FStar_Syntax_Free.univs t in
            ext out uu____14355 in
          aux uu____14352 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14358;
            FStar_Syntax_Syntax.index = uu____14359;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14366 =
            let uu____14369 = FStar_Syntax_Free.univs t in
            ext out uu____14369 in
          aux uu____14366 tl1
      | (Binding_sig uu____14372)::uu____14373 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14427)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14443 = FStar_Util.fifo_set_add uname out in
          aux uu____14443 tl1
      | (Binding_lid (uu____14446,(uu____14447,t)))::tl1 ->
          let uu____14462 =
            let uu____14465 = FStar_Syntax_Free.univnames t in
            ext out uu____14465 in
          aux uu____14462 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14468;
            FStar_Syntax_Syntax.index = uu____14469;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14476 =
            let uu____14479 = FStar_Syntax_Free.univnames t in
            ext out uu____14479 in
          aux uu____14476 tl1
      | (Binding_sig uu____14482)::uu____14483 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___143_14508  ->
            match uu___143_14508 with
            | Binding_var x -> [x]
            | Binding_lid uu____14512 -> []
            | Binding_sig uu____14517 -> []
            | Binding_univ uu____14524 -> []
            | Binding_sig_inst uu____14525 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14542 =
      let uu____14545 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14545
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14542 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14570 =
      let uu____14571 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___144_14581  ->
                match uu___144_14581 with
                | Binding_var x ->
                    let uu____14583 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14583
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14586) ->
                    let uu____14587 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14587
                | Binding_sig (ls,uu____14589) ->
                    let uu____14594 =
                      let uu____14595 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14595
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14594
                | Binding_sig_inst (ls,uu____14605,uu____14606) ->
                    let uu____14611 =
                      let uu____14612 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14612
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14611)) in
      FStar_All.pipe_right uu____14571 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14570 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14631 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14631
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14659  ->
                 fun uu____14660  ->
                   match (uu____14659, uu____14660) with
                   | ((b1,uu____14678),(b2,uu____14680)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___145_14727  ->
    match uu___145_14727 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14728 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___146_14747  ->
             match uu___146_14747 with
             | Binding_sig (lids,uu____14753) -> FStar_List.append lids keys
             | uu____14758 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14764  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14800) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14819,uu____14820) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____14857 = list_prefix p path1 in
            if uu____14857 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14871 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14871
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___168_14901 = e in
            {
              solver = (uu___168_14901.solver);
              range = (uu___168_14901.range);
              curmodule = (uu___168_14901.curmodule);
              gamma = (uu___168_14901.gamma);
              gamma_cache = (uu___168_14901.gamma_cache);
              modules = (uu___168_14901.modules);
              expected_typ = (uu___168_14901.expected_typ);
              sigtab = (uu___168_14901.sigtab);
              is_pattern = (uu___168_14901.is_pattern);
              instantiate_imp = (uu___168_14901.instantiate_imp);
              effects = (uu___168_14901.effects);
              generalize = (uu___168_14901.generalize);
              letrecs = (uu___168_14901.letrecs);
              top_level = (uu___168_14901.top_level);
              check_uvars = (uu___168_14901.check_uvars);
              use_eq = (uu___168_14901.use_eq);
              is_iface = (uu___168_14901.is_iface);
              admit = (uu___168_14901.admit);
              lax = (uu___168_14901.lax);
              lax_universes = (uu___168_14901.lax_universes);
              failhard = (uu___168_14901.failhard);
              nosynth = (uu___168_14901.nosynth);
              tc_term = (uu___168_14901.tc_term);
              type_of = (uu___168_14901.type_of);
              universe_of = (uu___168_14901.universe_of);
              use_bv_sorts = (uu___168_14901.use_bv_sorts);
              qname_and_index = (uu___168_14901.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___168_14901.synth);
              is_native_tactic = (uu___168_14901.is_native_tactic);
              identifier_info = (uu___168_14901.identifier_info);
              tc_hooks = (uu___168_14901.tc_hooks);
              dsenv = (uu___168_14901.dsenv)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___169_14928 = e in
    {
      solver = (uu___169_14928.solver);
      range = (uu___169_14928.range);
      curmodule = (uu___169_14928.curmodule);
      gamma = (uu___169_14928.gamma);
      gamma_cache = (uu___169_14928.gamma_cache);
      modules = (uu___169_14928.modules);
      expected_typ = (uu___169_14928.expected_typ);
      sigtab = (uu___169_14928.sigtab);
      is_pattern = (uu___169_14928.is_pattern);
      instantiate_imp = (uu___169_14928.instantiate_imp);
      effects = (uu___169_14928.effects);
      generalize = (uu___169_14928.generalize);
      letrecs = (uu___169_14928.letrecs);
      top_level = (uu___169_14928.top_level);
      check_uvars = (uu___169_14928.check_uvars);
      use_eq = (uu___169_14928.use_eq);
      is_iface = (uu___169_14928.is_iface);
      admit = (uu___169_14928.admit);
      lax = (uu___169_14928.lax);
      lax_universes = (uu___169_14928.lax_universes);
      failhard = (uu___169_14928.failhard);
      nosynth = (uu___169_14928.nosynth);
      tc_term = (uu___169_14928.tc_term);
      type_of = (uu___169_14928.type_of);
      universe_of = (uu___169_14928.universe_of);
      use_bv_sorts = (uu___169_14928.use_bv_sorts);
      qname_and_index = (uu___169_14928.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___169_14928.synth);
      is_native_tactic = (uu___169_14928.is_native_tactic);
      identifier_info = (uu___169_14928.identifier_info);
      tc_hooks = (uu___169_14928.tc_hooks);
      dsenv = (uu___169_14928.dsenv)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14943::rest ->
        let uu___170_14947 = e in
        {
          solver = (uu___170_14947.solver);
          range = (uu___170_14947.range);
          curmodule = (uu___170_14947.curmodule);
          gamma = (uu___170_14947.gamma);
          gamma_cache = (uu___170_14947.gamma_cache);
          modules = (uu___170_14947.modules);
          expected_typ = (uu___170_14947.expected_typ);
          sigtab = (uu___170_14947.sigtab);
          is_pattern = (uu___170_14947.is_pattern);
          instantiate_imp = (uu___170_14947.instantiate_imp);
          effects = (uu___170_14947.effects);
          generalize = (uu___170_14947.generalize);
          letrecs = (uu___170_14947.letrecs);
          top_level = (uu___170_14947.top_level);
          check_uvars = (uu___170_14947.check_uvars);
          use_eq = (uu___170_14947.use_eq);
          is_iface = (uu___170_14947.is_iface);
          admit = (uu___170_14947.admit);
          lax = (uu___170_14947.lax);
          lax_universes = (uu___170_14947.lax_universes);
          failhard = (uu___170_14947.failhard);
          nosynth = (uu___170_14947.nosynth);
          tc_term = (uu___170_14947.tc_term);
          type_of = (uu___170_14947.type_of);
          universe_of = (uu___170_14947.universe_of);
          use_bv_sorts = (uu___170_14947.use_bv_sorts);
          qname_and_index = (uu___170_14947.qname_and_index);
          proof_ns = rest;
          synth = (uu___170_14947.synth);
          is_native_tactic = (uu___170_14947.is_native_tactic);
          identifier_info = (uu___170_14947.identifier_info);
          tc_hooks = (uu___170_14947.tc_hooks);
          dsenv = (uu___170_14947.dsenv)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___171_14960 = e in
      {
        solver = (uu___171_14960.solver);
        range = (uu___171_14960.range);
        curmodule = (uu___171_14960.curmodule);
        gamma = (uu___171_14960.gamma);
        gamma_cache = (uu___171_14960.gamma_cache);
        modules = (uu___171_14960.modules);
        expected_typ = (uu___171_14960.expected_typ);
        sigtab = (uu___171_14960.sigtab);
        is_pattern = (uu___171_14960.is_pattern);
        instantiate_imp = (uu___171_14960.instantiate_imp);
        effects = (uu___171_14960.effects);
        generalize = (uu___171_14960.generalize);
        letrecs = (uu___171_14960.letrecs);
        top_level = (uu___171_14960.top_level);
        check_uvars = (uu___171_14960.check_uvars);
        use_eq = (uu___171_14960.use_eq);
        is_iface = (uu___171_14960.is_iface);
        admit = (uu___171_14960.admit);
        lax = (uu___171_14960.lax);
        lax_universes = (uu___171_14960.lax_universes);
        failhard = (uu___171_14960.failhard);
        nosynth = (uu___171_14960.nosynth);
        tc_term = (uu___171_14960.tc_term);
        type_of = (uu___171_14960.type_of);
        universe_of = (uu___171_14960.universe_of);
        use_bv_sorts = (uu___171_14960.use_bv_sorts);
        qname_and_index = (uu___171_14960.qname_and_index);
        proof_ns = ns;
        synth = (uu___171_14960.synth);
        is_native_tactic = (uu___171_14960.is_native_tactic);
        identifier_info = (uu___171_14960.identifier_info);
        tc_hooks = (uu___171_14960.tc_hooks);
        dsenv = (uu___171_14960.dsenv)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14989 =
        FStar_List.map
          (fun fpns  ->
             let uu____15011 =
               let uu____15012 =
                 let uu____15013 =
                   FStar_List.map
                     (fun uu____15025  ->
                        match uu____15025 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____15013 in
               Prims.strcat uu____15012 "]" in
             Prims.strcat "[" uu____15011) pns in
      FStar_String.concat ";" uu____14989 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____15041  -> ());
    push = (fun uu____15043  -> ());
    pop = (fun uu____15045  -> ());
    encode_modul = (fun uu____15048  -> fun uu____15049  -> ());
    encode_sig = (fun uu____15052  -> fun uu____15053  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____15059 =
             let uu____15066 = FStar_Options.peek () in (e, g, uu____15066) in
           [uu____15059]);
    solve = (fun uu____15082  -> fun uu____15083  -> fun uu____15084  -> ());
    is_trivial = (fun uu____15091  -> fun uu____15092  -> false);
    finish = (fun uu____15094  -> ());
    refresh = (fun uu____15096  -> ())
  }