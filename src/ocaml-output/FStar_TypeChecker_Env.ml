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
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5036  -> fun uu____5037  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___144_5050 = env in
      {
        solver = (uu___144_5050.solver);
        range = (uu___144_5050.range);
        curmodule = (uu___144_5050.curmodule);
        gamma = (uu___144_5050.gamma);
        gamma_cache = (uu___144_5050.gamma_cache);
        modules = (uu___144_5050.modules);
        expected_typ = (uu___144_5050.expected_typ);
        sigtab = (uu___144_5050.sigtab);
        is_pattern = (uu___144_5050.is_pattern);
        instantiate_imp = (uu___144_5050.instantiate_imp);
        effects = (uu___144_5050.effects);
        generalize = (uu___144_5050.generalize);
        letrecs = (uu___144_5050.letrecs);
        top_level = (uu___144_5050.top_level);
        check_uvars = (uu___144_5050.check_uvars);
        use_eq = (uu___144_5050.use_eq);
        is_iface = (uu___144_5050.is_iface);
        admit = (uu___144_5050.admit);
        lax = (uu___144_5050.lax);
        lax_universes = (uu___144_5050.lax_universes);
        failhard = (uu___144_5050.failhard);
        nosynth = (uu___144_5050.nosynth);
        tc_term = (uu___144_5050.tc_term);
        type_of = (uu___144_5050.type_of);
        universe_of = (uu___144_5050.universe_of);
        use_bv_sorts = (uu___144_5050.use_bv_sorts);
        qname_and_index = (uu___144_5050.qname_and_index);
        proof_ns = (uu___144_5050.proof_ns);
        synth = (uu___144_5050.synth);
        is_native_tactic = (uu___144_5050.is_native_tactic);
        identifier_info = (uu___144_5050.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___144_5050.dsenv)
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
      | (NoDelta ,uu____5065) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5066,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5067,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5068 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5077 . Prims.unit -> 'Auu____5077 FStar_Util.smap =
  fun uu____5083  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5088 . Prims.unit -> 'Auu____5088 FStar_Util.smap =
  fun uu____5094  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____5169 = new_gamma_cache () in
            let uu____5172 = new_sigtab () in
            let uu____5175 =
              let uu____5176 = FStar_Options.using_facts_from () in
              match uu____5176 with
              | FStar_Pervasives_Native.Some ns ->
                  let uu____5186 =
                    let uu____5195 =
                      FStar_List.map
                        (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                    FStar_List.append uu____5195 [([], false)] in
                  [uu____5186]
              | FStar_Pervasives_Native.None  -> [[]] in
            let uu____5268 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            let uu____5271 = FStar_ToSyntax_Env.empty_env () in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____5169;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____5172;
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
              proof_ns = uu____5175;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5303  -> false);
              identifier_info = uu____5268;
              tc_hooks = default_tc_hooks;
              dsenv = uu____5271
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
  fun uu____5374  ->
    let uu____5375 = FStar_ST.op_Bang query_indices in
    match uu____5375 with
    | [] -> failwith "Empty query indices!"
    | uu____5452 ->
        let uu____5461 =
          let uu____5470 =
            let uu____5477 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5477 in
          let uu____5554 = FStar_ST.op_Bang query_indices in uu____5470 ::
            uu____5554 in
        FStar_ST.op_Colon_Equals query_indices uu____5461
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5696  ->
    let uu____5697 = FStar_ST.op_Bang query_indices in
    match uu____5697 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5865  ->
    match uu____5865 with
    | (l,n1) ->
        let uu____5872 = FStar_ST.op_Bang query_indices in
        (match uu____5872 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____6037 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6055  ->
    let uu____6056 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____6056
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6151 =
       let uu____6154 = FStar_ST.op_Bang stack in env :: uu____6154 in
     FStar_ST.op_Colon_Equals stack uu____6151);
    (let uu___145_6257 = env in
     let uu____6258 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6261 = FStar_Util.smap_copy (sigtab env) in
     let uu____6264 =
       let uu____6267 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6267 in
     {
       solver = (uu___145_6257.solver);
       range = (uu___145_6257.range);
       curmodule = (uu___145_6257.curmodule);
       gamma = (uu___145_6257.gamma);
       gamma_cache = uu____6258;
       modules = (uu___145_6257.modules);
       expected_typ = (uu___145_6257.expected_typ);
       sigtab = uu____6261;
       is_pattern = (uu___145_6257.is_pattern);
       instantiate_imp = (uu___145_6257.instantiate_imp);
       effects = (uu___145_6257.effects);
       generalize = (uu___145_6257.generalize);
       letrecs = (uu___145_6257.letrecs);
       top_level = (uu___145_6257.top_level);
       check_uvars = (uu___145_6257.check_uvars);
       use_eq = (uu___145_6257.use_eq);
       is_iface = (uu___145_6257.is_iface);
       admit = (uu___145_6257.admit);
       lax = (uu___145_6257.lax);
       lax_universes = (uu___145_6257.lax_universes);
       failhard = (uu___145_6257.failhard);
       nosynth = (uu___145_6257.nosynth);
       tc_term = (uu___145_6257.tc_term);
       type_of = (uu___145_6257.type_of);
       universe_of = (uu___145_6257.universe_of);
       use_bv_sorts = (uu___145_6257.use_bv_sorts);
       qname_and_index = (uu___145_6257.qname_and_index);
       proof_ns = (uu___145_6257.proof_ns);
       synth = (uu___145_6257.synth);
       is_native_tactic = (uu___145_6257.is_native_tactic);
       identifier_info = uu____6264;
       tc_hooks = (uu___145_6257.tc_hooks);
       dsenv = (uu___145_6257.dsenv)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6331  ->
    let uu____6332 = FStar_ST.op_Bang stack in
    match uu____6332 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6440 -> failwith "Impossible: Too many pops"
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
        let uu____6488 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6514  ->
                  match uu____6514 with
                  | (m,uu____6520) -> FStar_Ident.lid_equals l m)) in
        (match uu____6488 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___146_6527 = env in
               {
                 solver = (uu___146_6527.solver);
                 range = (uu___146_6527.range);
                 curmodule = (uu___146_6527.curmodule);
                 gamma = (uu___146_6527.gamma);
                 gamma_cache = (uu___146_6527.gamma_cache);
                 modules = (uu___146_6527.modules);
                 expected_typ = (uu___146_6527.expected_typ);
                 sigtab = (uu___146_6527.sigtab);
                 is_pattern = (uu___146_6527.is_pattern);
                 instantiate_imp = (uu___146_6527.instantiate_imp);
                 effects = (uu___146_6527.effects);
                 generalize = (uu___146_6527.generalize);
                 letrecs = (uu___146_6527.letrecs);
                 top_level = (uu___146_6527.top_level);
                 check_uvars = (uu___146_6527.check_uvars);
                 use_eq = (uu___146_6527.use_eq);
                 is_iface = (uu___146_6527.is_iface);
                 admit = (uu___146_6527.admit);
                 lax = (uu___146_6527.lax);
                 lax_universes = (uu___146_6527.lax_universes);
                 failhard = (uu___146_6527.failhard);
                 nosynth = (uu___146_6527.nosynth);
                 tc_term = (uu___146_6527.tc_term);
                 type_of = (uu___146_6527.type_of);
                 universe_of = (uu___146_6527.universe_of);
                 use_bv_sorts = (uu___146_6527.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___146_6527.proof_ns);
                 synth = (uu___146_6527.synth);
                 is_native_tactic = (uu___146_6527.is_native_tactic);
                 identifier_info = (uu___146_6527.identifier_info);
                 tc_hooks = (uu___146_6527.tc_hooks);
                 dsenv = (uu___146_6527.dsenv)
               }))
         | FStar_Pervasives_Native.Some (uu____6532,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___147_6540 = env in
               {
                 solver = (uu___147_6540.solver);
                 range = (uu___147_6540.range);
                 curmodule = (uu___147_6540.curmodule);
                 gamma = (uu___147_6540.gamma);
                 gamma_cache = (uu___147_6540.gamma_cache);
                 modules = (uu___147_6540.modules);
                 expected_typ = (uu___147_6540.expected_typ);
                 sigtab = (uu___147_6540.sigtab);
                 is_pattern = (uu___147_6540.is_pattern);
                 instantiate_imp = (uu___147_6540.instantiate_imp);
                 effects = (uu___147_6540.effects);
                 generalize = (uu___147_6540.generalize);
                 letrecs = (uu___147_6540.letrecs);
                 top_level = (uu___147_6540.top_level);
                 check_uvars = (uu___147_6540.check_uvars);
                 use_eq = (uu___147_6540.use_eq);
                 is_iface = (uu___147_6540.is_iface);
                 admit = (uu___147_6540.admit);
                 lax = (uu___147_6540.lax);
                 lax_universes = (uu___147_6540.lax_universes);
                 failhard = (uu___147_6540.failhard);
                 nosynth = (uu___147_6540.nosynth);
                 tc_term = (uu___147_6540.tc_term);
                 type_of = (uu___147_6540.type_of);
                 universe_of = (uu___147_6540.universe_of);
                 use_bv_sorts = (uu___147_6540.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___147_6540.proof_ns);
                 synth = (uu___147_6540.synth);
                 is_native_tactic = (uu___147_6540.is_native_tactic);
                 identifier_info = (uu___147_6540.identifier_info);
                 tc_hooks = (uu___147_6540.tc_hooks);
                 dsenv = (uu___147_6540.dsenv)
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
        (let uu___148_6562 = e in
         {
           solver = (uu___148_6562.solver);
           range = r;
           curmodule = (uu___148_6562.curmodule);
           gamma = (uu___148_6562.gamma);
           gamma_cache = (uu___148_6562.gamma_cache);
           modules = (uu___148_6562.modules);
           expected_typ = (uu___148_6562.expected_typ);
           sigtab = (uu___148_6562.sigtab);
           is_pattern = (uu___148_6562.is_pattern);
           instantiate_imp = (uu___148_6562.instantiate_imp);
           effects = (uu___148_6562.effects);
           generalize = (uu___148_6562.generalize);
           letrecs = (uu___148_6562.letrecs);
           top_level = (uu___148_6562.top_level);
           check_uvars = (uu___148_6562.check_uvars);
           use_eq = (uu___148_6562.use_eq);
           is_iface = (uu___148_6562.is_iface);
           admit = (uu___148_6562.admit);
           lax = (uu___148_6562.lax);
           lax_universes = (uu___148_6562.lax_universes);
           failhard = (uu___148_6562.failhard);
           nosynth = (uu___148_6562.nosynth);
           tc_term = (uu___148_6562.tc_term);
           type_of = (uu___148_6562.type_of);
           universe_of = (uu___148_6562.universe_of);
           use_bv_sorts = (uu___148_6562.use_bv_sorts);
           qname_and_index = (uu___148_6562.qname_and_index);
           proof_ns = (uu___148_6562.proof_ns);
           synth = (uu___148_6562.synth);
           is_native_tactic = (uu___148_6562.is_native_tactic);
           identifier_info = (uu___148_6562.identifier_info);
           tc_hooks = (uu___148_6562.tc_hooks);
           dsenv = (uu___148_6562.dsenv)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6575 =
        let uu____6576 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6576 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6575
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6681 =
          let uu____6682 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6682 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6681
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6787 =
          let uu____6788 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6788 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6787
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6894 =
        let uu____6895 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6895 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6894
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___149_7006 = env in
      {
        solver = (uu___149_7006.solver);
        range = (uu___149_7006.range);
        curmodule = lid;
        gamma = (uu___149_7006.gamma);
        gamma_cache = (uu___149_7006.gamma_cache);
        modules = (uu___149_7006.modules);
        expected_typ = (uu___149_7006.expected_typ);
        sigtab = (uu___149_7006.sigtab);
        is_pattern = (uu___149_7006.is_pattern);
        instantiate_imp = (uu___149_7006.instantiate_imp);
        effects = (uu___149_7006.effects);
        generalize = (uu___149_7006.generalize);
        letrecs = (uu___149_7006.letrecs);
        top_level = (uu___149_7006.top_level);
        check_uvars = (uu___149_7006.check_uvars);
        use_eq = (uu___149_7006.use_eq);
        is_iface = (uu___149_7006.is_iface);
        admit = (uu___149_7006.admit);
        lax = (uu___149_7006.lax);
        lax_universes = (uu___149_7006.lax_universes);
        failhard = (uu___149_7006.failhard);
        nosynth = (uu___149_7006.nosynth);
        tc_term = (uu___149_7006.tc_term);
        type_of = (uu___149_7006.type_of);
        universe_of = (uu___149_7006.universe_of);
        use_bv_sorts = (uu___149_7006.use_bv_sorts);
        qname_and_index = (uu___149_7006.qname_and_index);
        proof_ns = (uu___149_7006.proof_ns);
        synth = (uu___149_7006.synth);
        is_native_tactic = (uu___149_7006.is_native_tactic);
        identifier_info = (uu___149_7006.identifier_info);
        tc_hooks = (uu___149_7006.tc_hooks);
        dsenv = (uu___149_7006.dsenv)
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
    let uu____7037 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____7037
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____7041  ->
    let uu____7042 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____7042
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
      | ((formals,t),uu____7082) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____7106 = FStar_Syntax_Subst.subst vs t in (us, uu____7106)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___131_7120  ->
    match uu___131_7120 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7144  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7159 = inst_tscheme t in
      match uu____7159 with
      | (us,t1) ->
          let uu____7170 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7170)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7186  ->
          match uu____7186 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7201 =
                         let uu____7202 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7203 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7204 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7205 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7202 uu____7203 uu____7204 uu____7205 in
                       failwith uu____7201)
                    else ();
                    (let uu____7207 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7207))
               | uu____7214 ->
                   let uu____7215 =
                     let uu____7216 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7216 in
                   failwith uu____7215)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7221 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7226 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7231 -> false
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
             | ([],uu____7267) -> Maybe
             | (uu____7274,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7293 -> No in
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
          let uu____7400 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7400 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___132_7445  ->
                   match uu___132_7445 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7488 =
                           let uu____7507 =
                             let uu____7522 = inst_tscheme t in
                             FStar_Util.Inl uu____7522 in
                           (uu____7507, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7488
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7588,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7590);
                                     FStar_Syntax_Syntax.sigrng = uu____7591;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7592;
                                     FStar_Syntax_Syntax.sigmeta = uu____7593;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7594;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7614 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7614
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7660 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7667 -> cache t in
                       let uu____7668 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7668 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7743 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7743 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7829 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7909 = find_in_sigtab env lid in
         match uu____7909 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____8008) ->
          add_sigelts env ses
      | uu____8017 ->
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
            | uu____8031 -> ()))
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
        (fun uu___133_8060  ->
           match uu___133_8060 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____8078 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____8113,lb::[]),uu____8115) ->
          let uu____8128 =
            let uu____8137 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8146 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8137, uu____8146) in
          FStar_Pervasives_Native.Some uu____8128
      | FStar_Syntax_Syntax.Sig_let ((uu____8159,lbs),uu____8161) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8197 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8209 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8209
                   then
                     let uu____8220 =
                       let uu____8229 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8238 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8229, uu____8238) in
                     FStar_Pervasives_Native.Some uu____8220
                   else FStar_Pervasives_Native.None)
      | uu____8260 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8294 =
          let uu____8303 =
            let uu____8308 =
              let uu____8309 =
                let uu____8312 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8312 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8309) in
            inst_tscheme uu____8308 in
          (uu____8303, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8294
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8332,uu____8333) ->
        let uu____8338 =
          let uu____8347 =
            let uu____8352 =
              let uu____8353 =
                let uu____8356 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8356 in
              (us, uu____8353) in
            inst_tscheme uu____8352 in
          (uu____8347, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8338
    | uu____8373 -> FStar_Pervasives_Native.None
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
      let mapper uu____8433 =
        match uu____8433 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8529,uvs,t,uu____8532,uu____8533,uu____8534);
                    FStar_Syntax_Syntax.sigrng = uu____8535;
                    FStar_Syntax_Syntax.sigquals = uu____8536;
                    FStar_Syntax_Syntax.sigmeta = uu____8537;
                    FStar_Syntax_Syntax.sigattrs = uu____8538;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8559 =
                   let uu____8568 = inst_tscheme (uvs, t) in
                   (uu____8568, rng) in
                 FStar_Pervasives_Native.Some uu____8559
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8588;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8590;
                    FStar_Syntax_Syntax.sigattrs = uu____8591;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8608 =
                   let uu____8609 = in_cur_mod env l in uu____8609 = Yes in
                 if uu____8608
                 then
                   let uu____8620 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8620
                    then
                      let uu____8633 =
                        let uu____8642 = inst_tscheme (uvs, t) in
                        (uu____8642, rng) in
                      FStar_Pervasives_Native.Some uu____8633
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8669 =
                      let uu____8678 = inst_tscheme (uvs, t) in
                      (uu____8678, rng) in
                    FStar_Pervasives_Native.Some uu____8669)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8699,uu____8700);
                    FStar_Syntax_Syntax.sigrng = uu____8701;
                    FStar_Syntax_Syntax.sigquals = uu____8702;
                    FStar_Syntax_Syntax.sigmeta = uu____8703;
                    FStar_Syntax_Syntax.sigattrs = uu____8704;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8743 =
                        let uu____8752 = inst_tscheme (uvs, k) in
                        (uu____8752, rng) in
                      FStar_Pervasives_Native.Some uu____8743
                  | uu____8769 ->
                      let uu____8770 =
                        let uu____8779 =
                          let uu____8784 =
                            let uu____8785 =
                              let uu____8788 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8788 in
                            (uvs, uu____8785) in
                          inst_tscheme uu____8784 in
                        (uu____8779, rng) in
                      FStar_Pervasives_Native.Some uu____8770)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8809,uu____8810);
                    FStar_Syntax_Syntax.sigrng = uu____8811;
                    FStar_Syntax_Syntax.sigquals = uu____8812;
                    FStar_Syntax_Syntax.sigmeta = uu____8813;
                    FStar_Syntax_Syntax.sigattrs = uu____8814;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8854 =
                        let uu____8863 = inst_tscheme_with (uvs, k) us in
                        (uu____8863, rng) in
                      FStar_Pervasives_Native.Some uu____8854
                  | uu____8880 ->
                      let uu____8881 =
                        let uu____8890 =
                          let uu____8895 =
                            let uu____8896 =
                              let uu____8899 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8899 in
                            (uvs, uu____8896) in
                          inst_tscheme_with uu____8895 us in
                        (uu____8890, rng) in
                      FStar_Pervasives_Native.Some uu____8881)
             | FStar_Util.Inr se ->
                 let uu____8933 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8954;
                        FStar_Syntax_Syntax.sigrng = uu____8955;
                        FStar_Syntax_Syntax.sigquals = uu____8956;
                        FStar_Syntax_Syntax.sigmeta = uu____8957;
                        FStar_Syntax_Syntax.sigattrs = uu____8958;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8973 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8933
                   (FStar_Util.map_option
                      (fun uu____9021  ->
                         match uu____9021 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____9052 =
        let uu____9063 = lookup_qname env lid in
        FStar_Util.bind_opt uu____9063 mapper in
      match uu____9052 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___150_9156 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___150_9156.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___150_9156.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9183 = lookup_qname env l in
      match uu____9183 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9222 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9272 = try_lookup_bv env bv in
      match uu____9272 with
      | FStar_Pervasives_Native.None  ->
          let uu____9287 =
            let uu____9288 =
              let uu____9293 = variable_not_found bv in (uu____9293, bvr) in
            FStar_Errors.Error uu____9288 in
          FStar_Exn.raise uu____9287
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9304 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9305 = FStar_Range.set_use_range r bvr in
          (uu____9304, uu____9305)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9324 = try_lookup_lid_aux env l in
      match uu____9324 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____9390 =
            let uu____9399 =
              let uu____9404 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____9404) in
            (uu____9399, r1) in
          FStar_Pervasives_Native.Some uu____9390
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9433 = try_lookup_lid env l in
      match uu____9433 with
      | FStar_Pervasives_Native.None  ->
          let uu____9460 =
            let uu____9461 =
              let uu____9466 = name_not_found l in
              (uu____9466, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9461 in
          FStar_Exn.raise uu____9460
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___134_9504  ->
              match uu___134_9504 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9506 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9523 = lookup_qname env lid in
      match uu____9523 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9552,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9555;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9557;
              FStar_Syntax_Syntax.sigattrs = uu____9558;_},FStar_Pervasives_Native.None
            ),uu____9559)
          ->
          let uu____9608 =
            let uu____9619 =
              let uu____9624 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9624) in
            (uu____9619, q) in
          FStar_Pervasives_Native.Some uu____9608
      | uu____9641 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9680 = lookup_qname env lid in
      match uu____9680 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9705,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9708;
              FStar_Syntax_Syntax.sigquals = uu____9709;
              FStar_Syntax_Syntax.sigmeta = uu____9710;
              FStar_Syntax_Syntax.sigattrs = uu____9711;_},FStar_Pervasives_Native.None
            ),uu____9712)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9761 ->
          let uu____9782 =
            let uu____9783 =
              let uu____9788 = name_not_found lid in
              (uu____9788, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9783 in
          FStar_Exn.raise uu____9782
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9805 = lookup_qname env lid in
      match uu____9805 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9830,uvs,t,uu____9833,uu____9834,uu____9835);
              FStar_Syntax_Syntax.sigrng = uu____9836;
              FStar_Syntax_Syntax.sigquals = uu____9837;
              FStar_Syntax_Syntax.sigmeta = uu____9838;
              FStar_Syntax_Syntax.sigattrs = uu____9839;_},FStar_Pervasives_Native.None
            ),uu____9840)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9893 ->
          let uu____9914 =
            let uu____9915 =
              let uu____9920 = name_not_found lid in
              (uu____9920, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9915 in
          FStar_Exn.raise uu____9914
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9939 = lookup_qname env lid in
      match uu____9939 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9966,uu____9967,uu____9968,uu____9969,uu____9970,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9972;
              FStar_Syntax_Syntax.sigquals = uu____9973;
              FStar_Syntax_Syntax.sigmeta = uu____9974;
              FStar_Syntax_Syntax.sigattrs = uu____9975;_},uu____9976),uu____9977)
          -> (true, dcs)
      | uu____10038 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____10069 = lookup_qname env lid in
      match uu____10069 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10090,uu____10091,uu____10092,l,uu____10094,uu____10095);
              FStar_Syntax_Syntax.sigrng = uu____10096;
              FStar_Syntax_Syntax.sigquals = uu____10097;
              FStar_Syntax_Syntax.sigmeta = uu____10098;
              FStar_Syntax_Syntax.sigattrs = uu____10099;_},uu____10100),uu____10101)
          -> l
      | uu____10156 ->
          let uu____10177 =
            let uu____10178 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10178 in
          failwith uu____10177
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
        let uu____10215 = lookup_qname env lid in
        match uu____10215 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10243)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10294,lbs),uu____10296)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10324 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10324
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10356 -> FStar_Pervasives_Native.None)
        | uu____10361 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10398 = lookup_qname env ftv in
      match uu____10398 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10422) ->
          let uu____10467 = effect_signature se in
          (match uu____10467 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10488,t),r) ->
               let uu____10503 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10503)
      | uu____10504 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10533 = try_lookup_effect_lid env ftv in
      match uu____10533 with
      | FStar_Pervasives_Native.None  ->
          let uu____10536 =
            let uu____10537 =
              let uu____10542 = name_not_found ftv in
              (uu____10542, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10537 in
          FStar_Exn.raise uu____10536
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
        let uu____10562 = lookup_qname env lid0 in
        match uu____10562 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10593);
                FStar_Syntax_Syntax.sigrng = uu____10594;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10596;
                FStar_Syntax_Syntax.sigattrs = uu____10597;_},FStar_Pervasives_Native.None
              ),uu____10598)
            ->
            let lid1 =
              let uu____10652 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____10652 in
            let uu____10653 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___135_10657  ->
                      match uu___135_10657 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10658 -> false)) in
            if uu____10653
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10672 =
                      let uu____10673 =
                        let uu____10674 = get_range env in
                        FStar_Range.string_of_range uu____10674 in
                      let uu____10675 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10676 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10673 uu____10675 uu____10676 in
                    failwith uu____10672) in
               match (binders, univs1) with
               | ([],uu____10683) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10700,uu____10701::uu____10702::uu____10703) ->
                   let uu____10708 =
                     let uu____10709 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10710 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10709 uu____10710 in
                   failwith uu____10708
               | uu____10717 ->
                   let uu____10722 =
                     let uu____10727 =
                       let uu____10728 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10728) in
                     inst_tscheme_with uu____10727 insts in
                   (match uu____10722 with
                    | (uu____10739,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10742 =
                          let uu____10743 = FStar_Syntax_Subst.compress t1 in
                          uu____10743.FStar_Syntax_Syntax.n in
                        (match uu____10742 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10790 -> failwith "Impossible")))
        | uu____10797 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10839 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10839 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10852,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10859 = find1 l2 in
            (match uu____10859 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10866 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10866 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10870 = find1 l in
            (match uu____10870 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10886 = lookup_qname env l1 in
      match uu____10886 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10909;
              FStar_Syntax_Syntax.sigrng = uu____10910;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10912;
              FStar_Syntax_Syntax.sigattrs = uu____10913;_},uu____10914),uu____10915)
          -> q
      | uu____10966 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____11002 =
          let uu____11003 =
            let uu____11004 = FStar_Util.string_of_int i in
            let uu____11005 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____11004 uu____11005 in
          failwith uu____11003 in
        let uu____11006 = lookup_datacon env lid in
        match uu____11006 with
        | (uu____11011,t) ->
            let uu____11013 =
              let uu____11014 = FStar_Syntax_Subst.compress t in
              uu____11014.FStar_Syntax_Syntax.n in
            (match uu____11013 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11018) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____11049 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____11049
                      FStar_Pervasives_Native.fst)
             | uu____11058 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____11067 = lookup_qname env l in
      match uu____11067 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11088,uu____11089,uu____11090);
              FStar_Syntax_Syntax.sigrng = uu____11091;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11093;
              FStar_Syntax_Syntax.sigattrs = uu____11094;_},uu____11095),uu____11096)
          ->
          FStar_Util.for_some
            (fun uu___136_11149  ->
               match uu___136_11149 with
               | FStar_Syntax_Syntax.Projector uu____11150 -> true
               | uu____11155 -> false) quals
      | uu____11156 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11185 = lookup_qname env lid in
      match uu____11185 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11206,uu____11207,uu____11208,uu____11209,uu____11210,uu____11211);
              FStar_Syntax_Syntax.sigrng = uu____11212;
              FStar_Syntax_Syntax.sigquals = uu____11213;
              FStar_Syntax_Syntax.sigmeta = uu____11214;
              FStar_Syntax_Syntax.sigattrs = uu____11215;_},uu____11216),uu____11217)
          -> true
      | uu____11272 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11301 = lookup_qname env lid in
      match uu____11301 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11322,uu____11323,uu____11324,uu____11325,uu____11326,uu____11327);
              FStar_Syntax_Syntax.sigrng = uu____11328;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11330;
              FStar_Syntax_Syntax.sigattrs = uu____11331;_},uu____11332),uu____11333)
          ->
          FStar_Util.for_some
            (fun uu___137_11394  ->
               match uu___137_11394 with
               | FStar_Syntax_Syntax.RecordType uu____11395 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11404 -> true
               | uu____11413 -> false) quals
      | uu____11414 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11443 = lookup_qname env lid in
      match uu____11443 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11464,uu____11465);
              FStar_Syntax_Syntax.sigrng = uu____11466;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11468;
              FStar_Syntax_Syntax.sigattrs = uu____11469;_},uu____11470),uu____11471)
          ->
          FStar_Util.for_some
            (fun uu___138_11528  ->
               match uu___138_11528 with
               | FStar_Syntax_Syntax.Action uu____11529 -> true
               | uu____11530 -> false) quals
      | uu____11531 -> false
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
      let uu____11563 =
        let uu____11564 = FStar_Syntax_Util.un_uinst head1 in
        uu____11564.FStar_Syntax_Syntax.n in
      match uu____11563 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11568 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11635 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11651) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11668 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11675 ->
                 FStar_Pervasives_Native.Some true
             | uu____11692 -> FStar_Pervasives_Native.Some false) in
      let uu____11693 =
        let uu____11696 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11696 mapper in
      match uu____11693 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11744 = lookup_qname env lid in
      match uu____11744 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11765,uu____11766,tps,uu____11768,uu____11769,uu____11770);
              FStar_Syntax_Syntax.sigrng = uu____11771;
              FStar_Syntax_Syntax.sigquals = uu____11772;
              FStar_Syntax_Syntax.sigmeta = uu____11773;
              FStar_Syntax_Syntax.sigattrs = uu____11774;_},uu____11775),uu____11776)
          -> FStar_List.length tps
      | uu____11839 ->
          let uu____11860 =
            let uu____11861 =
              let uu____11866 = name_not_found lid in
              (uu____11866, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11861 in
          FStar_Exn.raise uu____11860
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
           (fun uu____11908  ->
              match uu____11908 with
              | (d,uu____11916) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11929 = effect_decl_opt env l in
      match uu____11929 with
      | FStar_Pervasives_Native.None  ->
          let uu____11944 =
            let uu____11945 =
              let uu____11950 = name_not_found l in
              (uu____11950, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11945 in
          FStar_Exn.raise uu____11944
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
            (let uu____12016 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____12069  ->
                       match uu____12069 with
                       | (m1,m2,uu____12082,uu____12083,uu____12084) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____12016 with
             | FStar_Pervasives_Native.None  ->
                 let uu____12101 =
                   let uu____12102 =
                     let uu____12107 =
                       let uu____12108 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____12109 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____12108
                         uu____12109 in
                     (uu____12107, (env.range)) in
                   FStar_Errors.Error uu____12102 in
                 FStar_Exn.raise uu____12101
             | FStar_Pervasives_Native.Some
                 (uu____12116,uu____12117,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____12160 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12160)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12187 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12213  ->
                match uu____12213 with
                | (d,uu____12219) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12187 with
      | FStar_Pervasives_Native.None  ->
          let uu____12230 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12230
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12243 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12243 with
           | (uu____12254,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12264)::(wp,uu____12266)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12302 -> failwith "Impossible"))
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
                 let uu____12351 = get_range env in
                 let uu____12352 =
                   let uu____12355 =
                     let uu____12356 =
                       let uu____12371 =
                         let uu____12374 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12374] in
                       (null_wp, uu____12371) in
                     FStar_Syntax_Syntax.Tm_app uu____12356 in
                   FStar_Syntax_Syntax.mk uu____12355 in
                 uu____12352 FStar_Pervasives_Native.None uu____12351 in
               let uu____12380 =
                 let uu____12381 =
                   let uu____12390 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12390] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12381;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12380)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___151_12401 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___151_12401.order);
              joins = (uu___151_12401.joins)
            } in
          let uu___152_12410 = env in
          {
            solver = (uu___152_12410.solver);
            range = (uu___152_12410.range);
            curmodule = (uu___152_12410.curmodule);
            gamma = (uu___152_12410.gamma);
            gamma_cache = (uu___152_12410.gamma_cache);
            modules = (uu___152_12410.modules);
            expected_typ = (uu___152_12410.expected_typ);
            sigtab = (uu___152_12410.sigtab);
            is_pattern = (uu___152_12410.is_pattern);
            instantiate_imp = (uu___152_12410.instantiate_imp);
            effects;
            generalize = (uu___152_12410.generalize);
            letrecs = (uu___152_12410.letrecs);
            top_level = (uu___152_12410.top_level);
            check_uvars = (uu___152_12410.check_uvars);
            use_eq = (uu___152_12410.use_eq);
            is_iface = (uu___152_12410.is_iface);
            admit = (uu___152_12410.admit);
            lax = (uu___152_12410.lax);
            lax_universes = (uu___152_12410.lax_universes);
            failhard = (uu___152_12410.failhard);
            nosynth = (uu___152_12410.nosynth);
            tc_term = (uu___152_12410.tc_term);
            type_of = (uu___152_12410.type_of);
            universe_of = (uu___152_12410.universe_of);
            use_bv_sorts = (uu___152_12410.use_bv_sorts);
            qname_and_index = (uu___152_12410.qname_and_index);
            proof_ns = (uu___152_12410.proof_ns);
            synth = (uu___152_12410.synth);
            is_native_tactic = (uu___152_12410.is_native_tactic);
            identifier_info = (uu___152_12410.identifier_info);
            tc_hooks = (uu___152_12410.tc_hooks);
            dsenv = (uu___152_12410.dsenv)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12427 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12427 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12517 = (e1.mlift).mlift_wp t wp in
                              let uu____12518 = l1 t wp e in
                              l2 t uu____12517 uu____12518))
                | uu____12519 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12558 = inst_tscheme lift_t in
            match uu____12558 with
            | (uu____12565,lift_t1) ->
                let uu____12567 =
                  let uu____12570 =
                    let uu____12571 =
                      let uu____12586 =
                        let uu____12589 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12590 =
                          let uu____12593 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12593] in
                        uu____12589 :: uu____12590 in
                      (lift_t1, uu____12586) in
                    FStar_Syntax_Syntax.Tm_app uu____12571 in
                  FStar_Syntax_Syntax.mk uu____12570 in
                uu____12567 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12634 = inst_tscheme lift_t in
            match uu____12634 with
            | (uu____12641,lift_t1) ->
                let uu____12643 =
                  let uu____12646 =
                    let uu____12647 =
                      let uu____12662 =
                        let uu____12665 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12666 =
                          let uu____12669 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12670 =
                            let uu____12673 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12673] in
                          uu____12669 :: uu____12670 in
                        uu____12665 :: uu____12666 in
                      (lift_t1, uu____12662) in
                    FStar_Syntax_Syntax.Tm_app uu____12647 in
                  FStar_Syntax_Syntax.mk uu____12646 in
                uu____12643 FStar_Pervasives_Native.None
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
              let uu____12711 =
                let uu____12712 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12712
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12711 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12716 =
              let uu____12717 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12717 in
            let uu____12718 =
              let uu____12719 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12737 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12737) in
              FStar_Util.dflt "none" uu____12719 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12716
              uu____12718 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12763  ->
                    match uu____12763 with
                    | (e,uu____12771) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12790 =
            match uu____12790 with
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
              let uu____12828 =
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
                                    (let uu____12849 =
                                       let uu____12858 =
                                         find_edge order1 (i, k) in
                                       let uu____12861 =
                                         find_edge order1 (k, j) in
                                       (uu____12858, uu____12861) in
                                     match uu____12849 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12876 =
                                           compose_edges e1 e2 in
                                         [uu____12876]
                                     | uu____12877 -> []))))) in
              FStar_List.append order1 uu____12828 in
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
                   let uu____12906 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12908 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12908
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12906
                   then
                     let uu____12913 =
                       let uu____12914 =
                         let uu____12919 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12920 = get_range env in
                         (uu____12919, uu____12920) in
                       FStar_Errors.Error uu____12914 in
                     FStar_Exn.raise uu____12913
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
                                            let uu____13045 =
                                              let uu____13054 =
                                                find_edge order2 (i, k) in
                                              let uu____13057 =
                                                find_edge order2 (j, k) in
                                              (uu____13054, uu____13057) in
                                            match uu____13045 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____13099,uu____13100)
                                                     ->
                                                     let uu____13107 =
                                                       let uu____13112 =
                                                         let uu____13113 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____13113 in
                                                       let uu____13116 =
                                                         let uu____13117 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____13117 in
                                                       (uu____13112,
                                                         uu____13116) in
                                                     (match uu____13107 with
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
                                            | uu____13152 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___153_13225 = env.effects in
              { decls = (uu___153_13225.decls); order = order2; joins } in
            let uu___154_13226 = env in
            {
              solver = (uu___154_13226.solver);
              range = (uu___154_13226.range);
              curmodule = (uu___154_13226.curmodule);
              gamma = (uu___154_13226.gamma);
              gamma_cache = (uu___154_13226.gamma_cache);
              modules = (uu___154_13226.modules);
              expected_typ = (uu___154_13226.expected_typ);
              sigtab = (uu___154_13226.sigtab);
              is_pattern = (uu___154_13226.is_pattern);
              instantiate_imp = (uu___154_13226.instantiate_imp);
              effects;
              generalize = (uu___154_13226.generalize);
              letrecs = (uu___154_13226.letrecs);
              top_level = (uu___154_13226.top_level);
              check_uvars = (uu___154_13226.check_uvars);
              use_eq = (uu___154_13226.use_eq);
              is_iface = (uu___154_13226.is_iface);
              admit = (uu___154_13226.admit);
              lax = (uu___154_13226.lax);
              lax_universes = (uu___154_13226.lax_universes);
              failhard = (uu___154_13226.failhard);
              nosynth = (uu___154_13226.nosynth);
              tc_term = (uu___154_13226.tc_term);
              type_of = (uu___154_13226.type_of);
              universe_of = (uu___154_13226.universe_of);
              use_bv_sorts = (uu___154_13226.use_bv_sorts);
              qname_and_index = (uu___154_13226.qname_and_index);
              proof_ns = (uu___154_13226.proof_ns);
              synth = (uu___154_13226.synth);
              is_native_tactic = (uu___154_13226.is_native_tactic);
              identifier_info = (uu___154_13226.identifier_info);
              tc_hooks = (uu___154_13226.tc_hooks);
              dsenv = (uu___154_13226.dsenv)
            }))
      | uu____13227 -> env
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
        | uu____13253 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13263 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13263 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13280 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13280 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13298 =
                     let uu____13299 =
                       let uu____13304 =
                         let uu____13305 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13310 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13317 =
                           let uu____13318 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13318 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13305 uu____13310 uu____13317 in
                       (uu____13304, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13299 in
                   FStar_Exn.raise uu____13298)
                else ();
                (let inst1 =
                   let uu____13323 =
                     let uu____13332 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13332 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13349  ->
                        fun uu____13350  ->
                          match (uu____13349, uu____13350) with
                          | ((x,uu____13372),(t,uu____13374)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13323 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13393 =
                     let uu___155_13394 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___155_13394.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___155_13394.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___155_13394.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___155_13394.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13393
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
          let uu____13420 = effect_decl_opt env effect_name in
          match uu____13420 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13453 =
                only_reifiable &&
                  (let uu____13455 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13455) in
              if uu____13453
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13471 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13490 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13519 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13519
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13520 =
                             let uu____13521 =
                               let uu____13526 = get_range env in
                               (message, uu____13526) in
                             FStar_Errors.Error uu____13521 in
                           FStar_Exn.raise uu____13520 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13536 =
                       let uu____13539 = get_range env in
                       let uu____13540 =
                         let uu____13543 =
                           let uu____13544 =
                             let uu____13559 =
                               let uu____13562 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13562; wp] in
                             (repr, uu____13559) in
                           FStar_Syntax_Syntax.Tm_app uu____13544 in
                         FStar_Syntax_Syntax.mk uu____13543 in
                       uu____13540 FStar_Pervasives_Native.None uu____13539 in
                     FStar_Pervasives_Native.Some uu____13536)
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
          let uu____13614 =
            let uu____13615 =
              let uu____13620 =
                let uu____13621 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13621 in
              let uu____13622 = get_range env in (uu____13620, uu____13622) in
            FStar_Errors.Error uu____13615 in
          FStar_Exn.raise uu____13614 in
        let uu____13623 = effect_repr_aux true env c u_c in
        match uu____13623 with
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
      | uu____13663 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13672 =
        let uu____13673 = FStar_Syntax_Subst.compress t in
        uu____13673.FStar_Syntax_Syntax.n in
      match uu____13672 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13676,c) ->
          is_reifiable_comp env c
      | uu____13694 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13718)::uu____13719 -> x :: rest
        | (Binding_sig_inst uu____13728)::uu____13729 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13744 = push1 x rest1 in local :: uu____13744 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___156_13748 = env in
       let uu____13749 = push1 s env.gamma in
       {
         solver = (uu___156_13748.solver);
         range = (uu___156_13748.range);
         curmodule = (uu___156_13748.curmodule);
         gamma = uu____13749;
         gamma_cache = (uu___156_13748.gamma_cache);
         modules = (uu___156_13748.modules);
         expected_typ = (uu___156_13748.expected_typ);
         sigtab = (uu___156_13748.sigtab);
         is_pattern = (uu___156_13748.is_pattern);
         instantiate_imp = (uu___156_13748.instantiate_imp);
         effects = (uu___156_13748.effects);
         generalize = (uu___156_13748.generalize);
         letrecs = (uu___156_13748.letrecs);
         top_level = (uu___156_13748.top_level);
         check_uvars = (uu___156_13748.check_uvars);
         use_eq = (uu___156_13748.use_eq);
         is_iface = (uu___156_13748.is_iface);
         admit = (uu___156_13748.admit);
         lax = (uu___156_13748.lax);
         lax_universes = (uu___156_13748.lax_universes);
         failhard = (uu___156_13748.failhard);
         nosynth = (uu___156_13748.nosynth);
         tc_term = (uu___156_13748.tc_term);
         type_of = (uu___156_13748.type_of);
         universe_of = (uu___156_13748.universe_of);
         use_bv_sorts = (uu___156_13748.use_bv_sorts);
         qname_and_index = (uu___156_13748.qname_and_index);
         proof_ns = (uu___156_13748.proof_ns);
         synth = (uu___156_13748.synth);
         is_native_tactic = (uu___156_13748.is_native_tactic);
         identifier_info = (uu___156_13748.identifier_info);
         tc_hooks = (uu___156_13748.tc_hooks);
         dsenv = (uu___156_13748.dsenv)
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
      let uu___157_13786 = env in
      {
        solver = (uu___157_13786.solver);
        range = (uu___157_13786.range);
        curmodule = (uu___157_13786.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___157_13786.gamma_cache);
        modules = (uu___157_13786.modules);
        expected_typ = (uu___157_13786.expected_typ);
        sigtab = (uu___157_13786.sigtab);
        is_pattern = (uu___157_13786.is_pattern);
        instantiate_imp = (uu___157_13786.instantiate_imp);
        effects = (uu___157_13786.effects);
        generalize = (uu___157_13786.generalize);
        letrecs = (uu___157_13786.letrecs);
        top_level = (uu___157_13786.top_level);
        check_uvars = (uu___157_13786.check_uvars);
        use_eq = (uu___157_13786.use_eq);
        is_iface = (uu___157_13786.is_iface);
        admit = (uu___157_13786.admit);
        lax = (uu___157_13786.lax);
        lax_universes = (uu___157_13786.lax_universes);
        failhard = (uu___157_13786.failhard);
        nosynth = (uu___157_13786.nosynth);
        tc_term = (uu___157_13786.tc_term);
        type_of = (uu___157_13786.type_of);
        universe_of = (uu___157_13786.universe_of);
        use_bv_sorts = (uu___157_13786.use_bv_sorts);
        qname_and_index = (uu___157_13786.qname_and_index);
        proof_ns = (uu___157_13786.proof_ns);
        synth = (uu___157_13786.synth);
        is_native_tactic = (uu___157_13786.is_native_tactic);
        identifier_info = (uu___157_13786.identifier_info);
        tc_hooks = (uu___157_13786.tc_hooks);
        dsenv = (uu___157_13786.dsenv)
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
            (let uu___158_13820 = env in
             {
               solver = (uu___158_13820.solver);
               range = (uu___158_13820.range);
               curmodule = (uu___158_13820.curmodule);
               gamma = rest;
               gamma_cache = (uu___158_13820.gamma_cache);
               modules = (uu___158_13820.modules);
               expected_typ = (uu___158_13820.expected_typ);
               sigtab = (uu___158_13820.sigtab);
               is_pattern = (uu___158_13820.is_pattern);
               instantiate_imp = (uu___158_13820.instantiate_imp);
               effects = (uu___158_13820.effects);
               generalize = (uu___158_13820.generalize);
               letrecs = (uu___158_13820.letrecs);
               top_level = (uu___158_13820.top_level);
               check_uvars = (uu___158_13820.check_uvars);
               use_eq = (uu___158_13820.use_eq);
               is_iface = (uu___158_13820.is_iface);
               admit = (uu___158_13820.admit);
               lax = (uu___158_13820.lax);
               lax_universes = (uu___158_13820.lax_universes);
               failhard = (uu___158_13820.failhard);
               nosynth = (uu___158_13820.nosynth);
               tc_term = (uu___158_13820.tc_term);
               type_of = (uu___158_13820.type_of);
               universe_of = (uu___158_13820.universe_of);
               use_bv_sorts = (uu___158_13820.use_bv_sorts);
               qname_and_index = (uu___158_13820.qname_and_index);
               proof_ns = (uu___158_13820.proof_ns);
               synth = (uu___158_13820.synth);
               is_native_tactic = (uu___158_13820.is_native_tactic);
               identifier_info = (uu___158_13820.identifier_info);
               tc_hooks = (uu___158_13820.tc_hooks);
               dsenv = (uu___158_13820.dsenv)
             }))
    | uu____13821 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13845  ->
             match uu____13845 with | (x,uu____13851) -> push_bv env1 x) env
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
            let uu___159_13881 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___159_13881.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___159_13881.FStar_Syntax_Syntax.index);
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
      (let uu___160_13916 = env in
       {
         solver = (uu___160_13916.solver);
         range = (uu___160_13916.range);
         curmodule = (uu___160_13916.curmodule);
         gamma = [];
         gamma_cache = (uu___160_13916.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___160_13916.sigtab);
         is_pattern = (uu___160_13916.is_pattern);
         instantiate_imp = (uu___160_13916.instantiate_imp);
         effects = (uu___160_13916.effects);
         generalize = (uu___160_13916.generalize);
         letrecs = (uu___160_13916.letrecs);
         top_level = (uu___160_13916.top_level);
         check_uvars = (uu___160_13916.check_uvars);
         use_eq = (uu___160_13916.use_eq);
         is_iface = (uu___160_13916.is_iface);
         admit = (uu___160_13916.admit);
         lax = (uu___160_13916.lax);
         lax_universes = (uu___160_13916.lax_universes);
         failhard = (uu___160_13916.failhard);
         nosynth = (uu___160_13916.nosynth);
         tc_term = (uu___160_13916.tc_term);
         type_of = (uu___160_13916.type_of);
         universe_of = (uu___160_13916.universe_of);
         use_bv_sorts = (uu___160_13916.use_bv_sorts);
         qname_and_index = (uu___160_13916.qname_and_index);
         proof_ns = (uu___160_13916.proof_ns);
         synth = (uu___160_13916.synth);
         is_native_tactic = (uu___160_13916.is_native_tactic);
         identifier_info = (uu___160_13916.identifier_info);
         tc_hooks = (uu___160_13916.tc_hooks);
         dsenv = (uu___160_13916.dsenv)
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
        let uu____13953 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13953 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13981 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13981)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___161_13996 = env in
      {
        solver = (uu___161_13996.solver);
        range = (uu___161_13996.range);
        curmodule = (uu___161_13996.curmodule);
        gamma = (uu___161_13996.gamma);
        gamma_cache = (uu___161_13996.gamma_cache);
        modules = (uu___161_13996.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___161_13996.sigtab);
        is_pattern = (uu___161_13996.is_pattern);
        instantiate_imp = (uu___161_13996.instantiate_imp);
        effects = (uu___161_13996.effects);
        generalize = (uu___161_13996.generalize);
        letrecs = (uu___161_13996.letrecs);
        top_level = (uu___161_13996.top_level);
        check_uvars = (uu___161_13996.check_uvars);
        use_eq = false;
        is_iface = (uu___161_13996.is_iface);
        admit = (uu___161_13996.admit);
        lax = (uu___161_13996.lax);
        lax_universes = (uu___161_13996.lax_universes);
        failhard = (uu___161_13996.failhard);
        nosynth = (uu___161_13996.nosynth);
        tc_term = (uu___161_13996.tc_term);
        type_of = (uu___161_13996.type_of);
        universe_of = (uu___161_13996.universe_of);
        use_bv_sorts = (uu___161_13996.use_bv_sorts);
        qname_and_index = (uu___161_13996.qname_and_index);
        proof_ns = (uu___161_13996.proof_ns);
        synth = (uu___161_13996.synth);
        is_native_tactic = (uu___161_13996.is_native_tactic);
        identifier_info = (uu___161_13996.identifier_info);
        tc_hooks = (uu___161_13996.tc_hooks);
        dsenv = (uu___161_13996.dsenv)
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
    let uu____14022 = expected_typ env_ in
    ((let uu___162_14028 = env_ in
      {
        solver = (uu___162_14028.solver);
        range = (uu___162_14028.range);
        curmodule = (uu___162_14028.curmodule);
        gamma = (uu___162_14028.gamma);
        gamma_cache = (uu___162_14028.gamma_cache);
        modules = (uu___162_14028.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___162_14028.sigtab);
        is_pattern = (uu___162_14028.is_pattern);
        instantiate_imp = (uu___162_14028.instantiate_imp);
        effects = (uu___162_14028.effects);
        generalize = (uu___162_14028.generalize);
        letrecs = (uu___162_14028.letrecs);
        top_level = (uu___162_14028.top_level);
        check_uvars = (uu___162_14028.check_uvars);
        use_eq = false;
        is_iface = (uu___162_14028.is_iface);
        admit = (uu___162_14028.admit);
        lax = (uu___162_14028.lax);
        lax_universes = (uu___162_14028.lax_universes);
        failhard = (uu___162_14028.failhard);
        nosynth = (uu___162_14028.nosynth);
        tc_term = (uu___162_14028.tc_term);
        type_of = (uu___162_14028.type_of);
        universe_of = (uu___162_14028.universe_of);
        use_bv_sorts = (uu___162_14028.use_bv_sorts);
        qname_and_index = (uu___162_14028.qname_and_index);
        proof_ns = (uu___162_14028.proof_ns);
        synth = (uu___162_14028.synth);
        is_native_tactic = (uu___162_14028.is_native_tactic);
        identifier_info = (uu___162_14028.identifier_info);
        tc_hooks = (uu___162_14028.tc_hooks);
        dsenv = (uu___162_14028.dsenv)
      }), uu____14022)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____14043 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___139_14053  ->
                    match uu___139_14053 with
                    | Binding_sig (uu____14056,se) -> [se]
                    | uu____14062 -> [])) in
          FStar_All.pipe_right uu____14043 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___163_14069 = env in
       {
         solver = (uu___163_14069.solver);
         range = (uu___163_14069.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___163_14069.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___163_14069.expected_typ);
         sigtab = (uu___163_14069.sigtab);
         is_pattern = (uu___163_14069.is_pattern);
         instantiate_imp = (uu___163_14069.instantiate_imp);
         effects = (uu___163_14069.effects);
         generalize = (uu___163_14069.generalize);
         letrecs = (uu___163_14069.letrecs);
         top_level = (uu___163_14069.top_level);
         check_uvars = (uu___163_14069.check_uvars);
         use_eq = (uu___163_14069.use_eq);
         is_iface = (uu___163_14069.is_iface);
         admit = (uu___163_14069.admit);
         lax = (uu___163_14069.lax);
         lax_universes = (uu___163_14069.lax_universes);
         failhard = (uu___163_14069.failhard);
         nosynth = (uu___163_14069.nosynth);
         tc_term = (uu___163_14069.tc_term);
         type_of = (uu___163_14069.type_of);
         universe_of = (uu___163_14069.universe_of);
         use_bv_sorts = (uu___163_14069.use_bv_sorts);
         qname_and_index = (uu___163_14069.qname_and_index);
         proof_ns = (uu___163_14069.proof_ns);
         synth = (uu___163_14069.synth);
         is_native_tactic = (uu___163_14069.is_native_tactic);
         identifier_info = (uu___163_14069.identifier_info);
         tc_hooks = (uu___163_14069.tc_hooks);
         dsenv = (uu___163_14069.dsenv)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____14151)::tl1 -> aux out tl1
      | (Binding_lid (uu____14155,(uu____14156,t)))::tl1 ->
          let uu____14171 =
            let uu____14178 = FStar_Syntax_Free.uvars t in
            ext out uu____14178 in
          aux uu____14171 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14185;
            FStar_Syntax_Syntax.index = uu____14186;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14193 =
            let uu____14200 = FStar_Syntax_Free.uvars t in
            ext out uu____14200 in
          aux uu____14193 tl1
      | (Binding_sig uu____14207)::uu____14208 -> out
      | (Binding_sig_inst uu____14217)::uu____14218 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14274)::tl1 -> aux out tl1
      | (Binding_univ uu____14286)::tl1 -> aux out tl1
      | (Binding_lid (uu____14290,(uu____14291,t)))::tl1 ->
          let uu____14306 =
            let uu____14309 = FStar_Syntax_Free.univs t in
            ext out uu____14309 in
          aux uu____14306 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14312;
            FStar_Syntax_Syntax.index = uu____14313;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14320 =
            let uu____14323 = FStar_Syntax_Free.univs t in
            ext out uu____14323 in
          aux uu____14320 tl1
      | (Binding_sig uu____14326)::uu____14327 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14381)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14397 = FStar_Util.fifo_set_add uname out in
          aux uu____14397 tl1
      | (Binding_lid (uu____14400,(uu____14401,t)))::tl1 ->
          let uu____14416 =
            let uu____14419 = FStar_Syntax_Free.univnames t in
            ext out uu____14419 in
          aux uu____14416 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14422;
            FStar_Syntax_Syntax.index = uu____14423;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14430 =
            let uu____14433 = FStar_Syntax_Free.univnames t in
            ext out uu____14433 in
          aux uu____14430 tl1
      | (Binding_sig uu____14436)::uu____14437 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___140_14462  ->
            match uu___140_14462 with
            | Binding_var x -> [x]
            | Binding_lid uu____14466 -> []
            | Binding_sig uu____14471 -> []
            | Binding_univ uu____14478 -> []
            | Binding_sig_inst uu____14479 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14496 =
      let uu____14499 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14499
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14496 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14524 =
      let uu____14525 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___141_14535  ->
                match uu___141_14535 with
                | Binding_var x ->
                    let uu____14537 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14537
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14540) ->
                    let uu____14541 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14541
                | Binding_sig (ls,uu____14543) ->
                    let uu____14548 =
                      let uu____14549 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14549
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14548
                | Binding_sig_inst (ls,uu____14559,uu____14560) ->
                    let uu____14565 =
                      let uu____14566 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14566
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14565)) in
      FStar_All.pipe_right uu____14525 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14524 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14585 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14585
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14613  ->
                 fun uu____14614  ->
                   match (uu____14613, uu____14614) with
                   | ((b1,uu____14632),(b2,uu____14634)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___142_14681  ->
    match uu___142_14681 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14682 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___143_14701  ->
             match uu___143_14701 with
             | Binding_sig (lids,uu____14707) -> FStar_List.append lids keys
             | uu____14712 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14718  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14754) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14773,uu____14774) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____14811 = list_prefix p path1 in
            if uu____14811 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14825 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14825
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___164_14855 = e in
            {
              solver = (uu___164_14855.solver);
              range = (uu___164_14855.range);
              curmodule = (uu___164_14855.curmodule);
              gamma = (uu___164_14855.gamma);
              gamma_cache = (uu___164_14855.gamma_cache);
              modules = (uu___164_14855.modules);
              expected_typ = (uu___164_14855.expected_typ);
              sigtab = (uu___164_14855.sigtab);
              is_pattern = (uu___164_14855.is_pattern);
              instantiate_imp = (uu___164_14855.instantiate_imp);
              effects = (uu___164_14855.effects);
              generalize = (uu___164_14855.generalize);
              letrecs = (uu___164_14855.letrecs);
              top_level = (uu___164_14855.top_level);
              check_uvars = (uu___164_14855.check_uvars);
              use_eq = (uu___164_14855.use_eq);
              is_iface = (uu___164_14855.is_iface);
              admit = (uu___164_14855.admit);
              lax = (uu___164_14855.lax);
              lax_universes = (uu___164_14855.lax_universes);
              failhard = (uu___164_14855.failhard);
              nosynth = (uu___164_14855.nosynth);
              tc_term = (uu___164_14855.tc_term);
              type_of = (uu___164_14855.type_of);
              universe_of = (uu___164_14855.universe_of);
              use_bv_sorts = (uu___164_14855.use_bv_sorts);
              qname_and_index = (uu___164_14855.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___164_14855.synth);
              is_native_tactic = (uu___164_14855.is_native_tactic);
              identifier_info = (uu___164_14855.identifier_info);
              tc_hooks = (uu___164_14855.tc_hooks);
              dsenv = (uu___164_14855.dsenv)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___165_14882 = e in
    {
      solver = (uu___165_14882.solver);
      range = (uu___165_14882.range);
      curmodule = (uu___165_14882.curmodule);
      gamma = (uu___165_14882.gamma);
      gamma_cache = (uu___165_14882.gamma_cache);
      modules = (uu___165_14882.modules);
      expected_typ = (uu___165_14882.expected_typ);
      sigtab = (uu___165_14882.sigtab);
      is_pattern = (uu___165_14882.is_pattern);
      instantiate_imp = (uu___165_14882.instantiate_imp);
      effects = (uu___165_14882.effects);
      generalize = (uu___165_14882.generalize);
      letrecs = (uu___165_14882.letrecs);
      top_level = (uu___165_14882.top_level);
      check_uvars = (uu___165_14882.check_uvars);
      use_eq = (uu___165_14882.use_eq);
      is_iface = (uu___165_14882.is_iface);
      admit = (uu___165_14882.admit);
      lax = (uu___165_14882.lax);
      lax_universes = (uu___165_14882.lax_universes);
      failhard = (uu___165_14882.failhard);
      nosynth = (uu___165_14882.nosynth);
      tc_term = (uu___165_14882.tc_term);
      type_of = (uu___165_14882.type_of);
      universe_of = (uu___165_14882.universe_of);
      use_bv_sorts = (uu___165_14882.use_bv_sorts);
      qname_and_index = (uu___165_14882.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___165_14882.synth);
      is_native_tactic = (uu___165_14882.is_native_tactic);
      identifier_info = (uu___165_14882.identifier_info);
      tc_hooks = (uu___165_14882.tc_hooks);
      dsenv = (uu___165_14882.dsenv)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14897::rest ->
        let uu___166_14901 = e in
        {
          solver = (uu___166_14901.solver);
          range = (uu___166_14901.range);
          curmodule = (uu___166_14901.curmodule);
          gamma = (uu___166_14901.gamma);
          gamma_cache = (uu___166_14901.gamma_cache);
          modules = (uu___166_14901.modules);
          expected_typ = (uu___166_14901.expected_typ);
          sigtab = (uu___166_14901.sigtab);
          is_pattern = (uu___166_14901.is_pattern);
          instantiate_imp = (uu___166_14901.instantiate_imp);
          effects = (uu___166_14901.effects);
          generalize = (uu___166_14901.generalize);
          letrecs = (uu___166_14901.letrecs);
          top_level = (uu___166_14901.top_level);
          check_uvars = (uu___166_14901.check_uvars);
          use_eq = (uu___166_14901.use_eq);
          is_iface = (uu___166_14901.is_iface);
          admit = (uu___166_14901.admit);
          lax = (uu___166_14901.lax);
          lax_universes = (uu___166_14901.lax_universes);
          failhard = (uu___166_14901.failhard);
          nosynth = (uu___166_14901.nosynth);
          tc_term = (uu___166_14901.tc_term);
          type_of = (uu___166_14901.type_of);
          universe_of = (uu___166_14901.universe_of);
          use_bv_sorts = (uu___166_14901.use_bv_sorts);
          qname_and_index = (uu___166_14901.qname_and_index);
          proof_ns = rest;
          synth = (uu___166_14901.synth);
          is_native_tactic = (uu___166_14901.is_native_tactic);
          identifier_info = (uu___166_14901.identifier_info);
          tc_hooks = (uu___166_14901.tc_hooks);
          dsenv = (uu___166_14901.dsenv)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___167_14914 = e in
      {
        solver = (uu___167_14914.solver);
        range = (uu___167_14914.range);
        curmodule = (uu___167_14914.curmodule);
        gamma = (uu___167_14914.gamma);
        gamma_cache = (uu___167_14914.gamma_cache);
        modules = (uu___167_14914.modules);
        expected_typ = (uu___167_14914.expected_typ);
        sigtab = (uu___167_14914.sigtab);
        is_pattern = (uu___167_14914.is_pattern);
        instantiate_imp = (uu___167_14914.instantiate_imp);
        effects = (uu___167_14914.effects);
        generalize = (uu___167_14914.generalize);
        letrecs = (uu___167_14914.letrecs);
        top_level = (uu___167_14914.top_level);
        check_uvars = (uu___167_14914.check_uvars);
        use_eq = (uu___167_14914.use_eq);
        is_iface = (uu___167_14914.is_iface);
        admit = (uu___167_14914.admit);
        lax = (uu___167_14914.lax);
        lax_universes = (uu___167_14914.lax_universes);
        failhard = (uu___167_14914.failhard);
        nosynth = (uu___167_14914.nosynth);
        tc_term = (uu___167_14914.tc_term);
        type_of = (uu___167_14914.type_of);
        universe_of = (uu___167_14914.universe_of);
        use_bv_sorts = (uu___167_14914.use_bv_sorts);
        qname_and_index = (uu___167_14914.qname_and_index);
        proof_ns = ns;
        synth = (uu___167_14914.synth);
        is_native_tactic = (uu___167_14914.is_native_tactic);
        identifier_info = (uu___167_14914.identifier_info);
        tc_hooks = (uu___167_14914.tc_hooks);
        dsenv = (uu___167_14914.dsenv)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14943 =
        FStar_List.map
          (fun fpns  ->
             let uu____14965 =
               let uu____14966 =
                 let uu____14967 =
                   FStar_List.map
                     (fun uu____14979  ->
                        match uu____14979 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14967 in
               Prims.strcat uu____14966 "]" in
             Prims.strcat "[" uu____14965) pns in
      FStar_String.concat ";" uu____14943 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14995  -> ());
    push = (fun uu____14997  -> ());
    pop = (fun uu____14999  -> ());
    encode_modul = (fun uu____15002  -> fun uu____15003  -> ());
    encode_sig = (fun uu____15006  -> fun uu____15007  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____15013 =
             let uu____15020 = FStar_Options.peek () in (e, g, uu____15020) in
           [uu____15013]);
    solve = (fun uu____15036  -> fun uu____15037  -> fun uu____15038  -> ());
    is_trivial = (fun uu____15045  -> fun uu____15046  -> false);
    finish = (fun uu____15048  -> ());
    refresh = (fun uu____15050  -> ())
  }