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
           (fun uu___140_4932  ->
              match uu___140_4932 with
              | Binding_var x ->
                  let y =
                    let uu____4935 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____4935 in
                  let uu____4936 =
                    let uu____4937 = FStar_Syntax_Subst.compress y in
                    uu____4937.FStar_Syntax_Syntax.n in
                  (match uu____4936 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____4941 =
                         let uu___154_4942 = y1 in
                         let uu____4943 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___154_4942.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___154_4942.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____4943
                         } in
                       Binding_var uu____4941
                   | uu____4946 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___155_4956 = env in
      let uu____4957 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___155_4956.solver);
        range = (uu___155_4956.range);
        curmodule = (uu___155_4956.curmodule);
        gamma = uu____4957;
        gamma_cache = (uu___155_4956.gamma_cache);
        modules = (uu___155_4956.modules);
        expected_typ = (uu___155_4956.expected_typ);
        sigtab = (uu___155_4956.sigtab);
        is_pattern = (uu___155_4956.is_pattern);
        instantiate_imp = (uu___155_4956.instantiate_imp);
        effects = (uu___155_4956.effects);
        generalize = (uu___155_4956.generalize);
        letrecs = (uu___155_4956.letrecs);
        top_level = (uu___155_4956.top_level);
        check_uvars = (uu___155_4956.check_uvars);
        use_eq = (uu___155_4956.use_eq);
        is_iface = (uu___155_4956.is_iface);
        admit = (uu___155_4956.admit);
        lax = (uu___155_4956.lax);
        lax_universes = (uu___155_4956.lax_universes);
        failhard = (uu___155_4956.failhard);
        nosynth = (uu___155_4956.nosynth);
        tc_term = (uu___155_4956.tc_term);
        type_of = (uu___155_4956.type_of);
        universe_of = (uu___155_4956.universe_of);
        use_bv_sorts = (uu___155_4956.use_bv_sorts);
        qname_and_index = (uu___155_4956.qname_and_index);
        proof_ns = (uu___155_4956.proof_ns);
        synth = (uu___155_4956.synth);
        is_native_tactic = (uu___155_4956.is_native_tactic);
        identifier_info = (uu___155_4956.identifier_info);
        tc_hooks = (uu___155_4956.tc_hooks);
        dsenv = (uu___155_4956.dsenv)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4964  -> fun uu____4965  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___156_4978 = env in
      {
        solver = (uu___156_4978.solver);
        range = (uu___156_4978.range);
        curmodule = (uu___156_4978.curmodule);
        gamma = (uu___156_4978.gamma);
        gamma_cache = (uu___156_4978.gamma_cache);
        modules = (uu___156_4978.modules);
        expected_typ = (uu___156_4978.expected_typ);
        sigtab = (uu___156_4978.sigtab);
        is_pattern = (uu___156_4978.is_pattern);
        instantiate_imp = (uu___156_4978.instantiate_imp);
        effects = (uu___156_4978.effects);
        generalize = (uu___156_4978.generalize);
        letrecs = (uu___156_4978.letrecs);
        top_level = (uu___156_4978.top_level);
        check_uvars = (uu___156_4978.check_uvars);
        use_eq = (uu___156_4978.use_eq);
        is_iface = (uu___156_4978.is_iface);
        admit = (uu___156_4978.admit);
        lax = (uu___156_4978.lax);
        lax_universes = (uu___156_4978.lax_universes);
        failhard = (uu___156_4978.failhard);
        nosynth = (uu___156_4978.nosynth);
        tc_term = (uu___156_4978.tc_term);
        type_of = (uu___156_4978.type_of);
        universe_of = (uu___156_4978.universe_of);
        use_bv_sorts = (uu___156_4978.use_bv_sorts);
        qname_and_index = (uu___156_4978.qname_and_index);
        proof_ns = (uu___156_4978.proof_ns);
        synth = (uu___156_4978.synth);
        is_native_tactic = (uu___156_4978.is_native_tactic);
        identifier_info = (uu___156_4978.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___156_4978.dsenv)
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
      | (NoDelta ,uu____4993) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4994,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4995,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4996 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5005 . Prims.unit -> 'Auu____5005 FStar_Util.smap =
  fun uu____5011  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5016 . Prims.unit -> 'Auu____5016 FStar_Util.smap =
  fun uu____5022  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____5097 = new_gamma_cache () in
            let uu____5100 = new_sigtab () in
            let uu____5103 = FStar_Options.using_facts_from () in
            let uu____5104 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            let uu____5107 = FStar_ToSyntax_Env.empty_env () in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____5097;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____5100;
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
              proof_ns = uu____5103;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5139  -> false);
              identifier_info = uu____5104;
              tc_hooks = default_tc_hooks;
              dsenv = uu____5107
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
  fun uu____5210  ->
    let uu____5211 = FStar_ST.op_Bang query_indices in
    match uu____5211 with
    | [] -> failwith "Empty query indices!"
    | uu____5288 ->
        let uu____5297 =
          let uu____5306 =
            let uu____5313 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5313 in
          let uu____5390 = FStar_ST.op_Bang query_indices in uu____5306 ::
            uu____5390 in
        FStar_ST.op_Colon_Equals query_indices uu____5297
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5532  ->
    let uu____5533 = FStar_ST.op_Bang query_indices in
    match uu____5533 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5701  ->
    match uu____5701 with
    | (l,n1) ->
        let uu____5708 = FStar_ST.op_Bang query_indices in
        (match uu____5708 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5873 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5891  ->
    let uu____5892 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5892
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5987 =
       let uu____5990 = FStar_ST.op_Bang stack in env :: uu____5990 in
     FStar_ST.op_Colon_Equals stack uu____5987);
    (let uu___157_6093 = env in
     let uu____6094 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6097 = FStar_Util.smap_copy (sigtab env) in
     let uu____6100 =
       let uu____6103 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6103 in
     {
       solver = (uu___157_6093.solver);
       range = (uu___157_6093.range);
       curmodule = (uu___157_6093.curmodule);
       gamma = (uu___157_6093.gamma);
       gamma_cache = uu____6094;
       modules = (uu___157_6093.modules);
       expected_typ = (uu___157_6093.expected_typ);
       sigtab = uu____6097;
       is_pattern = (uu___157_6093.is_pattern);
       instantiate_imp = (uu___157_6093.instantiate_imp);
       effects = (uu___157_6093.effects);
       generalize = (uu___157_6093.generalize);
       letrecs = (uu___157_6093.letrecs);
       top_level = (uu___157_6093.top_level);
       check_uvars = (uu___157_6093.check_uvars);
       use_eq = (uu___157_6093.use_eq);
       is_iface = (uu___157_6093.is_iface);
       admit = (uu___157_6093.admit);
       lax = (uu___157_6093.lax);
       lax_universes = (uu___157_6093.lax_universes);
       failhard = (uu___157_6093.failhard);
       nosynth = (uu___157_6093.nosynth);
       tc_term = (uu___157_6093.tc_term);
       type_of = (uu___157_6093.type_of);
       universe_of = (uu___157_6093.universe_of);
       use_bv_sorts = (uu___157_6093.use_bv_sorts);
       qname_and_index = (uu___157_6093.qname_and_index);
       proof_ns = (uu___157_6093.proof_ns);
       synth = (uu___157_6093.synth);
       is_native_tactic = (uu___157_6093.is_native_tactic);
       identifier_info = uu____6100;
       tc_hooks = (uu___157_6093.tc_hooks);
       dsenv = (uu___157_6093.dsenv)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6167  ->
    let uu____6168 = FStar_ST.op_Bang stack in
    match uu____6168 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6276 -> failwith "Impossible: Too many pops"
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
        let uu____6320 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6346  ->
                  match uu____6346 with
                  | (m,uu____6352) -> FStar_Ident.lid_equals l m)) in
        (match uu____6320 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___158_6359 = env in
               {
                 solver = (uu___158_6359.solver);
                 range = (uu___158_6359.range);
                 curmodule = (uu___158_6359.curmodule);
                 gamma = (uu___158_6359.gamma);
                 gamma_cache = (uu___158_6359.gamma_cache);
                 modules = (uu___158_6359.modules);
                 expected_typ = (uu___158_6359.expected_typ);
                 sigtab = (uu___158_6359.sigtab);
                 is_pattern = (uu___158_6359.is_pattern);
                 instantiate_imp = (uu___158_6359.instantiate_imp);
                 effects = (uu___158_6359.effects);
                 generalize = (uu___158_6359.generalize);
                 letrecs = (uu___158_6359.letrecs);
                 top_level = (uu___158_6359.top_level);
                 check_uvars = (uu___158_6359.check_uvars);
                 use_eq = (uu___158_6359.use_eq);
                 is_iface = (uu___158_6359.is_iface);
                 admit = (uu___158_6359.admit);
                 lax = (uu___158_6359.lax);
                 lax_universes = (uu___158_6359.lax_universes);
                 failhard = (uu___158_6359.failhard);
                 nosynth = (uu___158_6359.nosynth);
                 tc_term = (uu___158_6359.tc_term);
                 type_of = (uu___158_6359.type_of);
                 universe_of = (uu___158_6359.universe_of);
                 use_bv_sorts = (uu___158_6359.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___158_6359.proof_ns);
                 synth = (uu___158_6359.synth);
                 is_native_tactic = (uu___158_6359.is_native_tactic);
                 identifier_info = (uu___158_6359.identifier_info);
                 tc_hooks = (uu___158_6359.tc_hooks);
                 dsenv = (uu___158_6359.dsenv)
               }))
         | FStar_Pervasives_Native.Some (uu____6364,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___159_6372 = env in
               {
                 solver = (uu___159_6372.solver);
                 range = (uu___159_6372.range);
                 curmodule = (uu___159_6372.curmodule);
                 gamma = (uu___159_6372.gamma);
                 gamma_cache = (uu___159_6372.gamma_cache);
                 modules = (uu___159_6372.modules);
                 expected_typ = (uu___159_6372.expected_typ);
                 sigtab = (uu___159_6372.sigtab);
                 is_pattern = (uu___159_6372.is_pattern);
                 instantiate_imp = (uu___159_6372.instantiate_imp);
                 effects = (uu___159_6372.effects);
                 generalize = (uu___159_6372.generalize);
                 letrecs = (uu___159_6372.letrecs);
                 top_level = (uu___159_6372.top_level);
                 check_uvars = (uu___159_6372.check_uvars);
                 use_eq = (uu___159_6372.use_eq);
                 is_iface = (uu___159_6372.is_iface);
                 admit = (uu___159_6372.admit);
                 lax = (uu___159_6372.lax);
                 lax_universes = (uu___159_6372.lax_universes);
                 failhard = (uu___159_6372.failhard);
                 nosynth = (uu___159_6372.nosynth);
                 tc_term = (uu___159_6372.tc_term);
                 type_of = (uu___159_6372.type_of);
                 universe_of = (uu___159_6372.universe_of);
                 use_bv_sorts = (uu___159_6372.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___159_6372.proof_ns);
                 synth = (uu___159_6372.synth);
                 is_native_tactic = (uu___159_6372.is_native_tactic);
                 identifier_info = (uu___159_6372.identifier_info);
                 tc_hooks = (uu___159_6372.tc_hooks);
                 dsenv = (uu___159_6372.dsenv)
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
        (let uu___160_6394 = e in
         {
           solver = (uu___160_6394.solver);
           range = r;
           curmodule = (uu___160_6394.curmodule);
           gamma = (uu___160_6394.gamma);
           gamma_cache = (uu___160_6394.gamma_cache);
           modules = (uu___160_6394.modules);
           expected_typ = (uu___160_6394.expected_typ);
           sigtab = (uu___160_6394.sigtab);
           is_pattern = (uu___160_6394.is_pattern);
           instantiate_imp = (uu___160_6394.instantiate_imp);
           effects = (uu___160_6394.effects);
           generalize = (uu___160_6394.generalize);
           letrecs = (uu___160_6394.letrecs);
           top_level = (uu___160_6394.top_level);
           check_uvars = (uu___160_6394.check_uvars);
           use_eq = (uu___160_6394.use_eq);
           is_iface = (uu___160_6394.is_iface);
           admit = (uu___160_6394.admit);
           lax = (uu___160_6394.lax);
           lax_universes = (uu___160_6394.lax_universes);
           failhard = (uu___160_6394.failhard);
           nosynth = (uu___160_6394.nosynth);
           tc_term = (uu___160_6394.tc_term);
           type_of = (uu___160_6394.type_of);
           universe_of = (uu___160_6394.universe_of);
           use_bv_sorts = (uu___160_6394.use_bv_sorts);
           qname_and_index = (uu___160_6394.qname_and_index);
           proof_ns = (uu___160_6394.proof_ns);
           synth = (uu___160_6394.synth);
           is_native_tactic = (uu___160_6394.is_native_tactic);
           identifier_info = (uu___160_6394.identifier_info);
           tc_hooks = (uu___160_6394.tc_hooks);
           dsenv = (uu___160_6394.dsenv)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6407 =
        let uu____6408 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6408 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6407
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6513 =
          let uu____6514 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6514 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6513
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6619 =
          let uu____6620 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6620 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6619
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6726 =
        let uu____6727 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6727 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6726
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___161_6838 = env in
      {
        solver = (uu___161_6838.solver);
        range = (uu___161_6838.range);
        curmodule = lid;
        gamma = (uu___161_6838.gamma);
        gamma_cache = (uu___161_6838.gamma_cache);
        modules = (uu___161_6838.modules);
        expected_typ = (uu___161_6838.expected_typ);
        sigtab = (uu___161_6838.sigtab);
        is_pattern = (uu___161_6838.is_pattern);
        instantiate_imp = (uu___161_6838.instantiate_imp);
        effects = (uu___161_6838.effects);
        generalize = (uu___161_6838.generalize);
        letrecs = (uu___161_6838.letrecs);
        top_level = (uu___161_6838.top_level);
        check_uvars = (uu___161_6838.check_uvars);
        use_eq = (uu___161_6838.use_eq);
        is_iface = (uu___161_6838.is_iface);
        admit = (uu___161_6838.admit);
        lax = (uu___161_6838.lax);
        lax_universes = (uu___161_6838.lax_universes);
        failhard = (uu___161_6838.failhard);
        nosynth = (uu___161_6838.nosynth);
        tc_term = (uu___161_6838.tc_term);
        type_of = (uu___161_6838.type_of);
        universe_of = (uu___161_6838.universe_of);
        use_bv_sorts = (uu___161_6838.use_bv_sorts);
        qname_and_index = (uu___161_6838.qname_and_index);
        proof_ns = (uu___161_6838.proof_ns);
        synth = (uu___161_6838.synth);
        is_native_tactic = (uu___161_6838.is_native_tactic);
        identifier_info = (uu___161_6838.identifier_info);
        tc_hooks = (uu___161_6838.tc_hooks);
        dsenv = (uu___161_6838.dsenv)
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
    let uu____6869 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6869
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6873  ->
    let uu____6874 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6874
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
      | ((formals,t),uu____6914) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6938 = FStar_Syntax_Subst.subst vs t in (us, uu____6938)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___141_6952  ->
    match uu___141_6952 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6976  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6991 = inst_tscheme t in
      match uu____6991 with
      | (us,t1) ->
          let uu____7002 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7002)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7018  ->
          match uu____7018 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7033 =
                         let uu____7034 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7035 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7036 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7037 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7034 uu____7035 uu____7036 uu____7037 in
                       failwith uu____7033)
                    else ();
                    (let uu____7039 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7039))
               | uu____7046 ->
                   let uu____7047 =
                     let uu____7048 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7048 in
                   failwith uu____7047)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7053 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7058 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7063 -> false
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
             | ([],uu____7099) -> Maybe
             | (uu____7106,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7125 -> No in
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
          let uu____7232 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7232 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___142_7277  ->
                   match uu___142_7277 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7320 =
                           let uu____7339 =
                             let uu____7354 = inst_tscheme t in
                             FStar_Util.Inl uu____7354 in
                           (uu____7339, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7320
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7420,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7422);
                                     FStar_Syntax_Syntax.sigrng = uu____7423;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7424;
                                     FStar_Syntax_Syntax.sigmeta = uu____7425;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7426;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7446 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7446
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7492 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7499 -> cache t in
                       let uu____7500 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7500 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7575 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7575 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7661 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7741 = find_in_sigtab env lid in
         match uu____7741 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7840) ->
          add_sigelts env ses
      | uu____7849 ->
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
            | uu____7863 -> ()))
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
        (fun uu___143_7892  ->
           match uu___143_7892 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7910 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7945,lb::[]),uu____7947) ->
          let uu____7960 =
            let uu____7969 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7978 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7969, uu____7978) in
          FStar_Pervasives_Native.Some uu____7960
      | FStar_Syntax_Syntax.Sig_let ((uu____7991,lbs),uu____7993) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8029 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8041 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8041
                   then
                     let uu____8052 =
                       let uu____8061 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8070 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8061, uu____8070) in
                     FStar_Pervasives_Native.Some uu____8052
                   else FStar_Pervasives_Native.None)
      | uu____8092 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8126 =
          let uu____8135 =
            let uu____8140 =
              let uu____8141 =
                let uu____8144 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8144 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8141) in
            inst_tscheme uu____8140 in
          (uu____8135, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8126
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8164,uu____8165) ->
        let uu____8170 =
          let uu____8179 =
            let uu____8184 =
              let uu____8185 =
                let uu____8188 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8188 in
              (us, uu____8185) in
            inst_tscheme uu____8184 in
          (uu____8179, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8170
    | uu____8205 -> FStar_Pervasives_Native.None
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
      let mapper uu____8265 =
        match uu____8265 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8361,uvs,t,uu____8364,uu____8365,uu____8366);
                    FStar_Syntax_Syntax.sigrng = uu____8367;
                    FStar_Syntax_Syntax.sigquals = uu____8368;
                    FStar_Syntax_Syntax.sigmeta = uu____8369;
                    FStar_Syntax_Syntax.sigattrs = uu____8370;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8391 =
                   let uu____8400 = inst_tscheme (uvs, t) in
                   (uu____8400, rng) in
                 FStar_Pervasives_Native.Some uu____8391
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8420;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8422;
                    FStar_Syntax_Syntax.sigattrs = uu____8423;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8440 =
                   let uu____8441 = in_cur_mod env l in uu____8441 = Yes in
                 if uu____8440
                 then
                   let uu____8452 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8452
                    then
                      let uu____8465 =
                        let uu____8474 = inst_tscheme (uvs, t) in
                        (uu____8474, rng) in
                      FStar_Pervasives_Native.Some uu____8465
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8501 =
                      let uu____8510 = inst_tscheme (uvs, t) in
                      (uu____8510, rng) in
                    FStar_Pervasives_Native.Some uu____8501)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8531,uu____8532);
                    FStar_Syntax_Syntax.sigrng = uu____8533;
                    FStar_Syntax_Syntax.sigquals = uu____8534;
                    FStar_Syntax_Syntax.sigmeta = uu____8535;
                    FStar_Syntax_Syntax.sigattrs = uu____8536;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8575 =
                        let uu____8584 = inst_tscheme (uvs, k) in
                        (uu____8584, rng) in
                      FStar_Pervasives_Native.Some uu____8575
                  | uu____8601 ->
                      let uu____8602 =
                        let uu____8611 =
                          let uu____8616 =
                            let uu____8617 =
                              let uu____8620 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8620 in
                            (uvs, uu____8617) in
                          inst_tscheme uu____8616 in
                        (uu____8611, rng) in
                      FStar_Pervasives_Native.Some uu____8602)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8641,uu____8642);
                    FStar_Syntax_Syntax.sigrng = uu____8643;
                    FStar_Syntax_Syntax.sigquals = uu____8644;
                    FStar_Syntax_Syntax.sigmeta = uu____8645;
                    FStar_Syntax_Syntax.sigattrs = uu____8646;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8686 =
                        let uu____8695 = inst_tscheme_with (uvs, k) us in
                        (uu____8695, rng) in
                      FStar_Pervasives_Native.Some uu____8686
                  | uu____8712 ->
                      let uu____8713 =
                        let uu____8722 =
                          let uu____8727 =
                            let uu____8728 =
                              let uu____8731 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8731 in
                            (uvs, uu____8728) in
                          inst_tscheme_with uu____8727 us in
                        (uu____8722, rng) in
                      FStar_Pervasives_Native.Some uu____8713)
             | FStar_Util.Inr se ->
                 let uu____8765 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8786;
                        FStar_Syntax_Syntax.sigrng = uu____8787;
                        FStar_Syntax_Syntax.sigquals = uu____8788;
                        FStar_Syntax_Syntax.sigmeta = uu____8789;
                        FStar_Syntax_Syntax.sigattrs = uu____8790;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8805 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8765
                   (FStar_Util.map_option
                      (fun uu____8853  ->
                         match uu____8853 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8884 =
        let uu____8895 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8895 mapper in
      match uu____8884 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___162_8988 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___162_8988.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___162_8988.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9015 = lookup_qname env l in
      match uu____9015 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9054 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9104 = try_lookup_bv env bv in
      match uu____9104 with
      | FStar_Pervasives_Native.None  ->
          let uu____9119 =
            let uu____9120 =
              let uu____9125 = variable_not_found bv in (uu____9125, bvr) in
            FStar_Errors.Error uu____9120 in
          FStar_Exn.raise uu____9119
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9136 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9137 =
            let uu____9138 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9138 in
          (uu____9136, uu____9137)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9157 = try_lookup_lid_aux env l in
      match uu____9157 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9223 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9223 in
          let uu____9224 =
            let uu____9233 =
              let uu____9238 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9238) in
            (uu____9233, r1) in
          FStar_Pervasives_Native.Some uu____9224
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9267 = try_lookup_lid env l in
      match uu____9267 with
      | FStar_Pervasives_Native.None  ->
          let uu____9294 =
            let uu____9295 =
              let uu____9300 = name_not_found l in
              (uu____9300, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9295 in
          FStar_Exn.raise uu____9294
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___144_9338  ->
              match uu___144_9338 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9340 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9357 = lookup_qname env lid in
      match uu____9357 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9386,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9389;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9391;
              FStar_Syntax_Syntax.sigattrs = uu____9392;_},FStar_Pervasives_Native.None
            ),uu____9393)
          ->
          let uu____9442 =
            let uu____9453 =
              let uu____9458 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9458) in
            (uu____9453, q) in
          FStar_Pervasives_Native.Some uu____9442
      | uu____9475 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9514 = lookup_qname env lid in
      match uu____9514 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9539,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9542;
              FStar_Syntax_Syntax.sigquals = uu____9543;
              FStar_Syntax_Syntax.sigmeta = uu____9544;
              FStar_Syntax_Syntax.sigattrs = uu____9545;_},FStar_Pervasives_Native.None
            ),uu____9546)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9595 ->
          let uu____9616 =
            let uu____9617 =
              let uu____9622 = name_not_found lid in
              (uu____9622, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9617 in
          FStar_Exn.raise uu____9616
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9639 = lookup_qname env lid in
      match uu____9639 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9664,uvs,t,uu____9667,uu____9668,uu____9669);
              FStar_Syntax_Syntax.sigrng = uu____9670;
              FStar_Syntax_Syntax.sigquals = uu____9671;
              FStar_Syntax_Syntax.sigmeta = uu____9672;
              FStar_Syntax_Syntax.sigattrs = uu____9673;_},FStar_Pervasives_Native.None
            ),uu____9674)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9727 ->
          let uu____9748 =
            let uu____9749 =
              let uu____9754 = name_not_found lid in
              (uu____9754, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9749 in
          FStar_Exn.raise uu____9748
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9773 = lookup_qname env lid in
      match uu____9773 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9800,uu____9801,uu____9802,uu____9803,uu____9804,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9806;
              FStar_Syntax_Syntax.sigquals = uu____9807;
              FStar_Syntax_Syntax.sigmeta = uu____9808;
              FStar_Syntax_Syntax.sigattrs = uu____9809;_},uu____9810),uu____9811)
          -> (true, dcs)
      | uu____9872 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9903 = lookup_qname env lid in
      match uu____9903 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9924,uu____9925,uu____9926,l,uu____9928,uu____9929);
              FStar_Syntax_Syntax.sigrng = uu____9930;
              FStar_Syntax_Syntax.sigquals = uu____9931;
              FStar_Syntax_Syntax.sigmeta = uu____9932;
              FStar_Syntax_Syntax.sigattrs = uu____9933;_},uu____9934),uu____9935)
          -> l
      | uu____9990 ->
          let uu____10011 =
            let uu____10012 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10012 in
          failwith uu____10011
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
        let uu____10049 = lookup_qname env lid in
        match uu____10049 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10077)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10128,lbs),uu____10130)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10158 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10158
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10190 -> FStar_Pervasives_Native.None)
        | uu____10195 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10232 = lookup_qname env ftv in
      match uu____10232 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10256) ->
          let uu____10301 = effect_signature se in
          (match uu____10301 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10322,t),r) ->
               let uu____10337 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10337)
      | uu____10338 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10367 = try_lookup_effect_lid env ftv in
      match uu____10367 with
      | FStar_Pervasives_Native.None  ->
          let uu____10370 =
            let uu____10371 =
              let uu____10376 = name_not_found ftv in
              (uu____10376, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10371 in
          FStar_Exn.raise uu____10370
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
        let uu____10396 = lookup_qname env lid0 in
        match uu____10396 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10427);
                FStar_Syntax_Syntax.sigrng = uu____10428;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10430;
                FStar_Syntax_Syntax.sigattrs = uu____10431;_},FStar_Pervasives_Native.None
              ),uu____10432)
            ->
            let lid1 =
              let uu____10486 =
                let uu____10487 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10487 in
              FStar_Ident.set_lid_range lid uu____10486 in
            let uu____10488 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___145_10492  ->
                      match uu___145_10492 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10493 -> false)) in
            if uu____10488
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10507 =
                      let uu____10508 =
                        let uu____10509 = get_range env in
                        FStar_Range.string_of_range uu____10509 in
                      let uu____10510 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10511 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10508 uu____10510 uu____10511 in
                    failwith uu____10507) in
               match (binders, univs1) with
               | ([],uu____10518) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10535,uu____10536::uu____10537::uu____10538) ->
                   let uu____10543 =
                     let uu____10544 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10545 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10544 uu____10545 in
                   failwith uu____10543
               | uu____10552 ->
                   let uu____10557 =
                     let uu____10562 =
                       let uu____10563 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10563) in
                     inst_tscheme_with uu____10562 insts in
                   (match uu____10557 with
                    | (uu____10574,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10577 =
                          let uu____10578 = FStar_Syntax_Subst.compress t1 in
                          uu____10578.FStar_Syntax_Syntax.n in
                        (match uu____10577 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10625 -> failwith "Impossible")))
        | uu____10632 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10674 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10674 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10687,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10694 = find1 l2 in
            (match uu____10694 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10701 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10701 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10705 = find1 l in
            (match uu____10705 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10721 = lookup_qname env l1 in
      match uu____10721 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10744;
              FStar_Syntax_Syntax.sigrng = uu____10745;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10747;
              FStar_Syntax_Syntax.sigattrs = uu____10748;_},uu____10749),uu____10750)
          -> q
      | uu____10801 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10837 =
          let uu____10838 =
            let uu____10839 = FStar_Util.string_of_int i in
            let uu____10840 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10839 uu____10840 in
          failwith uu____10838 in
        let uu____10841 = lookup_datacon env lid in
        match uu____10841 with
        | (uu____10846,t) ->
            let uu____10848 =
              let uu____10849 = FStar_Syntax_Subst.compress t in
              uu____10849.FStar_Syntax_Syntax.n in
            (match uu____10848 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10853) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10884 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10884
                      FStar_Pervasives_Native.fst)
             | uu____10893 -> fail ())
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
            (fun uu___146_10984  ->
               match uu___146_10984 with
               | FStar_Syntax_Syntax.Projector uu____10985 -> true
               | uu____10990 -> false) quals
      | uu____10991 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11020 = lookup_qname env lid in
      match uu____11020 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11041,uu____11042,uu____11043,uu____11044,uu____11045,uu____11046);
              FStar_Syntax_Syntax.sigrng = uu____11047;
              FStar_Syntax_Syntax.sigquals = uu____11048;
              FStar_Syntax_Syntax.sigmeta = uu____11049;
              FStar_Syntax_Syntax.sigattrs = uu____11050;_},uu____11051),uu____11052)
          -> true
      | uu____11107 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11136 = lookup_qname env lid in
      match uu____11136 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11157,uu____11158,uu____11159,uu____11160,uu____11161,uu____11162);
              FStar_Syntax_Syntax.sigrng = uu____11163;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11165;
              FStar_Syntax_Syntax.sigattrs = uu____11166;_},uu____11167),uu____11168)
          ->
          FStar_Util.for_some
            (fun uu___147_11229  ->
               match uu___147_11229 with
               | FStar_Syntax_Syntax.RecordType uu____11230 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11239 -> true
               | uu____11248 -> false) quals
      | uu____11249 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11278 = lookup_qname env lid in
      match uu____11278 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11299,uu____11300);
              FStar_Syntax_Syntax.sigrng = uu____11301;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11303;
              FStar_Syntax_Syntax.sigattrs = uu____11304;_},uu____11305),uu____11306)
          ->
          FStar_Util.for_some
            (fun uu___148_11363  ->
               match uu___148_11363 with
               | FStar_Syntax_Syntax.Action uu____11364 -> true
               | uu____11365 -> false) quals
      | uu____11366 -> false
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
      let uu____11398 =
        let uu____11399 = FStar_Syntax_Util.un_uinst head1 in
        uu____11399.FStar_Syntax_Syntax.n in
      match uu____11398 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11403 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11470 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11486) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11503 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11510 ->
                 FStar_Pervasives_Native.Some true
             | uu____11527 -> FStar_Pervasives_Native.Some false) in
      let uu____11528 =
        let uu____11531 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11531 mapper in
      match uu____11528 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11579 = lookup_qname env lid in
      match uu____11579 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11600,uu____11601,tps,uu____11603,uu____11604,uu____11605);
              FStar_Syntax_Syntax.sigrng = uu____11606;
              FStar_Syntax_Syntax.sigquals = uu____11607;
              FStar_Syntax_Syntax.sigmeta = uu____11608;
              FStar_Syntax_Syntax.sigattrs = uu____11609;_},uu____11610),uu____11611)
          -> FStar_List.length tps
      | uu____11674 ->
          let uu____11695 =
            let uu____11696 =
              let uu____11701 = name_not_found lid in
              (uu____11701, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11696 in
          FStar_Exn.raise uu____11695
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
           (fun uu____11743  ->
              match uu____11743 with
              | (d,uu____11751) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11764 = effect_decl_opt env l in
      match uu____11764 with
      | FStar_Pervasives_Native.None  ->
          let uu____11779 =
            let uu____11780 =
              let uu____11785 = name_not_found l in
              (uu____11785, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11780 in
          FStar_Exn.raise uu____11779
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
            (let uu____11851 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11904  ->
                       match uu____11904 with
                       | (m1,m2,uu____11917,uu____11918,uu____11919) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11851 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11936 =
                   let uu____11937 =
                     let uu____11942 =
                       let uu____11943 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11944 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11943
                         uu____11944 in
                     (uu____11942, (env.range)) in
                   FStar_Errors.Error uu____11937 in
                 FStar_Exn.raise uu____11936
             | FStar_Pervasives_Native.Some
                 (uu____11951,uu____11952,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11995 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11995)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12022 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12048  ->
                match uu____12048 with
                | (d,uu____12054) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12022 with
      | FStar_Pervasives_Native.None  ->
          let uu____12065 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12065
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12078 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12078 with
           | (uu____12089,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12099)::(wp,uu____12101)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12137 -> failwith "Impossible"))
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
                 let uu____12186 = get_range env in
                 let uu____12187 =
                   let uu____12190 =
                     let uu____12191 =
                       let uu____12206 =
                         let uu____12209 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12209] in
                       (null_wp, uu____12206) in
                     FStar_Syntax_Syntax.Tm_app uu____12191 in
                   FStar_Syntax_Syntax.mk uu____12190 in
                 uu____12187 FStar_Pervasives_Native.None uu____12186 in
               let uu____12215 =
                 let uu____12216 =
                   let uu____12225 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12225] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12216;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12215)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___163_12236 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___163_12236.order);
              joins = (uu___163_12236.joins)
            } in
          let uu___164_12245 = env in
          {
            solver = (uu___164_12245.solver);
            range = (uu___164_12245.range);
            curmodule = (uu___164_12245.curmodule);
            gamma = (uu___164_12245.gamma);
            gamma_cache = (uu___164_12245.gamma_cache);
            modules = (uu___164_12245.modules);
            expected_typ = (uu___164_12245.expected_typ);
            sigtab = (uu___164_12245.sigtab);
            is_pattern = (uu___164_12245.is_pattern);
            instantiate_imp = (uu___164_12245.instantiate_imp);
            effects;
            generalize = (uu___164_12245.generalize);
            letrecs = (uu___164_12245.letrecs);
            top_level = (uu___164_12245.top_level);
            check_uvars = (uu___164_12245.check_uvars);
            use_eq = (uu___164_12245.use_eq);
            is_iface = (uu___164_12245.is_iface);
            admit = (uu___164_12245.admit);
            lax = (uu___164_12245.lax);
            lax_universes = (uu___164_12245.lax_universes);
            failhard = (uu___164_12245.failhard);
            nosynth = (uu___164_12245.nosynth);
            tc_term = (uu___164_12245.tc_term);
            type_of = (uu___164_12245.type_of);
            universe_of = (uu___164_12245.universe_of);
            use_bv_sorts = (uu___164_12245.use_bv_sorts);
            qname_and_index = (uu___164_12245.qname_and_index);
            proof_ns = (uu___164_12245.proof_ns);
            synth = (uu___164_12245.synth);
            is_native_tactic = (uu___164_12245.is_native_tactic);
            identifier_info = (uu___164_12245.identifier_info);
            tc_hooks = (uu___164_12245.tc_hooks);
            dsenv = (uu___164_12245.dsenv)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12262 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12262 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12352 = (e1.mlift).mlift_wp t wp in
                              let uu____12353 = l1 t wp e in
                              l2 t uu____12352 uu____12353))
                | uu____12354 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12393 = inst_tscheme lift_t in
            match uu____12393 with
            | (uu____12400,lift_t1) ->
                let uu____12402 =
                  let uu____12405 =
                    let uu____12406 =
                      let uu____12421 =
                        let uu____12424 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12425 =
                          let uu____12428 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12428] in
                        uu____12424 :: uu____12425 in
                      (lift_t1, uu____12421) in
                    FStar_Syntax_Syntax.Tm_app uu____12406 in
                  FStar_Syntax_Syntax.mk uu____12405 in
                uu____12402 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12469 = inst_tscheme lift_t in
            match uu____12469 with
            | (uu____12476,lift_t1) ->
                let uu____12478 =
                  let uu____12481 =
                    let uu____12482 =
                      let uu____12497 =
                        let uu____12500 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12501 =
                          let uu____12504 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12505 =
                            let uu____12508 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12508] in
                          uu____12504 :: uu____12505 in
                        uu____12500 :: uu____12501 in
                      (lift_t1, uu____12497) in
                    FStar_Syntax_Syntax.Tm_app uu____12482 in
                  FStar_Syntax_Syntax.mk uu____12481 in
                uu____12478 FStar_Pervasives_Native.None
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
              let uu____12546 =
                let uu____12547 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12547
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12546 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12551 =
              let uu____12552 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12552 in
            let uu____12553 =
              let uu____12554 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12572 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12572) in
              FStar_Util.dflt "none" uu____12554 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12551
              uu____12553 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12598  ->
                    match uu____12598 with
                    | (e,uu____12606) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12625 =
            match uu____12625 with
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
              let uu____12663 =
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
                                    (let uu____12684 =
                                       let uu____12693 =
                                         find_edge order1 (i, k) in
                                       let uu____12696 =
                                         find_edge order1 (k, j) in
                                       (uu____12693, uu____12696) in
                                     match uu____12684 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12711 =
                                           compose_edges e1 e2 in
                                         [uu____12711]
                                     | uu____12712 -> []))))) in
              FStar_List.append order1 uu____12663 in
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
                   let uu____12741 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12743 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12743
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12741
                   then
                     let uu____12748 =
                       let uu____12749 =
                         let uu____12754 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12755 = get_range env in
                         (uu____12754, uu____12755) in
                       FStar_Errors.Error uu____12749 in
                     FStar_Exn.raise uu____12748
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
                                            let uu____12880 =
                                              let uu____12889 =
                                                find_edge order2 (i, k) in
                                              let uu____12892 =
                                                find_edge order2 (j, k) in
                                              (uu____12889, uu____12892) in
                                            match uu____12880 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12934,uu____12935)
                                                     ->
                                                     let uu____12942 =
                                                       let uu____12947 =
                                                         let uu____12948 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12948 in
                                                       let uu____12951 =
                                                         let uu____12952 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12952 in
                                                       (uu____12947,
                                                         uu____12951) in
                                                     (match uu____12942 with
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
                                            | uu____12987 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___165_13060 = env.effects in
              { decls = (uu___165_13060.decls); order = order2; joins } in
            let uu___166_13061 = env in
            {
              solver = (uu___166_13061.solver);
              range = (uu___166_13061.range);
              curmodule = (uu___166_13061.curmodule);
              gamma = (uu___166_13061.gamma);
              gamma_cache = (uu___166_13061.gamma_cache);
              modules = (uu___166_13061.modules);
              expected_typ = (uu___166_13061.expected_typ);
              sigtab = (uu___166_13061.sigtab);
              is_pattern = (uu___166_13061.is_pattern);
              instantiate_imp = (uu___166_13061.instantiate_imp);
              effects;
              generalize = (uu___166_13061.generalize);
              letrecs = (uu___166_13061.letrecs);
              top_level = (uu___166_13061.top_level);
              check_uvars = (uu___166_13061.check_uvars);
              use_eq = (uu___166_13061.use_eq);
              is_iface = (uu___166_13061.is_iface);
              admit = (uu___166_13061.admit);
              lax = (uu___166_13061.lax);
              lax_universes = (uu___166_13061.lax_universes);
              failhard = (uu___166_13061.failhard);
              nosynth = (uu___166_13061.nosynth);
              tc_term = (uu___166_13061.tc_term);
              type_of = (uu___166_13061.type_of);
              universe_of = (uu___166_13061.universe_of);
              use_bv_sorts = (uu___166_13061.use_bv_sorts);
              qname_and_index = (uu___166_13061.qname_and_index);
              proof_ns = (uu___166_13061.proof_ns);
              synth = (uu___166_13061.synth);
              is_native_tactic = (uu___166_13061.is_native_tactic);
              identifier_info = (uu___166_13061.identifier_info);
              tc_hooks = (uu___166_13061.tc_hooks);
              dsenv = (uu___166_13061.dsenv)
            }))
      | uu____13062 -> env
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
        | uu____13088 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13098 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13098 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13115 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13115 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13133 =
                     let uu____13134 =
                       let uu____13139 =
                         let uu____13140 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13145 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13152 =
                           let uu____13153 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13153 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13140 uu____13145 uu____13152 in
                       (uu____13139, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13134 in
                   FStar_Exn.raise uu____13133)
                else ();
                (let inst1 =
                   let uu____13158 =
                     let uu____13167 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13167 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13184  ->
                        fun uu____13185  ->
                          match (uu____13184, uu____13185) with
                          | ((x,uu____13207),(t,uu____13209)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13158 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13228 =
                     let uu___167_13229 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___167_13229.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___167_13229.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___167_13229.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___167_13229.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13228
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
          let uu____13255 = effect_decl_opt env effect_name in
          match uu____13255 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13288 =
                only_reifiable &&
                  (let uu____13290 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13290) in
              if uu____13288
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13306 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13325 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13354 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13354
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13355 =
                             let uu____13356 =
                               let uu____13361 = get_range env in
                               (message, uu____13361) in
                             FStar_Errors.Error uu____13356 in
                           FStar_Exn.raise uu____13355 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13371 =
                       let uu____13374 = get_range env in
                       let uu____13375 =
                         let uu____13378 =
                           let uu____13379 =
                             let uu____13394 =
                               let uu____13397 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13397; wp] in
                             (repr, uu____13394) in
                           FStar_Syntax_Syntax.Tm_app uu____13379 in
                         FStar_Syntax_Syntax.mk uu____13378 in
                       uu____13375 FStar_Pervasives_Native.None uu____13374 in
                     FStar_Pervasives_Native.Some uu____13371)
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
          let uu____13449 =
            let uu____13450 =
              let uu____13455 =
                let uu____13456 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13456 in
              let uu____13457 = get_range env in (uu____13455, uu____13457) in
            FStar_Errors.Error uu____13450 in
          FStar_Exn.raise uu____13449 in
        let uu____13458 = effect_repr_aux true env c u_c in
        match uu____13458 with
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
      | uu____13498 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13507 =
        let uu____13508 = FStar_Syntax_Subst.compress t in
        uu____13508.FStar_Syntax_Syntax.n in
      match uu____13507 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13511,c) ->
          is_reifiable_comp env c
      | uu____13529 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13553)::uu____13554 -> x :: rest
        | (Binding_sig_inst uu____13563)::uu____13564 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13579 = push1 x rest1 in local :: uu____13579 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___168_13583 = env in
       let uu____13584 = push1 s env.gamma in
       {
         solver = (uu___168_13583.solver);
         range = (uu___168_13583.range);
         curmodule = (uu___168_13583.curmodule);
         gamma = uu____13584;
         gamma_cache = (uu___168_13583.gamma_cache);
         modules = (uu___168_13583.modules);
         expected_typ = (uu___168_13583.expected_typ);
         sigtab = (uu___168_13583.sigtab);
         is_pattern = (uu___168_13583.is_pattern);
         instantiate_imp = (uu___168_13583.instantiate_imp);
         effects = (uu___168_13583.effects);
         generalize = (uu___168_13583.generalize);
         letrecs = (uu___168_13583.letrecs);
         top_level = (uu___168_13583.top_level);
         check_uvars = (uu___168_13583.check_uvars);
         use_eq = (uu___168_13583.use_eq);
         is_iface = (uu___168_13583.is_iface);
         admit = (uu___168_13583.admit);
         lax = (uu___168_13583.lax);
         lax_universes = (uu___168_13583.lax_universes);
         failhard = (uu___168_13583.failhard);
         nosynth = (uu___168_13583.nosynth);
         tc_term = (uu___168_13583.tc_term);
         type_of = (uu___168_13583.type_of);
         universe_of = (uu___168_13583.universe_of);
         use_bv_sorts = (uu___168_13583.use_bv_sorts);
         qname_and_index = (uu___168_13583.qname_and_index);
         proof_ns = (uu___168_13583.proof_ns);
         synth = (uu___168_13583.synth);
         is_native_tactic = (uu___168_13583.is_native_tactic);
         identifier_info = (uu___168_13583.identifier_info);
         tc_hooks = (uu___168_13583.tc_hooks);
         dsenv = (uu___168_13583.dsenv)
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
      let uu___169_13621 = env in
      {
        solver = (uu___169_13621.solver);
        range = (uu___169_13621.range);
        curmodule = (uu___169_13621.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___169_13621.gamma_cache);
        modules = (uu___169_13621.modules);
        expected_typ = (uu___169_13621.expected_typ);
        sigtab = (uu___169_13621.sigtab);
        is_pattern = (uu___169_13621.is_pattern);
        instantiate_imp = (uu___169_13621.instantiate_imp);
        effects = (uu___169_13621.effects);
        generalize = (uu___169_13621.generalize);
        letrecs = (uu___169_13621.letrecs);
        top_level = (uu___169_13621.top_level);
        check_uvars = (uu___169_13621.check_uvars);
        use_eq = (uu___169_13621.use_eq);
        is_iface = (uu___169_13621.is_iface);
        admit = (uu___169_13621.admit);
        lax = (uu___169_13621.lax);
        lax_universes = (uu___169_13621.lax_universes);
        failhard = (uu___169_13621.failhard);
        nosynth = (uu___169_13621.nosynth);
        tc_term = (uu___169_13621.tc_term);
        type_of = (uu___169_13621.type_of);
        universe_of = (uu___169_13621.universe_of);
        use_bv_sorts = (uu___169_13621.use_bv_sorts);
        qname_and_index = (uu___169_13621.qname_and_index);
        proof_ns = (uu___169_13621.proof_ns);
        synth = (uu___169_13621.synth);
        is_native_tactic = (uu___169_13621.is_native_tactic);
        identifier_info = (uu___169_13621.identifier_info);
        tc_hooks = (uu___169_13621.tc_hooks);
        dsenv = (uu___169_13621.dsenv)
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
            (let uu___170_13655 = env in
             {
               solver = (uu___170_13655.solver);
               range = (uu___170_13655.range);
               curmodule = (uu___170_13655.curmodule);
               gamma = rest;
               gamma_cache = (uu___170_13655.gamma_cache);
               modules = (uu___170_13655.modules);
               expected_typ = (uu___170_13655.expected_typ);
               sigtab = (uu___170_13655.sigtab);
               is_pattern = (uu___170_13655.is_pattern);
               instantiate_imp = (uu___170_13655.instantiate_imp);
               effects = (uu___170_13655.effects);
               generalize = (uu___170_13655.generalize);
               letrecs = (uu___170_13655.letrecs);
               top_level = (uu___170_13655.top_level);
               check_uvars = (uu___170_13655.check_uvars);
               use_eq = (uu___170_13655.use_eq);
               is_iface = (uu___170_13655.is_iface);
               admit = (uu___170_13655.admit);
               lax = (uu___170_13655.lax);
               lax_universes = (uu___170_13655.lax_universes);
               failhard = (uu___170_13655.failhard);
               nosynth = (uu___170_13655.nosynth);
               tc_term = (uu___170_13655.tc_term);
               type_of = (uu___170_13655.type_of);
               universe_of = (uu___170_13655.universe_of);
               use_bv_sorts = (uu___170_13655.use_bv_sorts);
               qname_and_index = (uu___170_13655.qname_and_index);
               proof_ns = (uu___170_13655.proof_ns);
               synth = (uu___170_13655.synth);
               is_native_tactic = (uu___170_13655.is_native_tactic);
               identifier_info = (uu___170_13655.identifier_info);
               tc_hooks = (uu___170_13655.tc_hooks);
               dsenv = (uu___170_13655.dsenv)
             }))
    | uu____13656 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13680  ->
             match uu____13680 with | (x,uu____13686) -> push_bv env1 x) env
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
            let uu___171_13716 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___171_13716.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___171_13716.FStar_Syntax_Syntax.index);
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
      (let uu___172_13751 = env in
       {
         solver = (uu___172_13751.solver);
         range = (uu___172_13751.range);
         curmodule = (uu___172_13751.curmodule);
         gamma = [];
         gamma_cache = (uu___172_13751.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___172_13751.sigtab);
         is_pattern = (uu___172_13751.is_pattern);
         instantiate_imp = (uu___172_13751.instantiate_imp);
         effects = (uu___172_13751.effects);
         generalize = (uu___172_13751.generalize);
         letrecs = (uu___172_13751.letrecs);
         top_level = (uu___172_13751.top_level);
         check_uvars = (uu___172_13751.check_uvars);
         use_eq = (uu___172_13751.use_eq);
         is_iface = (uu___172_13751.is_iface);
         admit = (uu___172_13751.admit);
         lax = (uu___172_13751.lax);
         lax_universes = (uu___172_13751.lax_universes);
         failhard = (uu___172_13751.failhard);
         nosynth = (uu___172_13751.nosynth);
         tc_term = (uu___172_13751.tc_term);
         type_of = (uu___172_13751.type_of);
         universe_of = (uu___172_13751.universe_of);
         use_bv_sorts = (uu___172_13751.use_bv_sorts);
         qname_and_index = (uu___172_13751.qname_and_index);
         proof_ns = (uu___172_13751.proof_ns);
         synth = (uu___172_13751.synth);
         is_native_tactic = (uu___172_13751.is_native_tactic);
         identifier_info = (uu___172_13751.identifier_info);
         tc_hooks = (uu___172_13751.tc_hooks);
         dsenv = (uu___172_13751.dsenv)
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
        let uu____13788 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13788 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13816 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13816)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___173_13831 = env in
      {
        solver = (uu___173_13831.solver);
        range = (uu___173_13831.range);
        curmodule = (uu___173_13831.curmodule);
        gamma = (uu___173_13831.gamma);
        gamma_cache = (uu___173_13831.gamma_cache);
        modules = (uu___173_13831.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___173_13831.sigtab);
        is_pattern = (uu___173_13831.is_pattern);
        instantiate_imp = (uu___173_13831.instantiate_imp);
        effects = (uu___173_13831.effects);
        generalize = (uu___173_13831.generalize);
        letrecs = (uu___173_13831.letrecs);
        top_level = (uu___173_13831.top_level);
        check_uvars = (uu___173_13831.check_uvars);
        use_eq = false;
        is_iface = (uu___173_13831.is_iface);
        admit = (uu___173_13831.admit);
        lax = (uu___173_13831.lax);
        lax_universes = (uu___173_13831.lax_universes);
        failhard = (uu___173_13831.failhard);
        nosynth = (uu___173_13831.nosynth);
        tc_term = (uu___173_13831.tc_term);
        type_of = (uu___173_13831.type_of);
        universe_of = (uu___173_13831.universe_of);
        use_bv_sorts = (uu___173_13831.use_bv_sorts);
        qname_and_index = (uu___173_13831.qname_and_index);
        proof_ns = (uu___173_13831.proof_ns);
        synth = (uu___173_13831.synth);
        is_native_tactic = (uu___173_13831.is_native_tactic);
        identifier_info = (uu___173_13831.identifier_info);
        tc_hooks = (uu___173_13831.tc_hooks);
        dsenv = (uu___173_13831.dsenv)
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
    let uu____13857 = expected_typ env_ in
    ((let uu___174_13863 = env_ in
      {
        solver = (uu___174_13863.solver);
        range = (uu___174_13863.range);
        curmodule = (uu___174_13863.curmodule);
        gamma = (uu___174_13863.gamma);
        gamma_cache = (uu___174_13863.gamma_cache);
        modules = (uu___174_13863.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___174_13863.sigtab);
        is_pattern = (uu___174_13863.is_pattern);
        instantiate_imp = (uu___174_13863.instantiate_imp);
        effects = (uu___174_13863.effects);
        generalize = (uu___174_13863.generalize);
        letrecs = (uu___174_13863.letrecs);
        top_level = (uu___174_13863.top_level);
        check_uvars = (uu___174_13863.check_uvars);
        use_eq = false;
        is_iface = (uu___174_13863.is_iface);
        admit = (uu___174_13863.admit);
        lax = (uu___174_13863.lax);
        lax_universes = (uu___174_13863.lax_universes);
        failhard = (uu___174_13863.failhard);
        nosynth = (uu___174_13863.nosynth);
        tc_term = (uu___174_13863.tc_term);
        type_of = (uu___174_13863.type_of);
        universe_of = (uu___174_13863.universe_of);
        use_bv_sorts = (uu___174_13863.use_bv_sorts);
        qname_and_index = (uu___174_13863.qname_and_index);
        proof_ns = (uu___174_13863.proof_ns);
        synth = (uu___174_13863.synth);
        is_native_tactic = (uu___174_13863.is_native_tactic);
        identifier_info = (uu___174_13863.identifier_info);
        tc_hooks = (uu___174_13863.tc_hooks);
        dsenv = (uu___174_13863.dsenv)
      }), uu____13857)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13878 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___149_13888  ->
                    match uu___149_13888 with
                    | Binding_sig (uu____13891,se) -> [se]
                    | uu____13897 -> [])) in
          FStar_All.pipe_right uu____13878 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___175_13904 = env in
       {
         solver = (uu___175_13904.solver);
         range = (uu___175_13904.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___175_13904.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___175_13904.expected_typ);
         sigtab = (uu___175_13904.sigtab);
         is_pattern = (uu___175_13904.is_pattern);
         instantiate_imp = (uu___175_13904.instantiate_imp);
         effects = (uu___175_13904.effects);
         generalize = (uu___175_13904.generalize);
         letrecs = (uu___175_13904.letrecs);
         top_level = (uu___175_13904.top_level);
         check_uvars = (uu___175_13904.check_uvars);
         use_eq = (uu___175_13904.use_eq);
         is_iface = (uu___175_13904.is_iface);
         admit = (uu___175_13904.admit);
         lax = (uu___175_13904.lax);
         lax_universes = (uu___175_13904.lax_universes);
         failhard = (uu___175_13904.failhard);
         nosynth = (uu___175_13904.nosynth);
         tc_term = (uu___175_13904.tc_term);
         type_of = (uu___175_13904.type_of);
         universe_of = (uu___175_13904.universe_of);
         use_bv_sorts = (uu___175_13904.use_bv_sorts);
         qname_and_index = (uu___175_13904.qname_and_index);
         proof_ns = (uu___175_13904.proof_ns);
         synth = (uu___175_13904.synth);
         is_native_tactic = (uu___175_13904.is_native_tactic);
         identifier_info = (uu___175_13904.identifier_info);
         tc_hooks = (uu___175_13904.tc_hooks);
         dsenv = (uu___175_13904.dsenv)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13986)::tl1 -> aux out tl1
      | (Binding_lid (uu____13990,(uu____13991,t)))::tl1 ->
          let uu____14006 =
            let uu____14013 = FStar_Syntax_Free.uvars t in
            ext out uu____14013 in
          aux uu____14006 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14020;
            FStar_Syntax_Syntax.index = uu____14021;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14028 =
            let uu____14035 = FStar_Syntax_Free.uvars t in
            ext out uu____14035 in
          aux uu____14028 tl1
      | (Binding_sig uu____14042)::uu____14043 -> out
      | (Binding_sig_inst uu____14052)::uu____14053 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14109)::tl1 -> aux out tl1
      | (Binding_univ uu____14121)::tl1 -> aux out tl1
      | (Binding_lid (uu____14125,(uu____14126,t)))::tl1 ->
          let uu____14141 =
            let uu____14144 = FStar_Syntax_Free.univs t in
            ext out uu____14144 in
          aux uu____14141 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14147;
            FStar_Syntax_Syntax.index = uu____14148;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14155 =
            let uu____14158 = FStar_Syntax_Free.univs t in
            ext out uu____14158 in
          aux uu____14155 tl1
      | (Binding_sig uu____14161)::uu____14162 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14216)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14232 = FStar_Util.fifo_set_add uname out in
          aux uu____14232 tl1
      | (Binding_lid (uu____14235,(uu____14236,t)))::tl1 ->
          let uu____14251 =
            let uu____14254 = FStar_Syntax_Free.univnames t in
            ext out uu____14254 in
          aux uu____14251 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14257;
            FStar_Syntax_Syntax.index = uu____14258;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14265 =
            let uu____14268 = FStar_Syntax_Free.univnames t in
            ext out uu____14268 in
          aux uu____14265 tl1
      | (Binding_sig uu____14271)::uu____14272 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___150_14297  ->
            match uu___150_14297 with
            | Binding_var x -> [x]
            | Binding_lid uu____14301 -> []
            | Binding_sig uu____14306 -> []
            | Binding_univ uu____14313 -> []
            | Binding_sig_inst uu____14314 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14331 =
      let uu____14334 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14334
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14331 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14359 =
      let uu____14360 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___151_14370  ->
                match uu___151_14370 with
                | Binding_var x ->
                    let uu____14372 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14372
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14375) ->
                    let uu____14376 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14376
                | Binding_sig (ls,uu____14378) ->
                    let uu____14383 =
                      let uu____14384 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14384
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14383
                | Binding_sig_inst (ls,uu____14394,uu____14395) ->
                    let uu____14400 =
                      let uu____14401 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14401
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14400)) in
      FStar_All.pipe_right uu____14360 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14359 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14420 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14420
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14448  ->
                 fun uu____14449  ->
                   match (uu____14448, uu____14449) with
                   | ((b1,uu____14467),(b2,uu____14469)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___152_14516  ->
    match uu___152_14516 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14517 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___153_14536  ->
             match uu___153_14536 with
             | Binding_sig (lids,uu____14542) -> FStar_List.append lids keys
             | uu____14547 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14553  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14589) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14608,uu____14609) -> false in
      let uu____14618 =
        FStar_List.tryFind
          (fun uu____14636  ->
             match uu____14636 with | (p,uu____14644) -> list_prefix p path)
          env.proof_ns in
      match uu____14618 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14655,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14675 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14675
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___176_14690 = e in
        {
          solver = (uu___176_14690.solver);
          range = (uu___176_14690.range);
          curmodule = (uu___176_14690.curmodule);
          gamma = (uu___176_14690.gamma);
          gamma_cache = (uu___176_14690.gamma_cache);
          modules = (uu___176_14690.modules);
          expected_typ = (uu___176_14690.expected_typ);
          sigtab = (uu___176_14690.sigtab);
          is_pattern = (uu___176_14690.is_pattern);
          instantiate_imp = (uu___176_14690.instantiate_imp);
          effects = (uu___176_14690.effects);
          generalize = (uu___176_14690.generalize);
          letrecs = (uu___176_14690.letrecs);
          top_level = (uu___176_14690.top_level);
          check_uvars = (uu___176_14690.check_uvars);
          use_eq = (uu___176_14690.use_eq);
          is_iface = (uu___176_14690.is_iface);
          admit = (uu___176_14690.admit);
          lax = (uu___176_14690.lax);
          lax_universes = (uu___176_14690.lax_universes);
          failhard = (uu___176_14690.failhard);
          nosynth = (uu___176_14690.nosynth);
          tc_term = (uu___176_14690.tc_term);
          type_of = (uu___176_14690.type_of);
          universe_of = (uu___176_14690.universe_of);
          use_bv_sorts = (uu___176_14690.use_bv_sorts);
          qname_and_index = (uu___176_14690.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___176_14690.synth);
          is_native_tactic = (uu___176_14690.is_native_tactic);
          identifier_info = (uu___176_14690.identifier_info);
          tc_hooks = (uu___176_14690.tc_hooks);
          dsenv = (uu___176_14690.dsenv)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___177_14723 = e in
      {
        solver = (uu___177_14723.solver);
        range = (uu___177_14723.range);
        curmodule = (uu___177_14723.curmodule);
        gamma = (uu___177_14723.gamma);
        gamma_cache = (uu___177_14723.gamma_cache);
        modules = (uu___177_14723.modules);
        expected_typ = (uu___177_14723.expected_typ);
        sigtab = (uu___177_14723.sigtab);
        is_pattern = (uu___177_14723.is_pattern);
        instantiate_imp = (uu___177_14723.instantiate_imp);
        effects = (uu___177_14723.effects);
        generalize = (uu___177_14723.generalize);
        letrecs = (uu___177_14723.letrecs);
        top_level = (uu___177_14723.top_level);
        check_uvars = (uu___177_14723.check_uvars);
        use_eq = (uu___177_14723.use_eq);
        is_iface = (uu___177_14723.is_iface);
        admit = (uu___177_14723.admit);
        lax = (uu___177_14723.lax);
        lax_universes = (uu___177_14723.lax_universes);
        failhard = (uu___177_14723.failhard);
        nosynth = (uu___177_14723.nosynth);
        tc_term = (uu___177_14723.tc_term);
        type_of = (uu___177_14723.type_of);
        universe_of = (uu___177_14723.universe_of);
        use_bv_sorts = (uu___177_14723.use_bv_sorts);
        qname_and_index = (uu___177_14723.qname_and_index);
        proof_ns = ns;
        synth = (uu___177_14723.synth);
        is_native_tactic = (uu___177_14723.is_native_tactic);
        identifier_info = (uu___177_14723.identifier_info);
        tc_hooks = (uu___177_14723.tc_hooks);
        dsenv = (uu___177_14723.dsenv)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14736 = FStar_Syntax_Free.names t in
      let uu____14739 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14736 uu____14739
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14758 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14758
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14765 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14765
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14781 =
      match uu____14781 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14797 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14797) in
    let uu____14799 =
      let uu____14802 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14802 FStar_List.rev in
    FStar_All.pipe_right uu____14799 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14819  -> ());
    push = (fun uu____14821  -> ());
    pop = (fun uu____14823  -> ());
    encode_modul = (fun uu____14826  -> fun uu____14827  -> ());
    encode_sig = (fun uu____14830  -> fun uu____14831  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14837 =
             let uu____14844 = FStar_Options.peek () in (e, g, uu____14844) in
           [uu____14837]);
    solve = (fun uu____14860  -> fun uu____14861  -> fun uu____14862  -> ());
    finish = (fun uu____14868  -> ());
    refresh = (fun uu____14870  -> ())
  }