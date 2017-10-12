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
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4908  -> fun uu____4909  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___143_4922 = env in
      {
        solver = (uu___143_4922.solver);
        range = (uu___143_4922.range);
        curmodule = (uu___143_4922.curmodule);
        gamma = (uu___143_4922.gamma);
        gamma_cache = (uu___143_4922.gamma_cache);
        modules = (uu___143_4922.modules);
        expected_typ = (uu___143_4922.expected_typ);
        sigtab = (uu___143_4922.sigtab);
        is_pattern = (uu___143_4922.is_pattern);
        instantiate_imp = (uu___143_4922.instantiate_imp);
        effects = (uu___143_4922.effects);
        generalize = (uu___143_4922.generalize);
        letrecs = (uu___143_4922.letrecs);
        top_level = (uu___143_4922.top_level);
        check_uvars = (uu___143_4922.check_uvars);
        use_eq = (uu___143_4922.use_eq);
        is_iface = (uu___143_4922.is_iface);
        admit = (uu___143_4922.admit);
        lax = (uu___143_4922.lax);
        lax_universes = (uu___143_4922.lax_universes);
        failhard = (uu___143_4922.failhard);
        nosynth = (uu___143_4922.nosynth);
        tc_term = (uu___143_4922.tc_term);
        type_of = (uu___143_4922.type_of);
        universe_of = (uu___143_4922.universe_of);
        use_bv_sorts = (uu___143_4922.use_bv_sorts);
        qname_and_index = (uu___143_4922.qname_and_index);
        proof_ns = (uu___143_4922.proof_ns);
        synth = (uu___143_4922.synth);
        is_native_tactic = (uu___143_4922.is_native_tactic);
        identifier_info = (uu___143_4922.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___143_4922.dsenv)
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
      | (NoDelta ,uu____4937) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4938,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4939,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4940 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4949 . Prims.unit -> 'Auu____4949 FStar_Util.smap =
  fun uu____4955  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4960 . Prims.unit -> 'Auu____4960 FStar_Util.smap =
  fun uu____4966  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____5041 = new_gamma_cache () in
            let uu____5044 = new_sigtab () in
            let uu____5047 = FStar_Options.using_facts_from () in
            let uu____5048 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            let uu____5051 = FStar_ToSyntax_Env.empty_env () in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____5041;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____5044;
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
              proof_ns = uu____5047;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5083  -> false);
              identifier_info = uu____5048;
              tc_hooks = default_tc_hooks;
              dsenv = uu____5051
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
  fun uu____5154  ->
    let uu____5155 = FStar_ST.op_Bang query_indices in
    match uu____5155 with
    | [] -> failwith "Empty query indices!"
    | uu____5232 ->
        let uu____5241 =
          let uu____5250 =
            let uu____5257 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5257 in
          let uu____5334 = FStar_ST.op_Bang query_indices in uu____5250 ::
            uu____5334 in
        FStar_ST.op_Colon_Equals query_indices uu____5241
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5476  ->
    let uu____5477 = FStar_ST.op_Bang query_indices in
    match uu____5477 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5645  ->
    match uu____5645 with
    | (l,n1) ->
        let uu____5652 = FStar_ST.op_Bang query_indices in
        (match uu____5652 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5817 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5835  ->
    let uu____5836 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5836
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5931 =
       let uu____5934 = FStar_ST.op_Bang stack in env :: uu____5934 in
     FStar_ST.op_Colon_Equals stack uu____5931);
    (let uu___144_6037 = env in
     let uu____6038 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6041 = FStar_Util.smap_copy (sigtab env) in
     let uu____6044 =
       let uu____6047 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6047 in
     {
       solver = (uu___144_6037.solver);
       range = (uu___144_6037.range);
       curmodule = (uu___144_6037.curmodule);
       gamma = (uu___144_6037.gamma);
       gamma_cache = uu____6038;
       modules = (uu___144_6037.modules);
       expected_typ = (uu___144_6037.expected_typ);
       sigtab = uu____6041;
       is_pattern = (uu___144_6037.is_pattern);
       instantiate_imp = (uu___144_6037.instantiate_imp);
       effects = (uu___144_6037.effects);
       generalize = (uu___144_6037.generalize);
       letrecs = (uu___144_6037.letrecs);
       top_level = (uu___144_6037.top_level);
       check_uvars = (uu___144_6037.check_uvars);
       use_eq = (uu___144_6037.use_eq);
       is_iface = (uu___144_6037.is_iface);
       admit = (uu___144_6037.admit);
       lax = (uu___144_6037.lax);
       lax_universes = (uu___144_6037.lax_universes);
       failhard = (uu___144_6037.failhard);
       nosynth = (uu___144_6037.nosynth);
       tc_term = (uu___144_6037.tc_term);
       type_of = (uu___144_6037.type_of);
       universe_of = (uu___144_6037.universe_of);
       use_bv_sorts = (uu___144_6037.use_bv_sorts);
       qname_and_index = (uu___144_6037.qname_and_index);
       proof_ns = (uu___144_6037.proof_ns);
       synth = (uu___144_6037.synth);
       is_native_tactic = (uu___144_6037.is_native_tactic);
       identifier_info = uu____6044;
       tc_hooks = (uu___144_6037.tc_hooks);
       dsenv = (uu___144_6037.dsenv)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6111  ->
    let uu____6112 = FStar_ST.op_Bang stack in
    match uu____6112 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6220 -> failwith "Impossible: Too many pops"
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
        let uu____6264 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6290  ->
                  match uu____6290 with
                  | (m,uu____6296) -> FStar_Ident.lid_equals l m)) in
        (match uu____6264 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___145_6303 = env in
               {
                 solver = (uu___145_6303.solver);
                 range = (uu___145_6303.range);
                 curmodule = (uu___145_6303.curmodule);
                 gamma = (uu___145_6303.gamma);
                 gamma_cache = (uu___145_6303.gamma_cache);
                 modules = (uu___145_6303.modules);
                 expected_typ = (uu___145_6303.expected_typ);
                 sigtab = (uu___145_6303.sigtab);
                 is_pattern = (uu___145_6303.is_pattern);
                 instantiate_imp = (uu___145_6303.instantiate_imp);
                 effects = (uu___145_6303.effects);
                 generalize = (uu___145_6303.generalize);
                 letrecs = (uu___145_6303.letrecs);
                 top_level = (uu___145_6303.top_level);
                 check_uvars = (uu___145_6303.check_uvars);
                 use_eq = (uu___145_6303.use_eq);
                 is_iface = (uu___145_6303.is_iface);
                 admit = (uu___145_6303.admit);
                 lax = (uu___145_6303.lax);
                 lax_universes = (uu___145_6303.lax_universes);
                 failhard = (uu___145_6303.failhard);
                 nosynth = (uu___145_6303.nosynth);
                 tc_term = (uu___145_6303.tc_term);
                 type_of = (uu___145_6303.type_of);
                 universe_of = (uu___145_6303.universe_of);
                 use_bv_sorts = (uu___145_6303.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___145_6303.proof_ns);
                 synth = (uu___145_6303.synth);
                 is_native_tactic = (uu___145_6303.is_native_tactic);
                 identifier_info = (uu___145_6303.identifier_info);
                 tc_hooks = (uu___145_6303.tc_hooks);
                 dsenv = (uu___145_6303.dsenv)
               }))
         | FStar_Pervasives_Native.Some (uu____6308,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___146_6316 = env in
               {
                 solver = (uu___146_6316.solver);
                 range = (uu___146_6316.range);
                 curmodule = (uu___146_6316.curmodule);
                 gamma = (uu___146_6316.gamma);
                 gamma_cache = (uu___146_6316.gamma_cache);
                 modules = (uu___146_6316.modules);
                 expected_typ = (uu___146_6316.expected_typ);
                 sigtab = (uu___146_6316.sigtab);
                 is_pattern = (uu___146_6316.is_pattern);
                 instantiate_imp = (uu___146_6316.instantiate_imp);
                 effects = (uu___146_6316.effects);
                 generalize = (uu___146_6316.generalize);
                 letrecs = (uu___146_6316.letrecs);
                 top_level = (uu___146_6316.top_level);
                 check_uvars = (uu___146_6316.check_uvars);
                 use_eq = (uu___146_6316.use_eq);
                 is_iface = (uu___146_6316.is_iface);
                 admit = (uu___146_6316.admit);
                 lax = (uu___146_6316.lax);
                 lax_universes = (uu___146_6316.lax_universes);
                 failhard = (uu___146_6316.failhard);
                 nosynth = (uu___146_6316.nosynth);
                 tc_term = (uu___146_6316.tc_term);
                 type_of = (uu___146_6316.type_of);
                 universe_of = (uu___146_6316.universe_of);
                 use_bv_sorts = (uu___146_6316.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___146_6316.proof_ns);
                 synth = (uu___146_6316.synth);
                 is_native_tactic = (uu___146_6316.is_native_tactic);
                 identifier_info = (uu___146_6316.identifier_info);
                 tc_hooks = (uu___146_6316.tc_hooks);
                 dsenv = (uu___146_6316.dsenv)
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
        (let uu___147_6338 = e in
         {
           solver = (uu___147_6338.solver);
           range = r;
           curmodule = (uu___147_6338.curmodule);
           gamma = (uu___147_6338.gamma);
           gamma_cache = (uu___147_6338.gamma_cache);
           modules = (uu___147_6338.modules);
           expected_typ = (uu___147_6338.expected_typ);
           sigtab = (uu___147_6338.sigtab);
           is_pattern = (uu___147_6338.is_pattern);
           instantiate_imp = (uu___147_6338.instantiate_imp);
           effects = (uu___147_6338.effects);
           generalize = (uu___147_6338.generalize);
           letrecs = (uu___147_6338.letrecs);
           top_level = (uu___147_6338.top_level);
           check_uvars = (uu___147_6338.check_uvars);
           use_eq = (uu___147_6338.use_eq);
           is_iface = (uu___147_6338.is_iface);
           admit = (uu___147_6338.admit);
           lax = (uu___147_6338.lax);
           lax_universes = (uu___147_6338.lax_universes);
           failhard = (uu___147_6338.failhard);
           nosynth = (uu___147_6338.nosynth);
           tc_term = (uu___147_6338.tc_term);
           type_of = (uu___147_6338.type_of);
           universe_of = (uu___147_6338.universe_of);
           use_bv_sorts = (uu___147_6338.use_bv_sorts);
           qname_and_index = (uu___147_6338.qname_and_index);
           proof_ns = (uu___147_6338.proof_ns);
           synth = (uu___147_6338.synth);
           is_native_tactic = (uu___147_6338.is_native_tactic);
           identifier_info = (uu___147_6338.identifier_info);
           tc_hooks = (uu___147_6338.tc_hooks);
           dsenv = (uu___147_6338.dsenv)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6351 =
        let uu____6352 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6352 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6351
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6457 =
          let uu____6458 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6458 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6457
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6563 =
          let uu____6564 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6564 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6563
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6670 =
        let uu____6671 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6671 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6670
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___148_6782 = env in
      {
        solver = (uu___148_6782.solver);
        range = (uu___148_6782.range);
        curmodule = lid;
        gamma = (uu___148_6782.gamma);
        gamma_cache = (uu___148_6782.gamma_cache);
        modules = (uu___148_6782.modules);
        expected_typ = (uu___148_6782.expected_typ);
        sigtab = (uu___148_6782.sigtab);
        is_pattern = (uu___148_6782.is_pattern);
        instantiate_imp = (uu___148_6782.instantiate_imp);
        effects = (uu___148_6782.effects);
        generalize = (uu___148_6782.generalize);
        letrecs = (uu___148_6782.letrecs);
        top_level = (uu___148_6782.top_level);
        check_uvars = (uu___148_6782.check_uvars);
        use_eq = (uu___148_6782.use_eq);
        is_iface = (uu___148_6782.is_iface);
        admit = (uu___148_6782.admit);
        lax = (uu___148_6782.lax);
        lax_universes = (uu___148_6782.lax_universes);
        failhard = (uu___148_6782.failhard);
        nosynth = (uu___148_6782.nosynth);
        tc_term = (uu___148_6782.tc_term);
        type_of = (uu___148_6782.type_of);
        universe_of = (uu___148_6782.universe_of);
        use_bv_sorts = (uu___148_6782.use_bv_sorts);
        qname_and_index = (uu___148_6782.qname_and_index);
        proof_ns = (uu___148_6782.proof_ns);
        synth = (uu___148_6782.synth);
        is_native_tactic = (uu___148_6782.is_native_tactic);
        identifier_info = (uu___148_6782.identifier_info);
        tc_hooks = (uu___148_6782.tc_hooks);
        dsenv = (uu___148_6782.dsenv)
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
    let uu____6813 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6813
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6817  ->
    let uu____6818 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6818
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
      | ((formals,t),uu____6858) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6882 = FStar_Syntax_Subst.subst vs t in (us, uu____6882)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___130_6896  ->
    match uu___130_6896 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6920  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6935 = inst_tscheme t in
      match uu____6935 with
      | (us,t1) ->
          let uu____6946 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6946)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6962  ->
          match uu____6962 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6977 =
                         let uu____6978 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6979 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6980 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6981 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6978 uu____6979 uu____6980 uu____6981 in
                       failwith uu____6977)
                    else ();
                    (let uu____6983 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6983))
               | uu____6990 ->
                   let uu____6991 =
                     let uu____6992 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6992 in
                   failwith uu____6991)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6997 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7002 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7007 -> false
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
             | ([],uu____7043) -> Maybe
             | (uu____7050,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7069 -> No in
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
          let uu____7176 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7176 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___131_7221  ->
                   match uu___131_7221 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7264 =
                           let uu____7283 =
                             let uu____7298 = inst_tscheme t in
                             FStar_Util.Inl uu____7298 in
                           (uu____7283, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7264
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7364,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7366);
                                     FStar_Syntax_Syntax.sigrng = uu____7367;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7368;
                                     FStar_Syntax_Syntax.sigmeta = uu____7369;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7370;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7390 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7390
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7436 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7443 -> cache t in
                       let uu____7444 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7444 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7519 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7519 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7605 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7685 = find_in_sigtab env lid in
         match uu____7685 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7784) ->
          add_sigelts env ses
      | uu____7793 ->
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
            | uu____7807 -> ()))
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
        (fun uu___132_7836  ->
           match uu___132_7836 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7854 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7889,lb::[]),uu____7891) ->
          let uu____7904 =
            let uu____7913 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7922 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7913, uu____7922) in
          FStar_Pervasives_Native.Some uu____7904
      | FStar_Syntax_Syntax.Sig_let ((uu____7935,lbs),uu____7937) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7973 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7985 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7985
                   then
                     let uu____7996 =
                       let uu____8005 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8014 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8005, uu____8014) in
                     FStar_Pervasives_Native.Some uu____7996
                   else FStar_Pervasives_Native.None)
      | uu____8036 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8070 =
          let uu____8079 =
            let uu____8084 =
              let uu____8085 =
                let uu____8088 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8088 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8085) in
            inst_tscheme uu____8084 in
          (uu____8079, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8070
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8108,uu____8109) ->
        let uu____8114 =
          let uu____8123 =
            let uu____8128 =
              let uu____8129 =
                let uu____8132 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8132 in
              (us, uu____8129) in
            inst_tscheme uu____8128 in
          (uu____8123, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8114
    | uu____8149 -> FStar_Pervasives_Native.None
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
      let mapper uu____8209 =
        match uu____8209 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8305,uvs,t,uu____8308,uu____8309,uu____8310);
                    FStar_Syntax_Syntax.sigrng = uu____8311;
                    FStar_Syntax_Syntax.sigquals = uu____8312;
                    FStar_Syntax_Syntax.sigmeta = uu____8313;
                    FStar_Syntax_Syntax.sigattrs = uu____8314;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8335 =
                   let uu____8344 = inst_tscheme (uvs, t) in
                   (uu____8344, rng) in
                 FStar_Pervasives_Native.Some uu____8335
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8364;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8366;
                    FStar_Syntax_Syntax.sigattrs = uu____8367;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8384 =
                   let uu____8385 = in_cur_mod env l in uu____8385 = Yes in
                 if uu____8384
                 then
                   let uu____8396 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8396
                    then
                      let uu____8409 =
                        let uu____8418 = inst_tscheme (uvs, t) in
                        (uu____8418, rng) in
                      FStar_Pervasives_Native.Some uu____8409
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8445 =
                      let uu____8454 = inst_tscheme (uvs, t) in
                      (uu____8454, rng) in
                    FStar_Pervasives_Native.Some uu____8445)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8475,uu____8476);
                    FStar_Syntax_Syntax.sigrng = uu____8477;
                    FStar_Syntax_Syntax.sigquals = uu____8478;
                    FStar_Syntax_Syntax.sigmeta = uu____8479;
                    FStar_Syntax_Syntax.sigattrs = uu____8480;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8519 =
                        let uu____8528 = inst_tscheme (uvs, k) in
                        (uu____8528, rng) in
                      FStar_Pervasives_Native.Some uu____8519
                  | uu____8545 ->
                      let uu____8546 =
                        let uu____8555 =
                          let uu____8560 =
                            let uu____8561 =
                              let uu____8564 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8564 in
                            (uvs, uu____8561) in
                          inst_tscheme uu____8560 in
                        (uu____8555, rng) in
                      FStar_Pervasives_Native.Some uu____8546)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8585,uu____8586);
                    FStar_Syntax_Syntax.sigrng = uu____8587;
                    FStar_Syntax_Syntax.sigquals = uu____8588;
                    FStar_Syntax_Syntax.sigmeta = uu____8589;
                    FStar_Syntax_Syntax.sigattrs = uu____8590;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8630 =
                        let uu____8639 = inst_tscheme_with (uvs, k) us in
                        (uu____8639, rng) in
                      FStar_Pervasives_Native.Some uu____8630
                  | uu____8656 ->
                      let uu____8657 =
                        let uu____8666 =
                          let uu____8671 =
                            let uu____8672 =
                              let uu____8675 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8675 in
                            (uvs, uu____8672) in
                          inst_tscheme_with uu____8671 us in
                        (uu____8666, rng) in
                      FStar_Pervasives_Native.Some uu____8657)
             | FStar_Util.Inr se ->
                 let uu____8709 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8730;
                        FStar_Syntax_Syntax.sigrng = uu____8731;
                        FStar_Syntax_Syntax.sigquals = uu____8732;
                        FStar_Syntax_Syntax.sigmeta = uu____8733;
                        FStar_Syntax_Syntax.sigattrs = uu____8734;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8749 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8709
                   (FStar_Util.map_option
                      (fun uu____8797  ->
                         match uu____8797 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8828 =
        let uu____8839 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8839 mapper in
      match uu____8828 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___149_8932 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___149_8932.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___149_8932.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8959 = lookup_qname env l in
      match uu____8959 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8998 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9048 = try_lookup_bv env bv in
      match uu____9048 with
      | FStar_Pervasives_Native.None  ->
          let uu____9063 =
            let uu____9064 =
              let uu____9069 = variable_not_found bv in (uu____9069, bvr) in
            FStar_Errors.Error uu____9064 in
          FStar_Exn.raise uu____9063
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9080 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9081 =
            let uu____9082 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9082 in
          (uu____9080, uu____9081)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9101 = try_lookup_lid_aux env l in
      match uu____9101 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9167 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9167 in
          let uu____9168 =
            let uu____9177 =
              let uu____9182 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9182) in
            (uu____9177, r1) in
          FStar_Pervasives_Native.Some uu____9168
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9211 = try_lookup_lid env l in
      match uu____9211 with
      | FStar_Pervasives_Native.None  ->
          let uu____9238 =
            let uu____9239 =
              let uu____9244 = name_not_found l in
              (uu____9244, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9239 in
          FStar_Exn.raise uu____9238
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___133_9282  ->
              match uu___133_9282 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9284 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9301 = lookup_qname env lid in
      match uu____9301 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9330,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9333;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9335;
              FStar_Syntax_Syntax.sigattrs = uu____9336;_},FStar_Pervasives_Native.None
            ),uu____9337)
          ->
          let uu____9386 =
            let uu____9397 =
              let uu____9402 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9402) in
            (uu____9397, q) in
          FStar_Pervasives_Native.Some uu____9386
      | uu____9419 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9458 = lookup_qname env lid in
      match uu____9458 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9483,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9486;
              FStar_Syntax_Syntax.sigquals = uu____9487;
              FStar_Syntax_Syntax.sigmeta = uu____9488;
              FStar_Syntax_Syntax.sigattrs = uu____9489;_},FStar_Pervasives_Native.None
            ),uu____9490)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9539 ->
          let uu____9560 =
            let uu____9561 =
              let uu____9566 = name_not_found lid in
              (uu____9566, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9561 in
          FStar_Exn.raise uu____9560
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9583 = lookup_qname env lid in
      match uu____9583 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9608,uvs,t,uu____9611,uu____9612,uu____9613);
              FStar_Syntax_Syntax.sigrng = uu____9614;
              FStar_Syntax_Syntax.sigquals = uu____9615;
              FStar_Syntax_Syntax.sigmeta = uu____9616;
              FStar_Syntax_Syntax.sigattrs = uu____9617;_},FStar_Pervasives_Native.None
            ),uu____9618)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9671 ->
          let uu____9692 =
            let uu____9693 =
              let uu____9698 = name_not_found lid in
              (uu____9698, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9693 in
          FStar_Exn.raise uu____9692
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9717 = lookup_qname env lid in
      match uu____9717 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9744,uu____9745,uu____9746,uu____9747,uu____9748,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9750;
              FStar_Syntax_Syntax.sigquals = uu____9751;
              FStar_Syntax_Syntax.sigmeta = uu____9752;
              FStar_Syntax_Syntax.sigattrs = uu____9753;_},uu____9754),uu____9755)
          -> (true, dcs)
      | uu____9816 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9847 = lookup_qname env lid in
      match uu____9847 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9868,uu____9869,uu____9870,l,uu____9872,uu____9873);
              FStar_Syntax_Syntax.sigrng = uu____9874;
              FStar_Syntax_Syntax.sigquals = uu____9875;
              FStar_Syntax_Syntax.sigmeta = uu____9876;
              FStar_Syntax_Syntax.sigattrs = uu____9877;_},uu____9878),uu____9879)
          -> l
      | uu____9934 ->
          let uu____9955 =
            let uu____9956 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9956 in
          failwith uu____9955
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
        let uu____9993 = lookup_qname env lid in
        match uu____9993 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10021)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10072,lbs),uu____10074)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10102 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10102
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10134 -> FStar_Pervasives_Native.None)
        | uu____10139 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10176 = lookup_qname env ftv in
      match uu____10176 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10200) ->
          let uu____10245 = effect_signature se in
          (match uu____10245 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10266,t),r) ->
               let uu____10281 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10281)
      | uu____10282 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10311 = try_lookup_effect_lid env ftv in
      match uu____10311 with
      | FStar_Pervasives_Native.None  ->
          let uu____10314 =
            let uu____10315 =
              let uu____10320 = name_not_found ftv in
              (uu____10320, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10315 in
          FStar_Exn.raise uu____10314
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
        let uu____10340 = lookup_qname env lid0 in
        match uu____10340 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10371);
                FStar_Syntax_Syntax.sigrng = uu____10372;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10374;
                FStar_Syntax_Syntax.sigattrs = uu____10375;_},FStar_Pervasives_Native.None
              ),uu____10376)
            ->
            let lid1 =
              let uu____10430 =
                let uu____10431 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10431 in
              FStar_Ident.set_lid_range lid uu____10430 in
            let uu____10432 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___134_10436  ->
                      match uu___134_10436 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10437 -> false)) in
            if uu____10432
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10451 =
                      let uu____10452 =
                        let uu____10453 = get_range env in
                        FStar_Range.string_of_range uu____10453 in
                      let uu____10454 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10455 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10452 uu____10454 uu____10455 in
                    failwith uu____10451) in
               match (binders, univs1) with
               | ([],uu____10462) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10479,uu____10480::uu____10481::uu____10482) ->
                   let uu____10487 =
                     let uu____10488 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10489 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10488 uu____10489 in
                   failwith uu____10487
               | uu____10496 ->
                   let uu____10501 =
                     let uu____10506 =
                       let uu____10507 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10507) in
                     inst_tscheme_with uu____10506 insts in
                   (match uu____10501 with
                    | (uu____10518,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10521 =
                          let uu____10522 = FStar_Syntax_Subst.compress t1 in
                          uu____10522.FStar_Syntax_Syntax.n in
                        (match uu____10521 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10569 -> failwith "Impossible")))
        | uu____10576 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10618 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10618 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10631,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10638 = find1 l2 in
            (match uu____10638 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10645 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10645 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10649 = find1 l in
            (match uu____10649 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10665 = lookup_qname env l1 in
      match uu____10665 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10688;
              FStar_Syntax_Syntax.sigrng = uu____10689;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10691;
              FStar_Syntax_Syntax.sigattrs = uu____10692;_},uu____10693),uu____10694)
          -> q
      | uu____10745 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10781 =
          let uu____10782 =
            let uu____10783 = FStar_Util.string_of_int i in
            let uu____10784 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10783 uu____10784 in
          failwith uu____10782 in
        let uu____10785 = lookup_datacon env lid in
        match uu____10785 with
        | (uu____10790,t) ->
            let uu____10792 =
              let uu____10793 = FStar_Syntax_Subst.compress t in
              uu____10793.FStar_Syntax_Syntax.n in
            (match uu____10792 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10797) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10828 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10828
                      FStar_Pervasives_Native.fst)
             | uu____10837 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10846 = lookup_qname env l in
      match uu____10846 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10867,uu____10868,uu____10869);
              FStar_Syntax_Syntax.sigrng = uu____10870;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10872;
              FStar_Syntax_Syntax.sigattrs = uu____10873;_},uu____10874),uu____10875)
          ->
          FStar_Util.for_some
            (fun uu___135_10928  ->
               match uu___135_10928 with
               | FStar_Syntax_Syntax.Projector uu____10929 -> true
               | uu____10934 -> false) quals
      | uu____10935 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10964 = lookup_qname env lid in
      match uu____10964 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10985,uu____10986,uu____10987,uu____10988,uu____10989,uu____10990);
              FStar_Syntax_Syntax.sigrng = uu____10991;
              FStar_Syntax_Syntax.sigquals = uu____10992;
              FStar_Syntax_Syntax.sigmeta = uu____10993;
              FStar_Syntax_Syntax.sigattrs = uu____10994;_},uu____10995),uu____10996)
          -> true
      | uu____11051 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11080 = lookup_qname env lid in
      match uu____11080 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11101,uu____11102,uu____11103,uu____11104,uu____11105,uu____11106);
              FStar_Syntax_Syntax.sigrng = uu____11107;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11109;
              FStar_Syntax_Syntax.sigattrs = uu____11110;_},uu____11111),uu____11112)
          ->
          FStar_Util.for_some
            (fun uu___136_11173  ->
               match uu___136_11173 with
               | FStar_Syntax_Syntax.RecordType uu____11174 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11183 -> true
               | uu____11192 -> false) quals
      | uu____11193 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11222 = lookup_qname env lid in
      match uu____11222 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11243,uu____11244);
              FStar_Syntax_Syntax.sigrng = uu____11245;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11247;
              FStar_Syntax_Syntax.sigattrs = uu____11248;_},uu____11249),uu____11250)
          ->
          FStar_Util.for_some
            (fun uu___137_11307  ->
               match uu___137_11307 with
               | FStar_Syntax_Syntax.Action uu____11308 -> true
               | uu____11309 -> false) quals
      | uu____11310 -> false
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
      let uu____11342 =
        let uu____11343 = FStar_Syntax_Util.un_uinst head1 in
        uu____11343.FStar_Syntax_Syntax.n in
      match uu____11342 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11347 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11414 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11430) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11447 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11454 ->
                 FStar_Pervasives_Native.Some true
             | uu____11471 -> FStar_Pervasives_Native.Some false) in
      let uu____11472 =
        let uu____11475 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11475 mapper in
      match uu____11472 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11523 = lookup_qname env lid in
      match uu____11523 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11544,uu____11545,tps,uu____11547,uu____11548,uu____11549);
              FStar_Syntax_Syntax.sigrng = uu____11550;
              FStar_Syntax_Syntax.sigquals = uu____11551;
              FStar_Syntax_Syntax.sigmeta = uu____11552;
              FStar_Syntax_Syntax.sigattrs = uu____11553;_},uu____11554),uu____11555)
          -> FStar_List.length tps
      | uu____11618 ->
          let uu____11639 =
            let uu____11640 =
              let uu____11645 = name_not_found lid in
              (uu____11645, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11640 in
          FStar_Exn.raise uu____11639
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
           (fun uu____11687  ->
              match uu____11687 with
              | (d,uu____11695) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11708 = effect_decl_opt env l in
      match uu____11708 with
      | FStar_Pervasives_Native.None  ->
          let uu____11723 =
            let uu____11724 =
              let uu____11729 = name_not_found l in
              (uu____11729, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11724 in
          FStar_Exn.raise uu____11723
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
            (let uu____11795 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11848  ->
                       match uu____11848 with
                       | (m1,m2,uu____11861,uu____11862,uu____11863) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11795 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11880 =
                   let uu____11881 =
                     let uu____11886 =
                       let uu____11887 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11888 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11887
                         uu____11888 in
                     (uu____11886, (env.range)) in
                   FStar_Errors.Error uu____11881 in
                 FStar_Exn.raise uu____11880
             | FStar_Pervasives_Native.Some
                 (uu____11895,uu____11896,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11939 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11939)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11966 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11992  ->
                match uu____11992 with
                | (d,uu____11998) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11966 with
      | FStar_Pervasives_Native.None  ->
          let uu____12009 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12009
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12022 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12022 with
           | (uu____12033,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12043)::(wp,uu____12045)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12081 -> failwith "Impossible"))
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
                 let uu____12130 = get_range env in
                 let uu____12131 =
                   let uu____12134 =
                     let uu____12135 =
                       let uu____12150 =
                         let uu____12153 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12153] in
                       (null_wp, uu____12150) in
                     FStar_Syntax_Syntax.Tm_app uu____12135 in
                   FStar_Syntax_Syntax.mk uu____12134 in
                 uu____12131 FStar_Pervasives_Native.None uu____12130 in
               let uu____12159 =
                 let uu____12160 =
                   let uu____12169 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12169] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12160;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12159)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___150_12180 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___150_12180.order);
              joins = (uu___150_12180.joins)
            } in
          let uu___151_12189 = env in
          {
            solver = (uu___151_12189.solver);
            range = (uu___151_12189.range);
            curmodule = (uu___151_12189.curmodule);
            gamma = (uu___151_12189.gamma);
            gamma_cache = (uu___151_12189.gamma_cache);
            modules = (uu___151_12189.modules);
            expected_typ = (uu___151_12189.expected_typ);
            sigtab = (uu___151_12189.sigtab);
            is_pattern = (uu___151_12189.is_pattern);
            instantiate_imp = (uu___151_12189.instantiate_imp);
            effects;
            generalize = (uu___151_12189.generalize);
            letrecs = (uu___151_12189.letrecs);
            top_level = (uu___151_12189.top_level);
            check_uvars = (uu___151_12189.check_uvars);
            use_eq = (uu___151_12189.use_eq);
            is_iface = (uu___151_12189.is_iface);
            admit = (uu___151_12189.admit);
            lax = (uu___151_12189.lax);
            lax_universes = (uu___151_12189.lax_universes);
            failhard = (uu___151_12189.failhard);
            nosynth = (uu___151_12189.nosynth);
            tc_term = (uu___151_12189.tc_term);
            type_of = (uu___151_12189.type_of);
            universe_of = (uu___151_12189.universe_of);
            use_bv_sorts = (uu___151_12189.use_bv_sorts);
            qname_and_index = (uu___151_12189.qname_and_index);
            proof_ns = (uu___151_12189.proof_ns);
            synth = (uu___151_12189.synth);
            is_native_tactic = (uu___151_12189.is_native_tactic);
            identifier_info = (uu___151_12189.identifier_info);
            tc_hooks = (uu___151_12189.tc_hooks);
            dsenv = (uu___151_12189.dsenv)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12206 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12206 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12296 = (e1.mlift).mlift_wp t wp in
                              let uu____12297 = l1 t wp e in
                              l2 t uu____12296 uu____12297))
                | uu____12298 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12337 = inst_tscheme lift_t in
            match uu____12337 with
            | (uu____12344,lift_t1) ->
                let uu____12346 =
                  let uu____12349 =
                    let uu____12350 =
                      let uu____12365 =
                        let uu____12368 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12369 =
                          let uu____12372 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12372] in
                        uu____12368 :: uu____12369 in
                      (lift_t1, uu____12365) in
                    FStar_Syntax_Syntax.Tm_app uu____12350 in
                  FStar_Syntax_Syntax.mk uu____12349 in
                uu____12346 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12413 = inst_tscheme lift_t in
            match uu____12413 with
            | (uu____12420,lift_t1) ->
                let uu____12422 =
                  let uu____12425 =
                    let uu____12426 =
                      let uu____12441 =
                        let uu____12444 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12445 =
                          let uu____12448 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12449 =
                            let uu____12452 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12452] in
                          uu____12448 :: uu____12449 in
                        uu____12444 :: uu____12445 in
                      (lift_t1, uu____12441) in
                    FStar_Syntax_Syntax.Tm_app uu____12426 in
                  FStar_Syntax_Syntax.mk uu____12425 in
                uu____12422 FStar_Pervasives_Native.None
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
              let uu____12490 =
                let uu____12491 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12491
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12490 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12495 =
              let uu____12496 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12496 in
            let uu____12497 =
              let uu____12498 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12516 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12516) in
              FStar_Util.dflt "none" uu____12498 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12495
              uu____12497 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12542  ->
                    match uu____12542 with
                    | (e,uu____12550) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12569 =
            match uu____12569 with
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
              let uu____12607 =
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
                                    (let uu____12628 =
                                       let uu____12637 =
                                         find_edge order1 (i, k) in
                                       let uu____12640 =
                                         find_edge order1 (k, j) in
                                       (uu____12637, uu____12640) in
                                     match uu____12628 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12655 =
                                           compose_edges e1 e2 in
                                         [uu____12655]
                                     | uu____12656 -> []))))) in
              FStar_List.append order1 uu____12607 in
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
                   let uu____12685 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12687 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12687
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12685
                   then
                     let uu____12692 =
                       let uu____12693 =
                         let uu____12698 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12699 = get_range env in
                         (uu____12698, uu____12699) in
                       FStar_Errors.Error uu____12693 in
                     FStar_Exn.raise uu____12692
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
                                            let uu____12824 =
                                              let uu____12833 =
                                                find_edge order2 (i, k) in
                                              let uu____12836 =
                                                find_edge order2 (j, k) in
                                              (uu____12833, uu____12836) in
                                            match uu____12824 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12878,uu____12879)
                                                     ->
                                                     let uu____12886 =
                                                       let uu____12891 =
                                                         let uu____12892 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12892 in
                                                       let uu____12895 =
                                                         let uu____12896 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12896 in
                                                       (uu____12891,
                                                         uu____12895) in
                                                     (match uu____12886 with
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
                                            | uu____12931 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___152_13004 = env.effects in
              { decls = (uu___152_13004.decls); order = order2; joins } in
            let uu___153_13005 = env in
            {
              solver = (uu___153_13005.solver);
              range = (uu___153_13005.range);
              curmodule = (uu___153_13005.curmodule);
              gamma = (uu___153_13005.gamma);
              gamma_cache = (uu___153_13005.gamma_cache);
              modules = (uu___153_13005.modules);
              expected_typ = (uu___153_13005.expected_typ);
              sigtab = (uu___153_13005.sigtab);
              is_pattern = (uu___153_13005.is_pattern);
              instantiate_imp = (uu___153_13005.instantiate_imp);
              effects;
              generalize = (uu___153_13005.generalize);
              letrecs = (uu___153_13005.letrecs);
              top_level = (uu___153_13005.top_level);
              check_uvars = (uu___153_13005.check_uvars);
              use_eq = (uu___153_13005.use_eq);
              is_iface = (uu___153_13005.is_iface);
              admit = (uu___153_13005.admit);
              lax = (uu___153_13005.lax);
              lax_universes = (uu___153_13005.lax_universes);
              failhard = (uu___153_13005.failhard);
              nosynth = (uu___153_13005.nosynth);
              tc_term = (uu___153_13005.tc_term);
              type_of = (uu___153_13005.type_of);
              universe_of = (uu___153_13005.universe_of);
              use_bv_sorts = (uu___153_13005.use_bv_sorts);
              qname_and_index = (uu___153_13005.qname_and_index);
              proof_ns = (uu___153_13005.proof_ns);
              synth = (uu___153_13005.synth);
              is_native_tactic = (uu___153_13005.is_native_tactic);
              identifier_info = (uu___153_13005.identifier_info);
              tc_hooks = (uu___153_13005.tc_hooks);
              dsenv = (uu___153_13005.dsenv)
            }))
      | uu____13006 -> env
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
        | uu____13032 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13042 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13042 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13059 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13059 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13077 =
                     let uu____13078 =
                       let uu____13083 =
                         let uu____13084 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13089 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13096 =
                           let uu____13097 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13097 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13084 uu____13089 uu____13096 in
                       (uu____13083, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13078 in
                   FStar_Exn.raise uu____13077)
                else ();
                (let inst1 =
                   let uu____13102 =
                     let uu____13111 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13111 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13128  ->
                        fun uu____13129  ->
                          match (uu____13128, uu____13129) with
                          | ((x,uu____13151),(t,uu____13153)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13102 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13172 =
                     let uu___154_13173 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___154_13173.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___154_13173.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___154_13173.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___154_13173.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13172
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
          let uu____13199 = effect_decl_opt env effect_name in
          match uu____13199 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13232 =
                only_reifiable &&
                  (let uu____13234 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13234) in
              if uu____13232
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13250 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13269 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13298 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13298
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13299 =
                             let uu____13300 =
                               let uu____13305 = get_range env in
                               (message, uu____13305) in
                             FStar_Errors.Error uu____13300 in
                           FStar_Exn.raise uu____13299 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13315 =
                       let uu____13318 = get_range env in
                       let uu____13319 =
                         let uu____13322 =
                           let uu____13323 =
                             let uu____13338 =
                               let uu____13341 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13341; wp] in
                             (repr, uu____13338) in
                           FStar_Syntax_Syntax.Tm_app uu____13323 in
                         FStar_Syntax_Syntax.mk uu____13322 in
                       uu____13319 FStar_Pervasives_Native.None uu____13318 in
                     FStar_Pervasives_Native.Some uu____13315)
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
          let uu____13393 =
            let uu____13394 =
              let uu____13399 =
                let uu____13400 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13400 in
              let uu____13401 = get_range env in (uu____13399, uu____13401) in
            FStar_Errors.Error uu____13394 in
          FStar_Exn.raise uu____13393 in
        let uu____13402 = effect_repr_aux true env c u_c in
        match uu____13402 with
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
      | uu____13442 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13451 =
        let uu____13452 = FStar_Syntax_Subst.compress t in
        uu____13452.FStar_Syntax_Syntax.n in
      match uu____13451 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13455,c) ->
          is_reifiable_comp env c
      | uu____13473 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13497)::uu____13498 -> x :: rest
        | (Binding_sig_inst uu____13507)::uu____13508 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13523 = push1 x rest1 in local :: uu____13523 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___155_13527 = env in
       let uu____13528 = push1 s env.gamma in
       {
         solver = (uu___155_13527.solver);
         range = (uu___155_13527.range);
         curmodule = (uu___155_13527.curmodule);
         gamma = uu____13528;
         gamma_cache = (uu___155_13527.gamma_cache);
         modules = (uu___155_13527.modules);
         expected_typ = (uu___155_13527.expected_typ);
         sigtab = (uu___155_13527.sigtab);
         is_pattern = (uu___155_13527.is_pattern);
         instantiate_imp = (uu___155_13527.instantiate_imp);
         effects = (uu___155_13527.effects);
         generalize = (uu___155_13527.generalize);
         letrecs = (uu___155_13527.letrecs);
         top_level = (uu___155_13527.top_level);
         check_uvars = (uu___155_13527.check_uvars);
         use_eq = (uu___155_13527.use_eq);
         is_iface = (uu___155_13527.is_iface);
         admit = (uu___155_13527.admit);
         lax = (uu___155_13527.lax);
         lax_universes = (uu___155_13527.lax_universes);
         failhard = (uu___155_13527.failhard);
         nosynth = (uu___155_13527.nosynth);
         tc_term = (uu___155_13527.tc_term);
         type_of = (uu___155_13527.type_of);
         universe_of = (uu___155_13527.universe_of);
         use_bv_sorts = (uu___155_13527.use_bv_sorts);
         qname_and_index = (uu___155_13527.qname_and_index);
         proof_ns = (uu___155_13527.proof_ns);
         synth = (uu___155_13527.synth);
         is_native_tactic = (uu___155_13527.is_native_tactic);
         identifier_info = (uu___155_13527.identifier_info);
         tc_hooks = (uu___155_13527.tc_hooks);
         dsenv = (uu___155_13527.dsenv)
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
      let uu___156_13565 = env in
      {
        solver = (uu___156_13565.solver);
        range = (uu___156_13565.range);
        curmodule = (uu___156_13565.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___156_13565.gamma_cache);
        modules = (uu___156_13565.modules);
        expected_typ = (uu___156_13565.expected_typ);
        sigtab = (uu___156_13565.sigtab);
        is_pattern = (uu___156_13565.is_pattern);
        instantiate_imp = (uu___156_13565.instantiate_imp);
        effects = (uu___156_13565.effects);
        generalize = (uu___156_13565.generalize);
        letrecs = (uu___156_13565.letrecs);
        top_level = (uu___156_13565.top_level);
        check_uvars = (uu___156_13565.check_uvars);
        use_eq = (uu___156_13565.use_eq);
        is_iface = (uu___156_13565.is_iface);
        admit = (uu___156_13565.admit);
        lax = (uu___156_13565.lax);
        lax_universes = (uu___156_13565.lax_universes);
        failhard = (uu___156_13565.failhard);
        nosynth = (uu___156_13565.nosynth);
        tc_term = (uu___156_13565.tc_term);
        type_of = (uu___156_13565.type_of);
        universe_of = (uu___156_13565.universe_of);
        use_bv_sorts = (uu___156_13565.use_bv_sorts);
        qname_and_index = (uu___156_13565.qname_and_index);
        proof_ns = (uu___156_13565.proof_ns);
        synth = (uu___156_13565.synth);
        is_native_tactic = (uu___156_13565.is_native_tactic);
        identifier_info = (uu___156_13565.identifier_info);
        tc_hooks = (uu___156_13565.tc_hooks);
        dsenv = (uu___156_13565.dsenv)
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
            (let uu___157_13599 = env in
             {
               solver = (uu___157_13599.solver);
               range = (uu___157_13599.range);
               curmodule = (uu___157_13599.curmodule);
               gamma = rest;
               gamma_cache = (uu___157_13599.gamma_cache);
               modules = (uu___157_13599.modules);
               expected_typ = (uu___157_13599.expected_typ);
               sigtab = (uu___157_13599.sigtab);
               is_pattern = (uu___157_13599.is_pattern);
               instantiate_imp = (uu___157_13599.instantiate_imp);
               effects = (uu___157_13599.effects);
               generalize = (uu___157_13599.generalize);
               letrecs = (uu___157_13599.letrecs);
               top_level = (uu___157_13599.top_level);
               check_uvars = (uu___157_13599.check_uvars);
               use_eq = (uu___157_13599.use_eq);
               is_iface = (uu___157_13599.is_iface);
               admit = (uu___157_13599.admit);
               lax = (uu___157_13599.lax);
               lax_universes = (uu___157_13599.lax_universes);
               failhard = (uu___157_13599.failhard);
               nosynth = (uu___157_13599.nosynth);
               tc_term = (uu___157_13599.tc_term);
               type_of = (uu___157_13599.type_of);
               universe_of = (uu___157_13599.universe_of);
               use_bv_sorts = (uu___157_13599.use_bv_sorts);
               qname_and_index = (uu___157_13599.qname_and_index);
               proof_ns = (uu___157_13599.proof_ns);
               synth = (uu___157_13599.synth);
               is_native_tactic = (uu___157_13599.is_native_tactic);
               identifier_info = (uu___157_13599.identifier_info);
               tc_hooks = (uu___157_13599.tc_hooks);
               dsenv = (uu___157_13599.dsenv)
             }))
    | uu____13600 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13624  ->
             match uu____13624 with | (x,uu____13630) -> push_bv env1 x) env
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
            let uu___158_13660 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___158_13660.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___158_13660.FStar_Syntax_Syntax.index);
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
      (let uu___159_13695 = env in
       {
         solver = (uu___159_13695.solver);
         range = (uu___159_13695.range);
         curmodule = (uu___159_13695.curmodule);
         gamma = [];
         gamma_cache = (uu___159_13695.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___159_13695.sigtab);
         is_pattern = (uu___159_13695.is_pattern);
         instantiate_imp = (uu___159_13695.instantiate_imp);
         effects = (uu___159_13695.effects);
         generalize = (uu___159_13695.generalize);
         letrecs = (uu___159_13695.letrecs);
         top_level = (uu___159_13695.top_level);
         check_uvars = (uu___159_13695.check_uvars);
         use_eq = (uu___159_13695.use_eq);
         is_iface = (uu___159_13695.is_iface);
         admit = (uu___159_13695.admit);
         lax = (uu___159_13695.lax);
         lax_universes = (uu___159_13695.lax_universes);
         failhard = (uu___159_13695.failhard);
         nosynth = (uu___159_13695.nosynth);
         tc_term = (uu___159_13695.tc_term);
         type_of = (uu___159_13695.type_of);
         universe_of = (uu___159_13695.universe_of);
         use_bv_sorts = (uu___159_13695.use_bv_sorts);
         qname_and_index = (uu___159_13695.qname_and_index);
         proof_ns = (uu___159_13695.proof_ns);
         synth = (uu___159_13695.synth);
         is_native_tactic = (uu___159_13695.is_native_tactic);
         identifier_info = (uu___159_13695.identifier_info);
         tc_hooks = (uu___159_13695.tc_hooks);
         dsenv = (uu___159_13695.dsenv)
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
        let uu____13732 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13732 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13760 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13760)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___160_13775 = env in
      {
        solver = (uu___160_13775.solver);
        range = (uu___160_13775.range);
        curmodule = (uu___160_13775.curmodule);
        gamma = (uu___160_13775.gamma);
        gamma_cache = (uu___160_13775.gamma_cache);
        modules = (uu___160_13775.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___160_13775.sigtab);
        is_pattern = (uu___160_13775.is_pattern);
        instantiate_imp = (uu___160_13775.instantiate_imp);
        effects = (uu___160_13775.effects);
        generalize = (uu___160_13775.generalize);
        letrecs = (uu___160_13775.letrecs);
        top_level = (uu___160_13775.top_level);
        check_uvars = (uu___160_13775.check_uvars);
        use_eq = false;
        is_iface = (uu___160_13775.is_iface);
        admit = (uu___160_13775.admit);
        lax = (uu___160_13775.lax);
        lax_universes = (uu___160_13775.lax_universes);
        failhard = (uu___160_13775.failhard);
        nosynth = (uu___160_13775.nosynth);
        tc_term = (uu___160_13775.tc_term);
        type_of = (uu___160_13775.type_of);
        universe_of = (uu___160_13775.universe_of);
        use_bv_sorts = (uu___160_13775.use_bv_sorts);
        qname_and_index = (uu___160_13775.qname_and_index);
        proof_ns = (uu___160_13775.proof_ns);
        synth = (uu___160_13775.synth);
        is_native_tactic = (uu___160_13775.is_native_tactic);
        identifier_info = (uu___160_13775.identifier_info);
        tc_hooks = (uu___160_13775.tc_hooks);
        dsenv = (uu___160_13775.dsenv)
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
    let uu____13801 = expected_typ env_ in
    ((let uu___161_13807 = env_ in
      {
        solver = (uu___161_13807.solver);
        range = (uu___161_13807.range);
        curmodule = (uu___161_13807.curmodule);
        gamma = (uu___161_13807.gamma);
        gamma_cache = (uu___161_13807.gamma_cache);
        modules = (uu___161_13807.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___161_13807.sigtab);
        is_pattern = (uu___161_13807.is_pattern);
        instantiate_imp = (uu___161_13807.instantiate_imp);
        effects = (uu___161_13807.effects);
        generalize = (uu___161_13807.generalize);
        letrecs = (uu___161_13807.letrecs);
        top_level = (uu___161_13807.top_level);
        check_uvars = (uu___161_13807.check_uvars);
        use_eq = false;
        is_iface = (uu___161_13807.is_iface);
        admit = (uu___161_13807.admit);
        lax = (uu___161_13807.lax);
        lax_universes = (uu___161_13807.lax_universes);
        failhard = (uu___161_13807.failhard);
        nosynth = (uu___161_13807.nosynth);
        tc_term = (uu___161_13807.tc_term);
        type_of = (uu___161_13807.type_of);
        universe_of = (uu___161_13807.universe_of);
        use_bv_sorts = (uu___161_13807.use_bv_sorts);
        qname_and_index = (uu___161_13807.qname_and_index);
        proof_ns = (uu___161_13807.proof_ns);
        synth = (uu___161_13807.synth);
        is_native_tactic = (uu___161_13807.is_native_tactic);
        identifier_info = (uu___161_13807.identifier_info);
        tc_hooks = (uu___161_13807.tc_hooks);
        dsenv = (uu___161_13807.dsenv)
      }), uu____13801)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13822 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___138_13832  ->
                    match uu___138_13832 with
                    | Binding_sig (uu____13835,se) -> [se]
                    | uu____13841 -> [])) in
          FStar_All.pipe_right uu____13822 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___162_13848 = env in
       {
         solver = (uu___162_13848.solver);
         range = (uu___162_13848.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___162_13848.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___162_13848.expected_typ);
         sigtab = (uu___162_13848.sigtab);
         is_pattern = (uu___162_13848.is_pattern);
         instantiate_imp = (uu___162_13848.instantiate_imp);
         effects = (uu___162_13848.effects);
         generalize = (uu___162_13848.generalize);
         letrecs = (uu___162_13848.letrecs);
         top_level = (uu___162_13848.top_level);
         check_uvars = (uu___162_13848.check_uvars);
         use_eq = (uu___162_13848.use_eq);
         is_iface = (uu___162_13848.is_iface);
         admit = (uu___162_13848.admit);
         lax = (uu___162_13848.lax);
         lax_universes = (uu___162_13848.lax_universes);
         failhard = (uu___162_13848.failhard);
         nosynth = (uu___162_13848.nosynth);
         tc_term = (uu___162_13848.tc_term);
         type_of = (uu___162_13848.type_of);
         universe_of = (uu___162_13848.universe_of);
         use_bv_sorts = (uu___162_13848.use_bv_sorts);
         qname_and_index = (uu___162_13848.qname_and_index);
         proof_ns = (uu___162_13848.proof_ns);
         synth = (uu___162_13848.synth);
         is_native_tactic = (uu___162_13848.is_native_tactic);
         identifier_info = (uu___162_13848.identifier_info);
         tc_hooks = (uu___162_13848.tc_hooks);
         dsenv = (uu___162_13848.dsenv)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13930)::tl1 -> aux out tl1
      | (Binding_lid (uu____13934,(uu____13935,t)))::tl1 ->
          let uu____13950 =
            let uu____13957 = FStar_Syntax_Free.uvars t in
            ext out uu____13957 in
          aux uu____13950 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13964;
            FStar_Syntax_Syntax.index = uu____13965;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13972 =
            let uu____13979 = FStar_Syntax_Free.uvars t in
            ext out uu____13979 in
          aux uu____13972 tl1
      | (Binding_sig uu____13986)::uu____13987 -> out
      | (Binding_sig_inst uu____13996)::uu____13997 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14053)::tl1 -> aux out tl1
      | (Binding_univ uu____14065)::tl1 -> aux out tl1
      | (Binding_lid (uu____14069,(uu____14070,t)))::tl1 ->
          let uu____14085 =
            let uu____14088 = FStar_Syntax_Free.univs t in
            ext out uu____14088 in
          aux uu____14085 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14091;
            FStar_Syntax_Syntax.index = uu____14092;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14099 =
            let uu____14102 = FStar_Syntax_Free.univs t in
            ext out uu____14102 in
          aux uu____14099 tl1
      | (Binding_sig uu____14105)::uu____14106 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14160)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14176 = FStar_Util.fifo_set_add uname out in
          aux uu____14176 tl1
      | (Binding_lid (uu____14179,(uu____14180,t)))::tl1 ->
          let uu____14195 =
            let uu____14198 = FStar_Syntax_Free.univnames t in
            ext out uu____14198 in
          aux uu____14195 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14201;
            FStar_Syntax_Syntax.index = uu____14202;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14209 =
            let uu____14212 = FStar_Syntax_Free.univnames t in
            ext out uu____14212 in
          aux uu____14209 tl1
      | (Binding_sig uu____14215)::uu____14216 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___139_14241  ->
            match uu___139_14241 with
            | Binding_var x -> [x]
            | Binding_lid uu____14245 -> []
            | Binding_sig uu____14250 -> []
            | Binding_univ uu____14257 -> []
            | Binding_sig_inst uu____14258 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14275 =
      let uu____14278 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14278
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14275 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14303 =
      let uu____14304 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___140_14314  ->
                match uu___140_14314 with
                | Binding_var x ->
                    let uu____14316 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14316
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14319) ->
                    let uu____14320 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14320
                | Binding_sig (ls,uu____14322) ->
                    let uu____14327 =
                      let uu____14328 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14328
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14327
                | Binding_sig_inst (ls,uu____14338,uu____14339) ->
                    let uu____14344 =
                      let uu____14345 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14345
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14344)) in
      FStar_All.pipe_right uu____14304 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14303 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14364 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14364
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14392  ->
                 fun uu____14393  ->
                   match (uu____14392, uu____14393) with
                   | ((b1,uu____14411),(b2,uu____14413)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___141_14460  ->
    match uu___141_14460 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14461 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___142_14480  ->
             match uu___142_14480 with
             | Binding_sig (lids,uu____14486) -> FStar_List.append lids keys
             | uu____14491 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14497  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14533) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14552,uu____14553) -> false in
      FStar_Util.for_some
        (fun uu____14571  ->
           match uu____14571 with | (p,b) -> b && (list_prefix p path))
        env.proof_ns
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14592 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14592
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___163_14607 = e in
        {
          solver = (uu___163_14607.solver);
          range = (uu___163_14607.range);
          curmodule = (uu___163_14607.curmodule);
          gamma = (uu___163_14607.gamma);
          gamma_cache = (uu___163_14607.gamma_cache);
          modules = (uu___163_14607.modules);
          expected_typ = (uu___163_14607.expected_typ);
          sigtab = (uu___163_14607.sigtab);
          is_pattern = (uu___163_14607.is_pattern);
          instantiate_imp = (uu___163_14607.instantiate_imp);
          effects = (uu___163_14607.effects);
          generalize = (uu___163_14607.generalize);
          letrecs = (uu___163_14607.letrecs);
          top_level = (uu___163_14607.top_level);
          check_uvars = (uu___163_14607.check_uvars);
          use_eq = (uu___163_14607.use_eq);
          is_iface = (uu___163_14607.is_iface);
          admit = (uu___163_14607.admit);
          lax = (uu___163_14607.lax);
          lax_universes = (uu___163_14607.lax_universes);
          failhard = (uu___163_14607.failhard);
          nosynth = (uu___163_14607.nosynth);
          tc_term = (uu___163_14607.tc_term);
          type_of = (uu___163_14607.type_of);
          universe_of = (uu___163_14607.universe_of);
          use_bv_sorts = (uu___163_14607.use_bv_sorts);
          qname_and_index = (uu___163_14607.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___163_14607.synth);
          is_native_tactic = (uu___163_14607.is_native_tactic);
          identifier_info = (uu___163_14607.identifier_info);
          tc_hooks = (uu___163_14607.tc_hooks);
          dsenv = (uu___163_14607.dsenv)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___164_14640 = e in
      {
        solver = (uu___164_14640.solver);
        range = (uu___164_14640.range);
        curmodule = (uu___164_14640.curmodule);
        gamma = (uu___164_14640.gamma);
        gamma_cache = (uu___164_14640.gamma_cache);
        modules = (uu___164_14640.modules);
        expected_typ = (uu___164_14640.expected_typ);
        sigtab = (uu___164_14640.sigtab);
        is_pattern = (uu___164_14640.is_pattern);
        instantiate_imp = (uu___164_14640.instantiate_imp);
        effects = (uu___164_14640.effects);
        generalize = (uu___164_14640.generalize);
        letrecs = (uu___164_14640.letrecs);
        top_level = (uu___164_14640.top_level);
        check_uvars = (uu___164_14640.check_uvars);
        use_eq = (uu___164_14640.use_eq);
        is_iface = (uu___164_14640.is_iface);
        admit = (uu___164_14640.admit);
        lax = (uu___164_14640.lax);
        lax_universes = (uu___164_14640.lax_universes);
        failhard = (uu___164_14640.failhard);
        nosynth = (uu___164_14640.nosynth);
        tc_term = (uu___164_14640.tc_term);
        type_of = (uu___164_14640.type_of);
        universe_of = (uu___164_14640.universe_of);
        use_bv_sorts = (uu___164_14640.use_bv_sorts);
        qname_and_index = (uu___164_14640.qname_and_index);
        proof_ns = ns;
        synth = (uu___164_14640.synth);
        is_native_tactic = (uu___164_14640.is_native_tactic);
        identifier_info = (uu___164_14640.identifier_info);
        tc_hooks = (uu___164_14640.tc_hooks);
        dsenv = (uu___164_14640.dsenv)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14654 =
      match uu____14654 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14670 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14670) in
    let uu____14672 = FStar_List.map aux env.proof_ns in
    FStar_All.pipe_right uu____14672 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14685  -> ());
    push = (fun uu____14687  -> ());
    pop = (fun uu____14689  -> ());
    encode_modul = (fun uu____14692  -> fun uu____14693  -> ());
    encode_sig = (fun uu____14696  -> fun uu____14697  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14703 =
             let uu____14710 = FStar_Options.peek () in (e, g, uu____14710) in
           [uu____14703]);
    solve = (fun uu____14726  -> fun uu____14727  -> fun uu____14728  -> ());
    finish = (fun uu____14734  -> ());
    refresh = (fun uu____14736  -> ())
  }