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
           (fun uu___132_4931  ->
              match uu___132_4931 with
              | Binding_var x ->
                  let y =
                    let uu____4934 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____4934 in
                  let uu____4935 =
                    let uu____4936 = FStar_Syntax_Subst.compress y in
                    uu____4936.FStar_Syntax_Syntax.n in
                  (match uu____4935 with
                   | FStar_Syntax_Syntax.Tm_name y1 -> Binding_var y1
                   | uu____4940 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___146_4950 = env in
      let uu____4951 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___146_4950.solver);
        range = (uu___146_4950.range);
        curmodule = (uu___146_4950.curmodule);
        gamma = uu____4951;
        gamma_cache = (uu___146_4950.gamma_cache);
        modules = (uu___146_4950.modules);
        expected_typ = (uu___146_4950.expected_typ);
        sigtab = (uu___146_4950.sigtab);
        is_pattern = (uu___146_4950.is_pattern);
        instantiate_imp = (uu___146_4950.instantiate_imp);
        effects = (uu___146_4950.effects);
        generalize = (uu___146_4950.generalize);
        letrecs = (uu___146_4950.letrecs);
        top_level = (uu___146_4950.top_level);
        check_uvars = (uu___146_4950.check_uvars);
        use_eq = (uu___146_4950.use_eq);
        is_iface = (uu___146_4950.is_iface);
        admit = (uu___146_4950.admit);
        lax = (uu___146_4950.lax);
        lax_universes = (uu___146_4950.lax_universes);
        failhard = (uu___146_4950.failhard);
        nosynth = (uu___146_4950.nosynth);
        tc_term = (uu___146_4950.tc_term);
        type_of = (uu___146_4950.type_of);
        universe_of = (uu___146_4950.universe_of);
        use_bv_sorts = (uu___146_4950.use_bv_sorts);
        qname_and_index = (uu___146_4950.qname_and_index);
        proof_ns = (uu___146_4950.proof_ns);
        synth = (uu___146_4950.synth);
        is_native_tactic = (uu___146_4950.is_native_tactic);
        identifier_info = (uu___146_4950.identifier_info);
        tc_hooks = (uu___146_4950.tc_hooks);
        dsenv = (uu___146_4950.dsenv)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4958  -> fun uu____4959  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___147_4972 = env in
      {
        solver = (uu___147_4972.solver);
        range = (uu___147_4972.range);
        curmodule = (uu___147_4972.curmodule);
        gamma = (uu___147_4972.gamma);
        gamma_cache = (uu___147_4972.gamma_cache);
        modules = (uu___147_4972.modules);
        expected_typ = (uu___147_4972.expected_typ);
        sigtab = (uu___147_4972.sigtab);
        is_pattern = (uu___147_4972.is_pattern);
        instantiate_imp = (uu___147_4972.instantiate_imp);
        effects = (uu___147_4972.effects);
        generalize = (uu___147_4972.generalize);
        letrecs = (uu___147_4972.letrecs);
        top_level = (uu___147_4972.top_level);
        check_uvars = (uu___147_4972.check_uvars);
        use_eq = (uu___147_4972.use_eq);
        is_iface = (uu___147_4972.is_iface);
        admit = (uu___147_4972.admit);
        lax = (uu___147_4972.lax);
        lax_universes = (uu___147_4972.lax_universes);
        failhard = (uu___147_4972.failhard);
        nosynth = (uu___147_4972.nosynth);
        tc_term = (uu___147_4972.tc_term);
        type_of = (uu___147_4972.type_of);
        universe_of = (uu___147_4972.universe_of);
        use_bv_sorts = (uu___147_4972.use_bv_sorts);
        qname_and_index = (uu___147_4972.qname_and_index);
        proof_ns = (uu___147_4972.proof_ns);
        synth = (uu___147_4972.synth);
        is_native_tactic = (uu___147_4972.is_native_tactic);
        identifier_info = (uu___147_4972.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___147_4972.dsenv)
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
      | (NoDelta ,uu____4987) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4988,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4989,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4990 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4999 . Prims.unit -> 'Auu____4999 FStar_Util.smap =
  fun uu____5005  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5010 . Prims.unit -> 'Auu____5010 FStar_Util.smap =
  fun uu____5016  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____5091 = new_gamma_cache () in
            let uu____5094 = new_sigtab () in
            let uu____5097 = FStar_Options.using_facts_from () in
            let uu____5098 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            let uu____5101 = FStar_ToSyntax_Env.empty_env () in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____5091;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____5094;
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
              proof_ns = uu____5097;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5133  -> false);
              identifier_info = uu____5098;
              tc_hooks = default_tc_hooks;
              dsenv = uu____5101
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
  fun uu____5204  ->
    let uu____5205 = FStar_ST.op_Bang query_indices in
    match uu____5205 with
    | [] -> failwith "Empty query indices!"
    | uu____5282 ->
        let uu____5291 =
          let uu____5300 =
            let uu____5307 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5307 in
          let uu____5384 = FStar_ST.op_Bang query_indices in uu____5300 ::
            uu____5384 in
        FStar_ST.op_Colon_Equals query_indices uu____5291
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5526  ->
    let uu____5527 = FStar_ST.op_Bang query_indices in
    match uu____5527 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5695  ->
    match uu____5695 with
    | (l,n1) ->
        let uu____5702 = FStar_ST.op_Bang query_indices in
        (match uu____5702 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5867 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5885  ->
    let uu____5886 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5886
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5981 =
       let uu____5984 = FStar_ST.op_Bang stack in env :: uu____5984 in
     FStar_ST.op_Colon_Equals stack uu____5981);
    (let uu___148_6087 = env in
     let uu____6088 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6091 = FStar_Util.smap_copy (sigtab env) in
     let uu____6094 =
       let uu____6097 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6097 in
     {
       solver = (uu___148_6087.solver);
       range = (uu___148_6087.range);
       curmodule = (uu___148_6087.curmodule);
       gamma = (uu___148_6087.gamma);
       gamma_cache = uu____6088;
       modules = (uu___148_6087.modules);
       expected_typ = (uu___148_6087.expected_typ);
       sigtab = uu____6091;
       is_pattern = (uu___148_6087.is_pattern);
       instantiate_imp = (uu___148_6087.instantiate_imp);
       effects = (uu___148_6087.effects);
       generalize = (uu___148_6087.generalize);
       letrecs = (uu___148_6087.letrecs);
       top_level = (uu___148_6087.top_level);
       check_uvars = (uu___148_6087.check_uvars);
       use_eq = (uu___148_6087.use_eq);
       is_iface = (uu___148_6087.is_iface);
       admit = (uu___148_6087.admit);
       lax = (uu___148_6087.lax);
       lax_universes = (uu___148_6087.lax_universes);
       failhard = (uu___148_6087.failhard);
       nosynth = (uu___148_6087.nosynth);
       tc_term = (uu___148_6087.tc_term);
       type_of = (uu___148_6087.type_of);
       universe_of = (uu___148_6087.universe_of);
       use_bv_sorts = (uu___148_6087.use_bv_sorts);
       qname_and_index = (uu___148_6087.qname_and_index);
       proof_ns = (uu___148_6087.proof_ns);
       synth = (uu___148_6087.synth);
       is_native_tactic = (uu___148_6087.is_native_tactic);
       identifier_info = uu____6094;
       tc_hooks = (uu___148_6087.tc_hooks);
       dsenv = (uu___148_6087.dsenv)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6161  ->
    let uu____6162 = FStar_ST.op_Bang stack in
    match uu____6162 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6270 -> failwith "Impossible: Too many pops"
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
        let uu____6314 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6340  ->
                  match uu____6340 with
                  | (m,uu____6346) -> FStar_Ident.lid_equals l m)) in
        (match uu____6314 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___149_6353 = env in
               {
                 solver = (uu___149_6353.solver);
                 range = (uu___149_6353.range);
                 curmodule = (uu___149_6353.curmodule);
                 gamma = (uu___149_6353.gamma);
                 gamma_cache = (uu___149_6353.gamma_cache);
                 modules = (uu___149_6353.modules);
                 expected_typ = (uu___149_6353.expected_typ);
                 sigtab = (uu___149_6353.sigtab);
                 is_pattern = (uu___149_6353.is_pattern);
                 instantiate_imp = (uu___149_6353.instantiate_imp);
                 effects = (uu___149_6353.effects);
                 generalize = (uu___149_6353.generalize);
                 letrecs = (uu___149_6353.letrecs);
                 top_level = (uu___149_6353.top_level);
                 check_uvars = (uu___149_6353.check_uvars);
                 use_eq = (uu___149_6353.use_eq);
                 is_iface = (uu___149_6353.is_iface);
                 admit = (uu___149_6353.admit);
                 lax = (uu___149_6353.lax);
                 lax_universes = (uu___149_6353.lax_universes);
                 failhard = (uu___149_6353.failhard);
                 nosynth = (uu___149_6353.nosynth);
                 tc_term = (uu___149_6353.tc_term);
                 type_of = (uu___149_6353.type_of);
                 universe_of = (uu___149_6353.universe_of);
                 use_bv_sorts = (uu___149_6353.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___149_6353.proof_ns);
                 synth = (uu___149_6353.synth);
                 is_native_tactic = (uu___149_6353.is_native_tactic);
                 identifier_info = (uu___149_6353.identifier_info);
                 tc_hooks = (uu___149_6353.tc_hooks);
                 dsenv = (uu___149_6353.dsenv)
               }))
         | FStar_Pervasives_Native.Some (uu____6358,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___150_6366 = env in
               {
                 solver = (uu___150_6366.solver);
                 range = (uu___150_6366.range);
                 curmodule = (uu___150_6366.curmodule);
                 gamma = (uu___150_6366.gamma);
                 gamma_cache = (uu___150_6366.gamma_cache);
                 modules = (uu___150_6366.modules);
                 expected_typ = (uu___150_6366.expected_typ);
                 sigtab = (uu___150_6366.sigtab);
                 is_pattern = (uu___150_6366.is_pattern);
                 instantiate_imp = (uu___150_6366.instantiate_imp);
                 effects = (uu___150_6366.effects);
                 generalize = (uu___150_6366.generalize);
                 letrecs = (uu___150_6366.letrecs);
                 top_level = (uu___150_6366.top_level);
                 check_uvars = (uu___150_6366.check_uvars);
                 use_eq = (uu___150_6366.use_eq);
                 is_iface = (uu___150_6366.is_iface);
                 admit = (uu___150_6366.admit);
                 lax = (uu___150_6366.lax);
                 lax_universes = (uu___150_6366.lax_universes);
                 failhard = (uu___150_6366.failhard);
                 nosynth = (uu___150_6366.nosynth);
                 tc_term = (uu___150_6366.tc_term);
                 type_of = (uu___150_6366.type_of);
                 universe_of = (uu___150_6366.universe_of);
                 use_bv_sorts = (uu___150_6366.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___150_6366.proof_ns);
                 synth = (uu___150_6366.synth);
                 is_native_tactic = (uu___150_6366.is_native_tactic);
                 identifier_info = (uu___150_6366.identifier_info);
                 tc_hooks = (uu___150_6366.tc_hooks);
                 dsenv = (uu___150_6366.dsenv)
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
        (let uu___151_6388 = e in
         {
           solver = (uu___151_6388.solver);
           range = r;
           curmodule = (uu___151_6388.curmodule);
           gamma = (uu___151_6388.gamma);
           gamma_cache = (uu___151_6388.gamma_cache);
           modules = (uu___151_6388.modules);
           expected_typ = (uu___151_6388.expected_typ);
           sigtab = (uu___151_6388.sigtab);
           is_pattern = (uu___151_6388.is_pattern);
           instantiate_imp = (uu___151_6388.instantiate_imp);
           effects = (uu___151_6388.effects);
           generalize = (uu___151_6388.generalize);
           letrecs = (uu___151_6388.letrecs);
           top_level = (uu___151_6388.top_level);
           check_uvars = (uu___151_6388.check_uvars);
           use_eq = (uu___151_6388.use_eq);
           is_iface = (uu___151_6388.is_iface);
           admit = (uu___151_6388.admit);
           lax = (uu___151_6388.lax);
           lax_universes = (uu___151_6388.lax_universes);
           failhard = (uu___151_6388.failhard);
           nosynth = (uu___151_6388.nosynth);
           tc_term = (uu___151_6388.tc_term);
           type_of = (uu___151_6388.type_of);
           universe_of = (uu___151_6388.universe_of);
           use_bv_sorts = (uu___151_6388.use_bv_sorts);
           qname_and_index = (uu___151_6388.qname_and_index);
           proof_ns = (uu___151_6388.proof_ns);
           synth = (uu___151_6388.synth);
           is_native_tactic = (uu___151_6388.is_native_tactic);
           identifier_info = (uu___151_6388.identifier_info);
           tc_hooks = (uu___151_6388.tc_hooks);
           dsenv = (uu___151_6388.dsenv)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6401 =
        let uu____6402 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6402 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6401
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6507 =
          let uu____6508 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6508 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6507
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6613 =
          let uu____6614 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6614 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6613
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6720 =
        let uu____6721 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6721 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6720
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___152_6832 = env in
      {
        solver = (uu___152_6832.solver);
        range = (uu___152_6832.range);
        curmodule = lid;
        gamma = (uu___152_6832.gamma);
        gamma_cache = (uu___152_6832.gamma_cache);
        modules = (uu___152_6832.modules);
        expected_typ = (uu___152_6832.expected_typ);
        sigtab = (uu___152_6832.sigtab);
        is_pattern = (uu___152_6832.is_pattern);
        instantiate_imp = (uu___152_6832.instantiate_imp);
        effects = (uu___152_6832.effects);
        generalize = (uu___152_6832.generalize);
        letrecs = (uu___152_6832.letrecs);
        top_level = (uu___152_6832.top_level);
        check_uvars = (uu___152_6832.check_uvars);
        use_eq = (uu___152_6832.use_eq);
        is_iface = (uu___152_6832.is_iface);
        admit = (uu___152_6832.admit);
        lax = (uu___152_6832.lax);
        lax_universes = (uu___152_6832.lax_universes);
        failhard = (uu___152_6832.failhard);
        nosynth = (uu___152_6832.nosynth);
        tc_term = (uu___152_6832.tc_term);
        type_of = (uu___152_6832.type_of);
        universe_of = (uu___152_6832.universe_of);
        use_bv_sorts = (uu___152_6832.use_bv_sorts);
        qname_and_index = (uu___152_6832.qname_and_index);
        proof_ns = (uu___152_6832.proof_ns);
        synth = (uu___152_6832.synth);
        is_native_tactic = (uu___152_6832.is_native_tactic);
        identifier_info = (uu___152_6832.identifier_info);
        tc_hooks = (uu___152_6832.tc_hooks);
        dsenv = (uu___152_6832.dsenv)
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
    let uu____6863 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6863
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6867  ->
    let uu____6868 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6868
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
  fun uu___133_6946  ->
    match uu___133_6946 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6970  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6985 = inst_tscheme t in
      match uu____6985 with
      | (us,t1) ->
          let uu____6996 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6996)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7012  ->
          match uu____7012 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7027 =
                         let uu____7028 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7029 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7030 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7031 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7028 uu____7029 uu____7030 uu____7031 in
                       failwith uu____7027)
                    else ();
                    (let uu____7033 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7033))
               | uu____7040 ->
                   let uu____7041 =
                     let uu____7042 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7042 in
                   failwith uu____7041)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7047 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7052 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7057 -> false
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
             | ([],uu____7093) -> Maybe
             | (uu____7100,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7119 -> No in
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
          let uu____7226 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7226 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___134_7271  ->
                   match uu___134_7271 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7314 =
                           let uu____7333 =
                             let uu____7348 = inst_tscheme t in
                             FStar_Util.Inl uu____7348 in
                           (uu____7333, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7314
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7414,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7416);
                                     FStar_Syntax_Syntax.sigrng = uu____7417;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7418;
                                     FStar_Syntax_Syntax.sigmeta = uu____7419;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7420;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7440 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7440
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7486 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7493 -> cache t in
                       let uu____7494 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7494 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7569 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7569 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7655 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7735 = find_in_sigtab env lid in
         match uu____7735 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7834) ->
          add_sigelts env ses
      | uu____7843 ->
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
            | uu____7857 -> ()))
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
        (fun uu___135_7886  ->
           match uu___135_7886 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7904 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7939,lb::[]),uu____7941) ->
          let uu____7954 =
            let uu____7963 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7972 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7963, uu____7972) in
          FStar_Pervasives_Native.Some uu____7954
      | FStar_Syntax_Syntax.Sig_let ((uu____7985,lbs),uu____7987) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8023 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8035 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8035
                   then
                     let uu____8046 =
                       let uu____8055 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8064 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8055, uu____8064) in
                     FStar_Pervasives_Native.Some uu____8046
                   else FStar_Pervasives_Native.None)
      | uu____8086 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8120 =
          let uu____8129 =
            let uu____8134 =
              let uu____8135 =
                let uu____8138 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8138 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8135) in
            inst_tscheme uu____8134 in
          (uu____8129, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8120
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8158,uu____8159) ->
        let uu____8164 =
          let uu____8173 =
            let uu____8178 =
              let uu____8179 =
                let uu____8182 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8182 in
              (us, uu____8179) in
            inst_tscheme uu____8178 in
          (uu____8173, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8164
    | uu____8199 -> FStar_Pervasives_Native.None
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
      let mapper uu____8259 =
        match uu____8259 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8355,uvs,t,uu____8358,uu____8359,uu____8360);
                    FStar_Syntax_Syntax.sigrng = uu____8361;
                    FStar_Syntax_Syntax.sigquals = uu____8362;
                    FStar_Syntax_Syntax.sigmeta = uu____8363;
                    FStar_Syntax_Syntax.sigattrs = uu____8364;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8385 =
                   let uu____8394 = inst_tscheme (uvs, t) in
                   (uu____8394, rng) in
                 FStar_Pervasives_Native.Some uu____8385
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8414;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8416;
                    FStar_Syntax_Syntax.sigattrs = uu____8417;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8434 =
                   let uu____8435 = in_cur_mod env l in uu____8435 = Yes in
                 if uu____8434
                 then
                   let uu____8446 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8446
                    then
                      let uu____8459 =
                        let uu____8468 = inst_tscheme (uvs, t) in
                        (uu____8468, rng) in
                      FStar_Pervasives_Native.Some uu____8459
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8495 =
                      let uu____8504 = inst_tscheme (uvs, t) in
                      (uu____8504, rng) in
                    FStar_Pervasives_Native.Some uu____8495)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8525,uu____8526);
                    FStar_Syntax_Syntax.sigrng = uu____8527;
                    FStar_Syntax_Syntax.sigquals = uu____8528;
                    FStar_Syntax_Syntax.sigmeta = uu____8529;
                    FStar_Syntax_Syntax.sigattrs = uu____8530;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8569 =
                        let uu____8578 = inst_tscheme (uvs, k) in
                        (uu____8578, rng) in
                      FStar_Pervasives_Native.Some uu____8569
                  | uu____8595 ->
                      let uu____8596 =
                        let uu____8605 =
                          let uu____8610 =
                            let uu____8611 =
                              let uu____8614 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8614 in
                            (uvs, uu____8611) in
                          inst_tscheme uu____8610 in
                        (uu____8605, rng) in
                      FStar_Pervasives_Native.Some uu____8596)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8635,uu____8636);
                    FStar_Syntax_Syntax.sigrng = uu____8637;
                    FStar_Syntax_Syntax.sigquals = uu____8638;
                    FStar_Syntax_Syntax.sigmeta = uu____8639;
                    FStar_Syntax_Syntax.sigattrs = uu____8640;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8680 =
                        let uu____8689 = inst_tscheme_with (uvs, k) us in
                        (uu____8689, rng) in
                      FStar_Pervasives_Native.Some uu____8680
                  | uu____8706 ->
                      let uu____8707 =
                        let uu____8716 =
                          let uu____8721 =
                            let uu____8722 =
                              let uu____8725 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8725 in
                            (uvs, uu____8722) in
                          inst_tscheme_with uu____8721 us in
                        (uu____8716, rng) in
                      FStar_Pervasives_Native.Some uu____8707)
             | FStar_Util.Inr se ->
                 let uu____8759 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8780;
                        FStar_Syntax_Syntax.sigrng = uu____8781;
                        FStar_Syntax_Syntax.sigquals = uu____8782;
                        FStar_Syntax_Syntax.sigmeta = uu____8783;
                        FStar_Syntax_Syntax.sigattrs = uu____8784;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8799 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8759
                   (FStar_Util.map_option
                      (fun uu____8847  ->
                         match uu____8847 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8878 =
        let uu____8889 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8889 mapper in
      match uu____8878 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___153_8982 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___153_8982.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___153_8982.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9009 = lookup_qname env l in
      match uu____9009 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9048 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9098 = try_lookup_bv env bv in
      match uu____9098 with
      | FStar_Pervasives_Native.None  ->
          let uu____9113 =
            let uu____9114 =
              let uu____9119 = variable_not_found bv in (uu____9119, bvr) in
            FStar_Errors.Error uu____9114 in
          FStar_Exn.raise uu____9113
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9130 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9131 =
            let uu____9132 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9132 in
          (uu____9130, uu____9131)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9151 = try_lookup_lid_aux env l in
      match uu____9151 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9217 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9217 in
          let uu____9218 =
            let uu____9227 =
              let uu____9232 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9232) in
            (uu____9227, r1) in
          FStar_Pervasives_Native.Some uu____9218
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9261 = try_lookup_lid env l in
      match uu____9261 with
      | FStar_Pervasives_Native.None  ->
          let uu____9288 =
            let uu____9289 =
              let uu____9294 = name_not_found l in
              (uu____9294, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9289 in
          FStar_Exn.raise uu____9288
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___136_9332  ->
              match uu___136_9332 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9334 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9351 = lookup_qname env lid in
      match uu____9351 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9380,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9383;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9385;
              FStar_Syntax_Syntax.sigattrs = uu____9386;_},FStar_Pervasives_Native.None
            ),uu____9387)
          ->
          let uu____9436 =
            let uu____9447 =
              let uu____9452 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9452) in
            (uu____9447, q) in
          FStar_Pervasives_Native.Some uu____9436
      | uu____9469 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9508 = lookup_qname env lid in
      match uu____9508 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9533,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9536;
              FStar_Syntax_Syntax.sigquals = uu____9537;
              FStar_Syntax_Syntax.sigmeta = uu____9538;
              FStar_Syntax_Syntax.sigattrs = uu____9539;_},FStar_Pervasives_Native.None
            ),uu____9540)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9589 ->
          let uu____9610 =
            let uu____9611 =
              let uu____9616 = name_not_found lid in
              (uu____9616, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9611 in
          FStar_Exn.raise uu____9610
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9633 = lookup_qname env lid in
      match uu____9633 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9658,uvs,t,uu____9661,uu____9662,uu____9663);
              FStar_Syntax_Syntax.sigrng = uu____9664;
              FStar_Syntax_Syntax.sigquals = uu____9665;
              FStar_Syntax_Syntax.sigmeta = uu____9666;
              FStar_Syntax_Syntax.sigattrs = uu____9667;_},FStar_Pervasives_Native.None
            ),uu____9668)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9721 ->
          let uu____9742 =
            let uu____9743 =
              let uu____9748 = name_not_found lid in
              (uu____9748, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9743 in
          FStar_Exn.raise uu____9742
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9767 = lookup_qname env lid in
      match uu____9767 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9794,uu____9795,uu____9796,uu____9797,uu____9798,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9800;
              FStar_Syntax_Syntax.sigquals = uu____9801;
              FStar_Syntax_Syntax.sigmeta = uu____9802;
              FStar_Syntax_Syntax.sigattrs = uu____9803;_},uu____9804),uu____9805)
          -> (true, dcs)
      | uu____9866 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9897 = lookup_qname env lid in
      match uu____9897 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9918,uu____9919,uu____9920,l,uu____9922,uu____9923);
              FStar_Syntax_Syntax.sigrng = uu____9924;
              FStar_Syntax_Syntax.sigquals = uu____9925;
              FStar_Syntax_Syntax.sigmeta = uu____9926;
              FStar_Syntax_Syntax.sigattrs = uu____9927;_},uu____9928),uu____9929)
          -> l
      | uu____9984 ->
          let uu____10005 =
            let uu____10006 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10006 in
          failwith uu____10005
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
        let uu____10043 = lookup_qname env lid in
        match uu____10043 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10071)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10122,lbs),uu____10124)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10152 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10152
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10184 -> FStar_Pervasives_Native.None)
        | uu____10189 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10226 = lookup_qname env ftv in
      match uu____10226 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10250) ->
          let uu____10295 = effect_signature se in
          (match uu____10295 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10316,t),r) ->
               let uu____10331 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10331)
      | uu____10332 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10361 = try_lookup_effect_lid env ftv in
      match uu____10361 with
      | FStar_Pervasives_Native.None  ->
          let uu____10364 =
            let uu____10365 =
              let uu____10370 = name_not_found ftv in
              (uu____10370, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10365 in
          FStar_Exn.raise uu____10364
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
        let uu____10390 = lookup_qname env lid0 in
        match uu____10390 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10421);
                FStar_Syntax_Syntax.sigrng = uu____10422;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10424;
                FStar_Syntax_Syntax.sigattrs = uu____10425;_},FStar_Pervasives_Native.None
              ),uu____10426)
            ->
            let lid1 =
              let uu____10480 =
                let uu____10481 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10481 in
              FStar_Ident.set_lid_range lid uu____10480 in
            let uu____10482 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___137_10486  ->
                      match uu___137_10486 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10487 -> false)) in
            if uu____10482
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10501 =
                      let uu____10502 =
                        let uu____10503 = get_range env in
                        FStar_Range.string_of_range uu____10503 in
                      let uu____10504 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10505 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10502 uu____10504 uu____10505 in
                    failwith uu____10501) in
               match (binders, univs1) with
               | ([],uu____10512) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10529,uu____10530::uu____10531::uu____10532) ->
                   let uu____10537 =
                     let uu____10538 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10539 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10538 uu____10539 in
                   failwith uu____10537
               | uu____10546 ->
                   let uu____10551 =
                     let uu____10556 =
                       let uu____10557 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10557) in
                     inst_tscheme_with uu____10556 insts in
                   (match uu____10551 with
                    | (uu____10568,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10571 =
                          let uu____10572 = FStar_Syntax_Subst.compress t1 in
                          uu____10572.FStar_Syntax_Syntax.n in
                        (match uu____10571 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10619 -> failwith "Impossible")))
        | uu____10626 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10668 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10668 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10681,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10688 = find1 l2 in
            (match uu____10688 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10695 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10695 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10699 = find1 l in
            (match uu____10699 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10715 = lookup_qname env l1 in
      match uu____10715 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10738;
              FStar_Syntax_Syntax.sigrng = uu____10739;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10741;
              FStar_Syntax_Syntax.sigattrs = uu____10742;_},uu____10743),uu____10744)
          -> q
      | uu____10795 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10831 =
          let uu____10832 =
            let uu____10833 = FStar_Util.string_of_int i in
            let uu____10834 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10833 uu____10834 in
          failwith uu____10832 in
        let uu____10835 = lookup_datacon env lid in
        match uu____10835 with
        | (uu____10840,t) ->
            let uu____10842 =
              let uu____10843 = FStar_Syntax_Subst.compress t in
              uu____10843.FStar_Syntax_Syntax.n in
            (match uu____10842 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10847) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10878 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10878
                      FStar_Pervasives_Native.fst)
             | uu____10887 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10896 = lookup_qname env l in
      match uu____10896 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10917,uu____10918,uu____10919);
              FStar_Syntax_Syntax.sigrng = uu____10920;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10922;
              FStar_Syntax_Syntax.sigattrs = uu____10923;_},uu____10924),uu____10925)
          ->
          FStar_Util.for_some
            (fun uu___138_10978  ->
               match uu___138_10978 with
               | FStar_Syntax_Syntax.Projector uu____10979 -> true
               | uu____10984 -> false) quals
      | uu____10985 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11014 = lookup_qname env lid in
      match uu____11014 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11035,uu____11036,uu____11037,uu____11038,uu____11039,uu____11040);
              FStar_Syntax_Syntax.sigrng = uu____11041;
              FStar_Syntax_Syntax.sigquals = uu____11042;
              FStar_Syntax_Syntax.sigmeta = uu____11043;
              FStar_Syntax_Syntax.sigattrs = uu____11044;_},uu____11045),uu____11046)
          -> true
      | uu____11101 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11130 = lookup_qname env lid in
      match uu____11130 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11151,uu____11152,uu____11153,uu____11154,uu____11155,uu____11156);
              FStar_Syntax_Syntax.sigrng = uu____11157;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11159;
              FStar_Syntax_Syntax.sigattrs = uu____11160;_},uu____11161),uu____11162)
          ->
          FStar_Util.for_some
            (fun uu___139_11223  ->
               match uu___139_11223 with
               | FStar_Syntax_Syntax.RecordType uu____11224 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11233 -> true
               | uu____11242 -> false) quals
      | uu____11243 -> false
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
            (fun uu___140_11357  ->
               match uu___140_11357 with
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
      let uu____11392 =
        let uu____11393 = FStar_Syntax_Util.un_uinst head1 in
        uu____11393.FStar_Syntax_Syntax.n in
      match uu____11392 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11397 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11464 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11480) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11497 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11504 ->
                 FStar_Pervasives_Native.Some true
             | uu____11521 -> FStar_Pervasives_Native.Some false) in
      let uu____11522 =
        let uu____11525 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11525 mapper in
      match uu____11522 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11573 = lookup_qname env lid in
      match uu____11573 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11594,uu____11595,tps,uu____11597,uu____11598,uu____11599);
              FStar_Syntax_Syntax.sigrng = uu____11600;
              FStar_Syntax_Syntax.sigquals = uu____11601;
              FStar_Syntax_Syntax.sigmeta = uu____11602;
              FStar_Syntax_Syntax.sigattrs = uu____11603;_},uu____11604),uu____11605)
          -> FStar_List.length tps
      | uu____11668 ->
          let uu____11689 =
            let uu____11690 =
              let uu____11695 = name_not_found lid in
              (uu____11695, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11690 in
          FStar_Exn.raise uu____11689
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
           (fun uu____11737  ->
              match uu____11737 with
              | (d,uu____11745) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11758 = effect_decl_opt env l in
      match uu____11758 with
      | FStar_Pervasives_Native.None  ->
          let uu____11773 =
            let uu____11774 =
              let uu____11779 = name_not_found l in
              (uu____11779, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11774 in
          FStar_Exn.raise uu____11773
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
            (let uu____11845 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11898  ->
                       match uu____11898 with
                       | (m1,m2,uu____11911,uu____11912,uu____11913) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11845 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11930 =
                   let uu____11931 =
                     let uu____11936 =
                       let uu____11937 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11938 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11937
                         uu____11938 in
                     (uu____11936, (env.range)) in
                   FStar_Errors.Error uu____11931 in
                 FStar_Exn.raise uu____11930
             | FStar_Pervasives_Native.Some
                 (uu____11945,uu____11946,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11989 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11989)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12016 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12042  ->
                match uu____12042 with
                | (d,uu____12048) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12016 with
      | FStar_Pervasives_Native.None  ->
          let uu____12059 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12059
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12072 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12072 with
           | (uu____12083,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12093)::(wp,uu____12095)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12131 -> failwith "Impossible"))
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
                 let uu____12180 = get_range env in
                 let uu____12181 =
                   let uu____12184 =
                     let uu____12185 =
                       let uu____12200 =
                         let uu____12203 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12203] in
                       (null_wp, uu____12200) in
                     FStar_Syntax_Syntax.Tm_app uu____12185 in
                   FStar_Syntax_Syntax.mk uu____12184 in
                 uu____12181 FStar_Pervasives_Native.None uu____12180 in
               let uu____12209 =
                 let uu____12210 =
                   let uu____12219 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12219] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12210;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12209)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___154_12230 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___154_12230.order);
              joins = (uu___154_12230.joins)
            } in
          let uu___155_12239 = env in
          {
            solver = (uu___155_12239.solver);
            range = (uu___155_12239.range);
            curmodule = (uu___155_12239.curmodule);
            gamma = (uu___155_12239.gamma);
            gamma_cache = (uu___155_12239.gamma_cache);
            modules = (uu___155_12239.modules);
            expected_typ = (uu___155_12239.expected_typ);
            sigtab = (uu___155_12239.sigtab);
            is_pattern = (uu___155_12239.is_pattern);
            instantiate_imp = (uu___155_12239.instantiate_imp);
            effects;
            generalize = (uu___155_12239.generalize);
            letrecs = (uu___155_12239.letrecs);
            top_level = (uu___155_12239.top_level);
            check_uvars = (uu___155_12239.check_uvars);
            use_eq = (uu___155_12239.use_eq);
            is_iface = (uu___155_12239.is_iface);
            admit = (uu___155_12239.admit);
            lax = (uu___155_12239.lax);
            lax_universes = (uu___155_12239.lax_universes);
            failhard = (uu___155_12239.failhard);
            nosynth = (uu___155_12239.nosynth);
            tc_term = (uu___155_12239.tc_term);
            type_of = (uu___155_12239.type_of);
            universe_of = (uu___155_12239.universe_of);
            use_bv_sorts = (uu___155_12239.use_bv_sorts);
            qname_and_index = (uu___155_12239.qname_and_index);
            proof_ns = (uu___155_12239.proof_ns);
            synth = (uu___155_12239.synth);
            is_native_tactic = (uu___155_12239.is_native_tactic);
            identifier_info = (uu___155_12239.identifier_info);
            tc_hooks = (uu___155_12239.tc_hooks);
            dsenv = (uu___155_12239.dsenv)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12256 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12256 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12346 = (e1.mlift).mlift_wp t wp in
                              let uu____12347 = l1 t wp e in
                              l2 t uu____12346 uu____12347))
                | uu____12348 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12387 = inst_tscheme lift_t in
            match uu____12387 with
            | (uu____12394,lift_t1) ->
                let uu____12396 =
                  let uu____12399 =
                    let uu____12400 =
                      let uu____12415 =
                        let uu____12418 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12419 =
                          let uu____12422 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12422] in
                        uu____12418 :: uu____12419 in
                      (lift_t1, uu____12415) in
                    FStar_Syntax_Syntax.Tm_app uu____12400 in
                  FStar_Syntax_Syntax.mk uu____12399 in
                uu____12396 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12463 = inst_tscheme lift_t in
            match uu____12463 with
            | (uu____12470,lift_t1) ->
                let uu____12472 =
                  let uu____12475 =
                    let uu____12476 =
                      let uu____12491 =
                        let uu____12494 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12495 =
                          let uu____12498 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12499 =
                            let uu____12502 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12502] in
                          uu____12498 :: uu____12499 in
                        uu____12494 :: uu____12495 in
                      (lift_t1, uu____12491) in
                    FStar_Syntax_Syntax.Tm_app uu____12476 in
                  FStar_Syntax_Syntax.mk uu____12475 in
                uu____12472 FStar_Pervasives_Native.None
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
              let uu____12540 =
                let uu____12541 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12541
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12540 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12545 =
              let uu____12546 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12546 in
            let uu____12547 =
              let uu____12548 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12566 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12566) in
              FStar_Util.dflt "none" uu____12548 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12545
              uu____12547 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12592  ->
                    match uu____12592 with
                    | (e,uu____12600) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12619 =
            match uu____12619 with
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
              let uu____12657 =
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
                                    (let uu____12678 =
                                       let uu____12687 =
                                         find_edge order1 (i, k) in
                                       let uu____12690 =
                                         find_edge order1 (k, j) in
                                       (uu____12687, uu____12690) in
                                     match uu____12678 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12705 =
                                           compose_edges e1 e2 in
                                         [uu____12705]
                                     | uu____12706 -> []))))) in
              FStar_List.append order1 uu____12657 in
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
                   let uu____12735 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12737 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12737
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12735
                   then
                     let uu____12742 =
                       let uu____12743 =
                         let uu____12748 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12749 = get_range env in
                         (uu____12748, uu____12749) in
                       FStar_Errors.Error uu____12743 in
                     FStar_Exn.raise uu____12742
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
                                            let uu____12874 =
                                              let uu____12883 =
                                                find_edge order2 (i, k) in
                                              let uu____12886 =
                                                find_edge order2 (j, k) in
                                              (uu____12883, uu____12886) in
                                            match uu____12874 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12928,uu____12929)
                                                     ->
                                                     let uu____12936 =
                                                       let uu____12941 =
                                                         let uu____12942 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12942 in
                                                       let uu____12945 =
                                                         let uu____12946 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12946 in
                                                       (uu____12941,
                                                         uu____12945) in
                                                     (match uu____12936 with
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
                                            | uu____12981 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___156_13054 = env.effects in
              { decls = (uu___156_13054.decls); order = order2; joins } in
            let uu___157_13055 = env in
            {
              solver = (uu___157_13055.solver);
              range = (uu___157_13055.range);
              curmodule = (uu___157_13055.curmodule);
              gamma = (uu___157_13055.gamma);
              gamma_cache = (uu___157_13055.gamma_cache);
              modules = (uu___157_13055.modules);
              expected_typ = (uu___157_13055.expected_typ);
              sigtab = (uu___157_13055.sigtab);
              is_pattern = (uu___157_13055.is_pattern);
              instantiate_imp = (uu___157_13055.instantiate_imp);
              effects;
              generalize = (uu___157_13055.generalize);
              letrecs = (uu___157_13055.letrecs);
              top_level = (uu___157_13055.top_level);
              check_uvars = (uu___157_13055.check_uvars);
              use_eq = (uu___157_13055.use_eq);
              is_iface = (uu___157_13055.is_iface);
              admit = (uu___157_13055.admit);
              lax = (uu___157_13055.lax);
              lax_universes = (uu___157_13055.lax_universes);
              failhard = (uu___157_13055.failhard);
              nosynth = (uu___157_13055.nosynth);
              tc_term = (uu___157_13055.tc_term);
              type_of = (uu___157_13055.type_of);
              universe_of = (uu___157_13055.universe_of);
              use_bv_sorts = (uu___157_13055.use_bv_sorts);
              qname_and_index = (uu___157_13055.qname_and_index);
              proof_ns = (uu___157_13055.proof_ns);
              synth = (uu___157_13055.synth);
              is_native_tactic = (uu___157_13055.is_native_tactic);
              identifier_info = (uu___157_13055.identifier_info);
              tc_hooks = (uu___157_13055.tc_hooks);
              dsenv = (uu___157_13055.dsenv)
            }))
      | uu____13056 -> env
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
        | uu____13082 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13092 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13092 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13109 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13109 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13127 =
                     let uu____13128 =
                       let uu____13133 =
                         let uu____13134 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13139 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13146 =
                           let uu____13147 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13147 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13134 uu____13139 uu____13146 in
                       (uu____13133, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13128 in
                   FStar_Exn.raise uu____13127)
                else ();
                (let inst1 =
                   let uu____13152 =
                     let uu____13161 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13161 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13178  ->
                        fun uu____13179  ->
                          match (uu____13178, uu____13179) with
                          | ((x,uu____13201),(t,uu____13203)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13152 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13222 =
                     let uu___158_13223 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___158_13223.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___158_13223.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___158_13223.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___158_13223.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13222
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
          let uu____13249 = effect_decl_opt env effect_name in
          match uu____13249 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13282 =
                only_reifiable &&
                  (let uu____13284 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13284) in
              if uu____13282
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13300 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13319 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13348 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13348
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13349 =
                             let uu____13350 =
                               let uu____13355 = get_range env in
                               (message, uu____13355) in
                             FStar_Errors.Error uu____13350 in
                           FStar_Exn.raise uu____13349 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13365 =
                       let uu____13368 = get_range env in
                       let uu____13369 =
                         let uu____13372 =
                           let uu____13373 =
                             let uu____13388 =
                               let uu____13391 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13391; wp] in
                             (repr, uu____13388) in
                           FStar_Syntax_Syntax.Tm_app uu____13373 in
                         FStar_Syntax_Syntax.mk uu____13372 in
                       uu____13369 FStar_Pervasives_Native.None uu____13368 in
                     FStar_Pervasives_Native.Some uu____13365)
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
          let uu____13443 =
            let uu____13444 =
              let uu____13449 =
                let uu____13450 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13450 in
              let uu____13451 = get_range env in (uu____13449, uu____13451) in
            FStar_Errors.Error uu____13444 in
          FStar_Exn.raise uu____13443 in
        let uu____13452 = effect_repr_aux true env c u_c in
        match uu____13452 with
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
      | uu____13492 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13501 =
        let uu____13502 = FStar_Syntax_Subst.compress t in
        uu____13502.FStar_Syntax_Syntax.n in
      match uu____13501 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13505,c) ->
          is_reifiable_comp env c
      | uu____13523 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13547)::uu____13548 -> x :: rest
        | (Binding_sig_inst uu____13557)::uu____13558 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13573 = push1 x rest1 in local :: uu____13573 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___159_13577 = env in
       let uu____13578 = push1 s env.gamma in
       {
         solver = (uu___159_13577.solver);
         range = (uu___159_13577.range);
         curmodule = (uu___159_13577.curmodule);
         gamma = uu____13578;
         gamma_cache = (uu___159_13577.gamma_cache);
         modules = (uu___159_13577.modules);
         expected_typ = (uu___159_13577.expected_typ);
         sigtab = (uu___159_13577.sigtab);
         is_pattern = (uu___159_13577.is_pattern);
         instantiate_imp = (uu___159_13577.instantiate_imp);
         effects = (uu___159_13577.effects);
         generalize = (uu___159_13577.generalize);
         letrecs = (uu___159_13577.letrecs);
         top_level = (uu___159_13577.top_level);
         check_uvars = (uu___159_13577.check_uvars);
         use_eq = (uu___159_13577.use_eq);
         is_iface = (uu___159_13577.is_iface);
         admit = (uu___159_13577.admit);
         lax = (uu___159_13577.lax);
         lax_universes = (uu___159_13577.lax_universes);
         failhard = (uu___159_13577.failhard);
         nosynth = (uu___159_13577.nosynth);
         tc_term = (uu___159_13577.tc_term);
         type_of = (uu___159_13577.type_of);
         universe_of = (uu___159_13577.universe_of);
         use_bv_sorts = (uu___159_13577.use_bv_sorts);
         qname_and_index = (uu___159_13577.qname_and_index);
         proof_ns = (uu___159_13577.proof_ns);
         synth = (uu___159_13577.synth);
         is_native_tactic = (uu___159_13577.is_native_tactic);
         identifier_info = (uu___159_13577.identifier_info);
         tc_hooks = (uu___159_13577.tc_hooks);
         dsenv = (uu___159_13577.dsenv)
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
      let uu___160_13615 = env in
      {
        solver = (uu___160_13615.solver);
        range = (uu___160_13615.range);
        curmodule = (uu___160_13615.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___160_13615.gamma_cache);
        modules = (uu___160_13615.modules);
        expected_typ = (uu___160_13615.expected_typ);
        sigtab = (uu___160_13615.sigtab);
        is_pattern = (uu___160_13615.is_pattern);
        instantiate_imp = (uu___160_13615.instantiate_imp);
        effects = (uu___160_13615.effects);
        generalize = (uu___160_13615.generalize);
        letrecs = (uu___160_13615.letrecs);
        top_level = (uu___160_13615.top_level);
        check_uvars = (uu___160_13615.check_uvars);
        use_eq = (uu___160_13615.use_eq);
        is_iface = (uu___160_13615.is_iface);
        admit = (uu___160_13615.admit);
        lax = (uu___160_13615.lax);
        lax_universes = (uu___160_13615.lax_universes);
        failhard = (uu___160_13615.failhard);
        nosynth = (uu___160_13615.nosynth);
        tc_term = (uu___160_13615.tc_term);
        type_of = (uu___160_13615.type_of);
        universe_of = (uu___160_13615.universe_of);
        use_bv_sorts = (uu___160_13615.use_bv_sorts);
        qname_and_index = (uu___160_13615.qname_and_index);
        proof_ns = (uu___160_13615.proof_ns);
        synth = (uu___160_13615.synth);
        is_native_tactic = (uu___160_13615.is_native_tactic);
        identifier_info = (uu___160_13615.identifier_info);
        tc_hooks = (uu___160_13615.tc_hooks);
        dsenv = (uu___160_13615.dsenv)
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
            (let uu___161_13649 = env in
             {
               solver = (uu___161_13649.solver);
               range = (uu___161_13649.range);
               curmodule = (uu___161_13649.curmodule);
               gamma = rest;
               gamma_cache = (uu___161_13649.gamma_cache);
               modules = (uu___161_13649.modules);
               expected_typ = (uu___161_13649.expected_typ);
               sigtab = (uu___161_13649.sigtab);
               is_pattern = (uu___161_13649.is_pattern);
               instantiate_imp = (uu___161_13649.instantiate_imp);
               effects = (uu___161_13649.effects);
               generalize = (uu___161_13649.generalize);
               letrecs = (uu___161_13649.letrecs);
               top_level = (uu___161_13649.top_level);
               check_uvars = (uu___161_13649.check_uvars);
               use_eq = (uu___161_13649.use_eq);
               is_iface = (uu___161_13649.is_iface);
               admit = (uu___161_13649.admit);
               lax = (uu___161_13649.lax);
               lax_universes = (uu___161_13649.lax_universes);
               failhard = (uu___161_13649.failhard);
               nosynth = (uu___161_13649.nosynth);
               tc_term = (uu___161_13649.tc_term);
               type_of = (uu___161_13649.type_of);
               universe_of = (uu___161_13649.universe_of);
               use_bv_sorts = (uu___161_13649.use_bv_sorts);
               qname_and_index = (uu___161_13649.qname_and_index);
               proof_ns = (uu___161_13649.proof_ns);
               synth = (uu___161_13649.synth);
               is_native_tactic = (uu___161_13649.is_native_tactic);
               identifier_info = (uu___161_13649.identifier_info);
               tc_hooks = (uu___161_13649.tc_hooks);
               dsenv = (uu___161_13649.dsenv)
             }))
    | uu____13650 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13674  ->
             match uu____13674 with | (x,uu____13680) -> push_bv env1 x) env
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
            let uu___162_13710 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___162_13710.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___162_13710.FStar_Syntax_Syntax.index);
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
      (let uu___163_13745 = env in
       {
         solver = (uu___163_13745.solver);
         range = (uu___163_13745.range);
         curmodule = (uu___163_13745.curmodule);
         gamma = [];
         gamma_cache = (uu___163_13745.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___163_13745.sigtab);
         is_pattern = (uu___163_13745.is_pattern);
         instantiate_imp = (uu___163_13745.instantiate_imp);
         effects = (uu___163_13745.effects);
         generalize = (uu___163_13745.generalize);
         letrecs = (uu___163_13745.letrecs);
         top_level = (uu___163_13745.top_level);
         check_uvars = (uu___163_13745.check_uvars);
         use_eq = (uu___163_13745.use_eq);
         is_iface = (uu___163_13745.is_iface);
         admit = (uu___163_13745.admit);
         lax = (uu___163_13745.lax);
         lax_universes = (uu___163_13745.lax_universes);
         failhard = (uu___163_13745.failhard);
         nosynth = (uu___163_13745.nosynth);
         tc_term = (uu___163_13745.tc_term);
         type_of = (uu___163_13745.type_of);
         universe_of = (uu___163_13745.universe_of);
         use_bv_sorts = (uu___163_13745.use_bv_sorts);
         qname_and_index = (uu___163_13745.qname_and_index);
         proof_ns = (uu___163_13745.proof_ns);
         synth = (uu___163_13745.synth);
         is_native_tactic = (uu___163_13745.is_native_tactic);
         identifier_info = (uu___163_13745.identifier_info);
         tc_hooks = (uu___163_13745.tc_hooks);
         dsenv = (uu___163_13745.dsenv)
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
        let uu____13782 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13782 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13810 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13810)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___164_13825 = env in
      {
        solver = (uu___164_13825.solver);
        range = (uu___164_13825.range);
        curmodule = (uu___164_13825.curmodule);
        gamma = (uu___164_13825.gamma);
        gamma_cache = (uu___164_13825.gamma_cache);
        modules = (uu___164_13825.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___164_13825.sigtab);
        is_pattern = (uu___164_13825.is_pattern);
        instantiate_imp = (uu___164_13825.instantiate_imp);
        effects = (uu___164_13825.effects);
        generalize = (uu___164_13825.generalize);
        letrecs = (uu___164_13825.letrecs);
        top_level = (uu___164_13825.top_level);
        check_uvars = (uu___164_13825.check_uvars);
        use_eq = false;
        is_iface = (uu___164_13825.is_iface);
        admit = (uu___164_13825.admit);
        lax = (uu___164_13825.lax);
        lax_universes = (uu___164_13825.lax_universes);
        failhard = (uu___164_13825.failhard);
        nosynth = (uu___164_13825.nosynth);
        tc_term = (uu___164_13825.tc_term);
        type_of = (uu___164_13825.type_of);
        universe_of = (uu___164_13825.universe_of);
        use_bv_sorts = (uu___164_13825.use_bv_sorts);
        qname_and_index = (uu___164_13825.qname_and_index);
        proof_ns = (uu___164_13825.proof_ns);
        synth = (uu___164_13825.synth);
        is_native_tactic = (uu___164_13825.is_native_tactic);
        identifier_info = (uu___164_13825.identifier_info);
        tc_hooks = (uu___164_13825.tc_hooks);
        dsenv = (uu___164_13825.dsenv)
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
    let uu____13851 = expected_typ env_ in
    ((let uu___165_13857 = env_ in
      {
        solver = (uu___165_13857.solver);
        range = (uu___165_13857.range);
        curmodule = (uu___165_13857.curmodule);
        gamma = (uu___165_13857.gamma);
        gamma_cache = (uu___165_13857.gamma_cache);
        modules = (uu___165_13857.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___165_13857.sigtab);
        is_pattern = (uu___165_13857.is_pattern);
        instantiate_imp = (uu___165_13857.instantiate_imp);
        effects = (uu___165_13857.effects);
        generalize = (uu___165_13857.generalize);
        letrecs = (uu___165_13857.letrecs);
        top_level = (uu___165_13857.top_level);
        check_uvars = (uu___165_13857.check_uvars);
        use_eq = false;
        is_iface = (uu___165_13857.is_iface);
        admit = (uu___165_13857.admit);
        lax = (uu___165_13857.lax);
        lax_universes = (uu___165_13857.lax_universes);
        failhard = (uu___165_13857.failhard);
        nosynth = (uu___165_13857.nosynth);
        tc_term = (uu___165_13857.tc_term);
        type_of = (uu___165_13857.type_of);
        universe_of = (uu___165_13857.universe_of);
        use_bv_sorts = (uu___165_13857.use_bv_sorts);
        qname_and_index = (uu___165_13857.qname_and_index);
        proof_ns = (uu___165_13857.proof_ns);
        synth = (uu___165_13857.synth);
        is_native_tactic = (uu___165_13857.is_native_tactic);
        identifier_info = (uu___165_13857.identifier_info);
        tc_hooks = (uu___165_13857.tc_hooks);
        dsenv = (uu___165_13857.dsenv)
      }), uu____13851)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13872 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___141_13882  ->
                    match uu___141_13882 with
                    | Binding_sig (uu____13885,se) -> [se]
                    | uu____13891 -> [])) in
          FStar_All.pipe_right uu____13872 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___166_13898 = env in
       {
         solver = (uu___166_13898.solver);
         range = (uu___166_13898.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___166_13898.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___166_13898.expected_typ);
         sigtab = (uu___166_13898.sigtab);
         is_pattern = (uu___166_13898.is_pattern);
         instantiate_imp = (uu___166_13898.instantiate_imp);
         effects = (uu___166_13898.effects);
         generalize = (uu___166_13898.generalize);
         letrecs = (uu___166_13898.letrecs);
         top_level = (uu___166_13898.top_level);
         check_uvars = (uu___166_13898.check_uvars);
         use_eq = (uu___166_13898.use_eq);
         is_iface = (uu___166_13898.is_iface);
         admit = (uu___166_13898.admit);
         lax = (uu___166_13898.lax);
         lax_universes = (uu___166_13898.lax_universes);
         failhard = (uu___166_13898.failhard);
         nosynth = (uu___166_13898.nosynth);
         tc_term = (uu___166_13898.tc_term);
         type_of = (uu___166_13898.type_of);
         universe_of = (uu___166_13898.universe_of);
         use_bv_sorts = (uu___166_13898.use_bv_sorts);
         qname_and_index = (uu___166_13898.qname_and_index);
         proof_ns = (uu___166_13898.proof_ns);
         synth = (uu___166_13898.synth);
         is_native_tactic = (uu___166_13898.is_native_tactic);
         identifier_info = (uu___166_13898.identifier_info);
         tc_hooks = (uu___166_13898.tc_hooks);
         dsenv = (uu___166_13898.dsenv)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13980)::tl1 -> aux out tl1
      | (Binding_lid (uu____13984,(uu____13985,t)))::tl1 ->
          let uu____14000 =
            let uu____14007 = FStar_Syntax_Free.uvars t in
            ext out uu____14007 in
          aux uu____14000 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14014;
            FStar_Syntax_Syntax.index = uu____14015;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14022 =
            let uu____14029 = FStar_Syntax_Free.uvars t in
            ext out uu____14029 in
          aux uu____14022 tl1
      | (Binding_sig uu____14036)::uu____14037 -> out
      | (Binding_sig_inst uu____14046)::uu____14047 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14103)::tl1 -> aux out tl1
      | (Binding_univ uu____14115)::tl1 -> aux out tl1
      | (Binding_lid (uu____14119,(uu____14120,t)))::tl1 ->
          let uu____14135 =
            let uu____14138 = FStar_Syntax_Free.univs t in
            ext out uu____14138 in
          aux uu____14135 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14141;
            FStar_Syntax_Syntax.index = uu____14142;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14149 =
            let uu____14152 = FStar_Syntax_Free.univs t in
            ext out uu____14152 in
          aux uu____14149 tl1
      | (Binding_sig uu____14155)::uu____14156 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14210)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14226 = FStar_Util.fifo_set_add uname out in
          aux uu____14226 tl1
      | (Binding_lid (uu____14229,(uu____14230,t)))::tl1 ->
          let uu____14245 =
            let uu____14248 = FStar_Syntax_Free.univnames t in
            ext out uu____14248 in
          aux uu____14245 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14251;
            FStar_Syntax_Syntax.index = uu____14252;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14259 =
            let uu____14262 = FStar_Syntax_Free.univnames t in
            ext out uu____14262 in
          aux uu____14259 tl1
      | (Binding_sig uu____14265)::uu____14266 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___142_14291  ->
            match uu___142_14291 with
            | Binding_var x -> [x]
            | Binding_lid uu____14295 -> []
            | Binding_sig uu____14300 -> []
            | Binding_univ uu____14307 -> []
            | Binding_sig_inst uu____14308 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14325 =
      let uu____14328 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14328
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14325 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14353 =
      let uu____14354 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___143_14364  ->
                match uu___143_14364 with
                | Binding_var x ->
                    let uu____14366 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14366
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14369) ->
                    let uu____14370 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14370
                | Binding_sig (ls,uu____14372) ->
                    let uu____14377 =
                      let uu____14378 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14378
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14377
                | Binding_sig_inst (ls,uu____14388,uu____14389) ->
                    let uu____14394 =
                      let uu____14395 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14395
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14394)) in
      FStar_All.pipe_right uu____14354 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14353 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14414 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14414
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14442  ->
                 fun uu____14443  ->
                   match (uu____14442, uu____14443) with
                   | ((b1,uu____14461),(b2,uu____14463)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___144_14510  ->
    match uu___144_14510 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14511 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___145_14530  ->
             match uu___145_14530 with
             | Binding_sig (lids,uu____14536) -> FStar_List.append lids keys
             | uu____14541 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14547  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14583) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14602,uu____14603) -> false in
      let uu____14612 =
        FStar_List.tryFind
          (fun uu____14630  ->
             match uu____14630 with | (p,uu____14638) -> list_prefix p path)
          env.proof_ns in
      match uu____14612 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14649,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14669 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14669
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___167_14684 = e in
        {
          solver = (uu___167_14684.solver);
          range = (uu___167_14684.range);
          curmodule = (uu___167_14684.curmodule);
          gamma = (uu___167_14684.gamma);
          gamma_cache = (uu___167_14684.gamma_cache);
          modules = (uu___167_14684.modules);
          expected_typ = (uu___167_14684.expected_typ);
          sigtab = (uu___167_14684.sigtab);
          is_pattern = (uu___167_14684.is_pattern);
          instantiate_imp = (uu___167_14684.instantiate_imp);
          effects = (uu___167_14684.effects);
          generalize = (uu___167_14684.generalize);
          letrecs = (uu___167_14684.letrecs);
          top_level = (uu___167_14684.top_level);
          check_uvars = (uu___167_14684.check_uvars);
          use_eq = (uu___167_14684.use_eq);
          is_iface = (uu___167_14684.is_iface);
          admit = (uu___167_14684.admit);
          lax = (uu___167_14684.lax);
          lax_universes = (uu___167_14684.lax_universes);
          failhard = (uu___167_14684.failhard);
          nosynth = (uu___167_14684.nosynth);
          tc_term = (uu___167_14684.tc_term);
          type_of = (uu___167_14684.type_of);
          universe_of = (uu___167_14684.universe_of);
          use_bv_sorts = (uu___167_14684.use_bv_sorts);
          qname_and_index = (uu___167_14684.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___167_14684.synth);
          is_native_tactic = (uu___167_14684.is_native_tactic);
          identifier_info = (uu___167_14684.identifier_info);
          tc_hooks = (uu___167_14684.tc_hooks);
          dsenv = (uu___167_14684.dsenv)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___168_14717 = e in
      {
        solver = (uu___168_14717.solver);
        range = (uu___168_14717.range);
        curmodule = (uu___168_14717.curmodule);
        gamma = (uu___168_14717.gamma);
        gamma_cache = (uu___168_14717.gamma_cache);
        modules = (uu___168_14717.modules);
        expected_typ = (uu___168_14717.expected_typ);
        sigtab = (uu___168_14717.sigtab);
        is_pattern = (uu___168_14717.is_pattern);
        instantiate_imp = (uu___168_14717.instantiate_imp);
        effects = (uu___168_14717.effects);
        generalize = (uu___168_14717.generalize);
        letrecs = (uu___168_14717.letrecs);
        top_level = (uu___168_14717.top_level);
        check_uvars = (uu___168_14717.check_uvars);
        use_eq = (uu___168_14717.use_eq);
        is_iface = (uu___168_14717.is_iface);
        admit = (uu___168_14717.admit);
        lax = (uu___168_14717.lax);
        lax_universes = (uu___168_14717.lax_universes);
        failhard = (uu___168_14717.failhard);
        nosynth = (uu___168_14717.nosynth);
        tc_term = (uu___168_14717.tc_term);
        type_of = (uu___168_14717.type_of);
        universe_of = (uu___168_14717.universe_of);
        use_bv_sorts = (uu___168_14717.use_bv_sorts);
        qname_and_index = (uu___168_14717.qname_and_index);
        proof_ns = ns;
        synth = (uu___168_14717.synth);
        is_native_tactic = (uu___168_14717.is_native_tactic);
        identifier_info = (uu___168_14717.identifier_info);
        tc_hooks = (uu___168_14717.tc_hooks);
        dsenv = (uu___168_14717.dsenv)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14731 =
      match uu____14731 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14747 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14747) in
    let uu____14749 =
      let uu____14752 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14752 FStar_List.rev in
    FStar_All.pipe_right uu____14749 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14769  -> ());
    push = (fun uu____14771  -> ());
    pop = (fun uu____14773  -> ());
    encode_modul = (fun uu____14776  -> fun uu____14777  -> ());
    encode_sig = (fun uu____14780  -> fun uu____14781  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14787 =
             let uu____14794 = FStar_Options.peek () in (e, g, uu____14794) in
           [uu____14787]);
    solve = (fun uu____14810  -> fun uu____14811  -> fun uu____14812  -> ());
    finish = (fun uu____14818  -> ());
    refresh = (fun uu____14820  -> ())
  }