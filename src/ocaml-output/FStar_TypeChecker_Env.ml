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
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref;}
[@@deriving show]
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  mark: Prims.string -> Prims.unit;
  reset_mark: Prims.string -> Prims.unit;
  commit_mark: Prims.string -> Prims.unit;
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
        identifier_info = __fname__identifier_info;_} -> __fname__solver
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
        identifier_info = __fname__identifier_info;_} -> __fname__range
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
        identifier_info = __fname__identifier_info;_} -> __fname__curmodule
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
        identifier_info = __fname__identifier_info;_} -> __fname__gamma
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
        identifier_info = __fname__identifier_info;_} -> __fname__gamma_cache
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
        identifier_info = __fname__identifier_info;_} -> __fname__modules
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
        identifier_info = __fname__identifier_info;_} ->
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
        identifier_info = __fname__identifier_info;_} -> __fname__sigtab
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
        identifier_info = __fname__identifier_info;_} -> __fname__is_pattern
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
        identifier_info = __fname__identifier_info;_} ->
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
        identifier_info = __fname__identifier_info;_} -> __fname__effects
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
        identifier_info = __fname__identifier_info;_} -> __fname__generalize
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
        identifier_info = __fname__identifier_info;_} -> __fname__letrecs
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
        identifier_info = __fname__identifier_info;_} -> __fname__top_level
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
        identifier_info = __fname__identifier_info;_} -> __fname__check_uvars
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
        identifier_info = __fname__identifier_info;_} -> __fname__use_eq
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
        identifier_info = __fname__identifier_info;_} -> __fname__is_iface
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
        identifier_info = __fname__identifier_info;_} -> __fname__admit
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
        identifier_info = __fname__identifier_info;_} -> __fname__lax
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
        identifier_info = __fname__identifier_info;_} ->
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
        identifier_info = __fname__identifier_info;_} -> __fname__failhard
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
        identifier_info = __fname__identifier_info;_} -> __fname__nosynth
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
        identifier_info = __fname__identifier_info;_} -> __fname__tc_term
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
        identifier_info = __fname__identifier_info;_} -> __fname__type_of
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
        identifier_info = __fname__identifier_info;_} -> __fname__universe_of
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
        identifier_info = __fname__identifier_info;_} ->
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
        identifier_info = __fname__identifier_info;_} ->
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
        identifier_info = __fname__identifier_info;_} -> __fname__proof_ns
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
        identifier_info = __fname__identifier_info;_} -> __fname__synth
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
        identifier_info = __fname__identifier_info;_} ->
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
        identifier_info = __fname__identifier_info;_} ->
        __fname__identifier_info
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__init
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__push
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__pop
let __proj__Mksolver_t__item__mark: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__mark
let __proj__Mksolver_t__item__reset_mark:
  solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__reset_mark
let __proj__Mksolver_t__item__commit_mark:
  solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__commit_mark
let __proj__Mksolver_t__item__encode_modul:
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
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
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
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
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
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
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
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
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__is_trivial
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; is_trivial = __fname__is_trivial;
        finish = __fname__finish; refresh = __fname__refresh;_} ->
        __fname__finish
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        mark = __fname__mark; reset_mark = __fname__reset_mark;
        commit_mark = __fname__commit_mark;
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
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
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
      | (NoDelta ,uu____5092) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5093,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5094,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5095 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5104 . Prims.unit -> 'Auu____5104 FStar_Util.smap =
  fun uu____5110  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5115 . Prims.unit -> 'Auu____5115 FStar_Util.smap =
  fun uu____5121  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____5196 = new_gamma_cache () in
            let uu____5199 = new_sigtab () in
            let uu____5202 =
              let uu____5203 = FStar_Options.using_facts_from () in
              match uu____5203 with
              | FStar_Pervasives_Native.Some ns ->
                  let uu____5213 =
                    let uu____5222 =
                      FStar_List.map
                        (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                    FStar_List.append uu____5222 [([], false)] in
                  [uu____5213]
              | FStar_Pervasives_Native.None  -> [[]] in
            let uu____5295 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
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
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5329  -> false);
              identifier_info = uu____5295
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
  fun uu____5400  ->
    let uu____5401 = FStar_ST.op_Bang query_indices in
    match uu____5401 with
    | [] -> failwith "Empty query indices!"
    | uu____5458 ->
        let uu____5467 =
          let uu____5476 =
            let uu____5483 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5483 in
          let uu____5540 = FStar_ST.op_Bang query_indices in uu____5476 ::
            uu____5540 in
        FStar_ST.op_Colon_Equals query_indices uu____5467
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5642  ->
    let uu____5643 = FStar_ST.op_Bang query_indices in
    match uu____5643 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5771  ->
    match uu____5771 with
    | (l,n1) ->
        let uu____5778 = FStar_ST.op_Bang query_indices in
        (match uu____5778 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5903 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5921  ->
    let uu____5922 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5922
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____5982  ->
    let uu____5983 = FStar_ST.op_Bang query_indices in
    match uu____5983 with
    | hd1::uu____6035::tl1 ->
        FStar_ST.op_Colon_Equals query_indices (hd1 :: tl1)
    | uu____6117 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6144 =
       let uu____6147 = FStar_ST.op_Bang stack in env :: uu____6147 in
     FStar_ST.op_Colon_Equals stack uu____6144);
    (let uu___126_6186 = env in
     let uu____6187 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6190 = FStar_Util.smap_copy (sigtab env) in
     let uu____6193 =
       let uu____6196 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6196 in
     {
       solver = (uu___126_6186.solver);
       range = (uu___126_6186.range);
       curmodule = (uu___126_6186.curmodule);
       gamma = (uu___126_6186.gamma);
       gamma_cache = uu____6187;
       modules = (uu___126_6186.modules);
       expected_typ = (uu___126_6186.expected_typ);
       sigtab = uu____6190;
       is_pattern = (uu___126_6186.is_pattern);
       instantiate_imp = (uu___126_6186.instantiate_imp);
       effects = (uu___126_6186.effects);
       generalize = (uu___126_6186.generalize);
       letrecs = (uu___126_6186.letrecs);
       top_level = (uu___126_6186.top_level);
       check_uvars = (uu___126_6186.check_uvars);
       use_eq = (uu___126_6186.use_eq);
       is_iface = (uu___126_6186.is_iface);
       admit = (uu___126_6186.admit);
       lax = (uu___126_6186.lax);
       lax_universes = (uu___126_6186.lax_universes);
       failhard = (uu___126_6186.failhard);
       nosynth = (uu___126_6186.nosynth);
       tc_term = (uu___126_6186.tc_term);
       type_of = (uu___126_6186.type_of);
       universe_of = (uu___126_6186.universe_of);
       use_bv_sorts = (uu___126_6186.use_bv_sorts);
       qname_and_index = (uu___126_6186.qname_and_index);
       proof_ns = (uu___126_6186.proof_ns);
       synth = (uu___126_6186.synth);
       is_native_tactic = (uu___126_6186.is_native_tactic);
       identifier_info = uu____6193
     })
let pop_stack: Prims.unit -> env =
  fun uu____6224  ->
    let uu____6225 = FStar_ST.op_Bang stack in
    match uu____6225 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6269 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let mark: env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
let commit_mark: env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____6309 = pop_stack () in ());
    env
let reset_mark: env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____6337 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6363  ->
                  match uu____6363 with
                  | (m,uu____6369) -> FStar_Ident.lid_equals l m)) in
        (match uu____6337 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___127_6376 = env in
               {
                 solver = (uu___127_6376.solver);
                 range = (uu___127_6376.range);
                 curmodule = (uu___127_6376.curmodule);
                 gamma = (uu___127_6376.gamma);
                 gamma_cache = (uu___127_6376.gamma_cache);
                 modules = (uu___127_6376.modules);
                 expected_typ = (uu___127_6376.expected_typ);
                 sigtab = (uu___127_6376.sigtab);
                 is_pattern = (uu___127_6376.is_pattern);
                 instantiate_imp = (uu___127_6376.instantiate_imp);
                 effects = (uu___127_6376.effects);
                 generalize = (uu___127_6376.generalize);
                 letrecs = (uu___127_6376.letrecs);
                 top_level = (uu___127_6376.top_level);
                 check_uvars = (uu___127_6376.check_uvars);
                 use_eq = (uu___127_6376.use_eq);
                 is_iface = (uu___127_6376.is_iface);
                 admit = (uu___127_6376.admit);
                 lax = (uu___127_6376.lax);
                 lax_universes = (uu___127_6376.lax_universes);
                 failhard = (uu___127_6376.failhard);
                 nosynth = (uu___127_6376.nosynth);
                 tc_term = (uu___127_6376.tc_term);
                 type_of = (uu___127_6376.type_of);
                 universe_of = (uu___127_6376.universe_of);
                 use_bv_sorts = (uu___127_6376.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___127_6376.proof_ns);
                 synth = (uu___127_6376.synth);
                 is_native_tactic = (uu___127_6376.is_native_tactic);
                 identifier_info = (uu___127_6376.identifier_info)
               }))
         | FStar_Pervasives_Native.Some (uu____6381,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___128_6389 = env in
               {
                 solver = (uu___128_6389.solver);
                 range = (uu___128_6389.range);
                 curmodule = (uu___128_6389.curmodule);
                 gamma = (uu___128_6389.gamma);
                 gamma_cache = (uu___128_6389.gamma_cache);
                 modules = (uu___128_6389.modules);
                 expected_typ = (uu___128_6389.expected_typ);
                 sigtab = (uu___128_6389.sigtab);
                 is_pattern = (uu___128_6389.is_pattern);
                 instantiate_imp = (uu___128_6389.instantiate_imp);
                 effects = (uu___128_6389.effects);
                 generalize = (uu___128_6389.generalize);
                 letrecs = (uu___128_6389.letrecs);
                 top_level = (uu___128_6389.top_level);
                 check_uvars = (uu___128_6389.check_uvars);
                 use_eq = (uu___128_6389.use_eq);
                 is_iface = (uu___128_6389.is_iface);
                 admit = (uu___128_6389.admit);
                 lax = (uu___128_6389.lax);
                 lax_universes = (uu___128_6389.lax_universes);
                 failhard = (uu___128_6389.failhard);
                 nosynth = (uu___128_6389.nosynth);
                 tc_term = (uu___128_6389.tc_term);
                 type_of = (uu___128_6389.type_of);
                 universe_of = (uu___128_6389.universe_of);
                 use_bv_sorts = (uu___128_6389.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___128_6389.proof_ns);
                 synth = (uu___128_6389.synth);
                 is_native_tactic = (uu___128_6389.is_native_tactic);
                 identifier_info = (uu___128_6389.identifier_info)
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
        (let uu___129_6411 = e in
         {
           solver = (uu___129_6411.solver);
           range = r;
           curmodule = (uu___129_6411.curmodule);
           gamma = (uu___129_6411.gamma);
           gamma_cache = (uu___129_6411.gamma_cache);
           modules = (uu___129_6411.modules);
           expected_typ = (uu___129_6411.expected_typ);
           sigtab = (uu___129_6411.sigtab);
           is_pattern = (uu___129_6411.is_pattern);
           instantiate_imp = (uu___129_6411.instantiate_imp);
           effects = (uu___129_6411.effects);
           generalize = (uu___129_6411.generalize);
           letrecs = (uu___129_6411.letrecs);
           top_level = (uu___129_6411.top_level);
           check_uvars = (uu___129_6411.check_uvars);
           use_eq = (uu___129_6411.use_eq);
           is_iface = (uu___129_6411.is_iface);
           admit = (uu___129_6411.admit);
           lax = (uu___129_6411.lax);
           lax_universes = (uu___129_6411.lax_universes);
           failhard = (uu___129_6411.failhard);
           nosynth = (uu___129_6411.nosynth);
           tc_term = (uu___129_6411.tc_term);
           type_of = (uu___129_6411.type_of);
           universe_of = (uu___129_6411.universe_of);
           use_bv_sorts = (uu___129_6411.use_bv_sorts);
           qname_and_index = (uu___129_6411.qname_and_index);
           proof_ns = (uu___129_6411.proof_ns);
           synth = (uu___129_6411.synth);
           is_native_tactic = (uu___129_6411.is_native_tactic);
           identifier_info = (uu___129_6411.identifier_info)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6424 =
        let uu____6425 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6425 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6424
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6458 =
          let uu____6459 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6459 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6458
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6492 =
          let uu____6493 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6493 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6492
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6527 =
        let uu____6528 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6528 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6527
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___130_6567 = env in
      {
        solver = (uu___130_6567.solver);
        range = (uu___130_6567.range);
        curmodule = lid;
        gamma = (uu___130_6567.gamma);
        gamma_cache = (uu___130_6567.gamma_cache);
        modules = (uu___130_6567.modules);
        expected_typ = (uu___130_6567.expected_typ);
        sigtab = (uu___130_6567.sigtab);
        is_pattern = (uu___130_6567.is_pattern);
        instantiate_imp = (uu___130_6567.instantiate_imp);
        effects = (uu___130_6567.effects);
        generalize = (uu___130_6567.generalize);
        letrecs = (uu___130_6567.letrecs);
        top_level = (uu___130_6567.top_level);
        check_uvars = (uu___130_6567.check_uvars);
        use_eq = (uu___130_6567.use_eq);
        is_iface = (uu___130_6567.is_iface);
        admit = (uu___130_6567.admit);
        lax = (uu___130_6567.lax);
        lax_universes = (uu___130_6567.lax_universes);
        failhard = (uu___130_6567.failhard);
        nosynth = (uu___130_6567.nosynth);
        tc_term = (uu___130_6567.tc_term);
        type_of = (uu___130_6567.type_of);
        universe_of = (uu___130_6567.universe_of);
        use_bv_sorts = (uu___130_6567.use_bv_sorts);
        qname_and_index = (uu___130_6567.qname_and_index);
        proof_ns = (uu___130_6567.proof_ns);
        synth = (uu___130_6567.synth);
        is_native_tactic = (uu___130_6567.is_native_tactic);
        identifier_info = (uu___130_6567.identifier_info)
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
    let uu____6598 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6598
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6602  ->
    let uu____6603 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6603
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
      | ((formals,t),uu____6643) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6667 = FStar_Syntax_Subst.subst vs t in (us, uu____6667)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___113_6681  ->
    match uu___113_6681 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6705  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6720 = inst_tscheme t in
      match uu____6720 with
      | (us,t1) ->
          let uu____6731 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6731)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6747  ->
          match uu____6747 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6762 =
                         let uu____6763 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6764 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6765 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6766 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6763 uu____6764 uu____6765 uu____6766 in
                       failwith uu____6762)
                    else ();
                    (let uu____6768 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6768))
               | uu____6775 ->
                   let uu____6776 =
                     let uu____6777 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6777 in
                   failwith uu____6776)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6782 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6787 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6792 -> false
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
             | ([],uu____6828) -> Maybe
             | (uu____6835,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6854 -> No in
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
          let uu____6961 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6961 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___114_7006  ->
                   match uu___114_7006 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7049 =
                           let uu____7068 =
                             let uu____7083 = inst_tscheme t in
                             FStar_Util.Inl uu____7083 in
                           (uu____7068, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7049
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7149,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7151);
                                     FStar_Syntax_Syntax.sigrng = uu____7152;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7153;
                                     FStar_Syntax_Syntax.sigmeta = uu____7154;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7155;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7175 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7175
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7221 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7228 -> cache t in
                       let uu____7229 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7229 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7304 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7304 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7390 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7470 = find_in_sigtab env lid in
         match uu____7470 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7569) ->
          add_sigelts env ses
      | uu____7578 ->
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
            | uu____7592 -> ()))
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
        (fun uu___115_7621  ->
           match uu___115_7621 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7639 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7674,lb::[]),uu____7676) ->
          let uu____7689 =
            let uu____7698 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7707 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7698, uu____7707) in
          FStar_Pervasives_Native.Some uu____7689
      | FStar_Syntax_Syntax.Sig_let ((uu____7720,lbs),uu____7722) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7758 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7770 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7770
                   then
                     let uu____7781 =
                       let uu____7790 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7799 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7790, uu____7799) in
                     FStar_Pervasives_Native.Some uu____7781
                   else FStar_Pervasives_Native.None)
      | uu____7821 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7855 =
          let uu____7864 =
            let uu____7869 =
              let uu____7870 =
                let uu____7873 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7873 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7870) in
            inst_tscheme uu____7869 in
          (uu____7864, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7855
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7893,uu____7894) ->
        let uu____7899 =
          let uu____7908 =
            let uu____7913 =
              let uu____7914 =
                let uu____7917 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7917 in
              (us, uu____7914) in
            inst_tscheme uu____7913 in
          (uu____7908, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7899
    | uu____7934 -> FStar_Pervasives_Native.None
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
      let mapper uu____7994 =
        match uu____7994 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8090,uvs,t,uu____8093,uu____8094,uu____8095);
                    FStar_Syntax_Syntax.sigrng = uu____8096;
                    FStar_Syntax_Syntax.sigquals = uu____8097;
                    FStar_Syntax_Syntax.sigmeta = uu____8098;
                    FStar_Syntax_Syntax.sigattrs = uu____8099;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8120 =
                   let uu____8129 = inst_tscheme (uvs, t) in
                   (uu____8129, rng) in
                 FStar_Pervasives_Native.Some uu____8120
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8149;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8151;
                    FStar_Syntax_Syntax.sigattrs = uu____8152;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8169 =
                   let uu____8170 = in_cur_mod env l in uu____8170 = Yes in
                 if uu____8169
                 then
                   let uu____8181 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8181
                    then
                      let uu____8194 =
                        let uu____8203 = inst_tscheme (uvs, t) in
                        (uu____8203, rng) in
                      FStar_Pervasives_Native.Some uu____8194
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8230 =
                      let uu____8239 = inst_tscheme (uvs, t) in
                      (uu____8239, rng) in
                    FStar_Pervasives_Native.Some uu____8230)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8260,uu____8261);
                    FStar_Syntax_Syntax.sigrng = uu____8262;
                    FStar_Syntax_Syntax.sigquals = uu____8263;
                    FStar_Syntax_Syntax.sigmeta = uu____8264;
                    FStar_Syntax_Syntax.sigattrs = uu____8265;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8304 =
                        let uu____8313 = inst_tscheme (uvs, k) in
                        (uu____8313, rng) in
                      FStar_Pervasives_Native.Some uu____8304
                  | uu____8330 ->
                      let uu____8331 =
                        let uu____8340 =
                          let uu____8345 =
                            let uu____8346 =
                              let uu____8349 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8349 in
                            (uvs, uu____8346) in
                          inst_tscheme uu____8345 in
                        (uu____8340, rng) in
                      FStar_Pervasives_Native.Some uu____8331)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8370,uu____8371);
                    FStar_Syntax_Syntax.sigrng = uu____8372;
                    FStar_Syntax_Syntax.sigquals = uu____8373;
                    FStar_Syntax_Syntax.sigmeta = uu____8374;
                    FStar_Syntax_Syntax.sigattrs = uu____8375;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8415 =
                        let uu____8424 = inst_tscheme_with (uvs, k) us in
                        (uu____8424, rng) in
                      FStar_Pervasives_Native.Some uu____8415
                  | uu____8441 ->
                      let uu____8442 =
                        let uu____8451 =
                          let uu____8456 =
                            let uu____8457 =
                              let uu____8460 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8460 in
                            (uvs, uu____8457) in
                          inst_tscheme_with uu____8456 us in
                        (uu____8451, rng) in
                      FStar_Pervasives_Native.Some uu____8442)
             | FStar_Util.Inr se ->
                 let uu____8494 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8515;
                        FStar_Syntax_Syntax.sigrng = uu____8516;
                        FStar_Syntax_Syntax.sigquals = uu____8517;
                        FStar_Syntax_Syntax.sigmeta = uu____8518;
                        FStar_Syntax_Syntax.sigattrs = uu____8519;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8534 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8494
                   (FStar_Util.map_option
                      (fun uu____8582  ->
                         match uu____8582 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8613 =
        let uu____8624 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8624 mapper in
      match uu____8613 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___131_8717 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___131_8717.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___131_8717.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8744 = lookup_qname env l in
      match uu____8744 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8783 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8833 = try_lookup_bv env bv in
      match uu____8833 with
      | FStar_Pervasives_Native.None  ->
          let uu____8848 =
            let uu____8849 =
              let uu____8854 = variable_not_found bv in (uu____8854, bvr) in
            FStar_Errors.Error uu____8849 in
          FStar_Exn.raise uu____8848
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8865 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8866 = FStar_Range.set_use_range r bvr in
          (uu____8865, uu____8866)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8885 = try_lookup_lid_aux env l in
      match uu____8885 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____8951 =
            let uu____8960 =
              let uu____8965 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____8965) in
            (uu____8960, r1) in
          FStar_Pervasives_Native.Some uu____8951
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8994 = try_lookup_lid env l in
      match uu____8994 with
      | FStar_Pervasives_Native.None  ->
          let uu____9021 =
            let uu____9022 =
              let uu____9027 = name_not_found l in
              (uu____9027, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9022 in
          FStar_Exn.raise uu____9021
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___116_9065  ->
              match uu___116_9065 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9067 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9084 = lookup_qname env lid in
      match uu____9084 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9113,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9116;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9118;
              FStar_Syntax_Syntax.sigattrs = uu____9119;_},FStar_Pervasives_Native.None
            ),uu____9120)
          ->
          let uu____9169 =
            let uu____9180 =
              let uu____9185 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9185) in
            (uu____9180, q) in
          FStar_Pervasives_Native.Some uu____9169
      | uu____9202 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9241 = lookup_qname env lid in
      match uu____9241 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9266,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9269;
              FStar_Syntax_Syntax.sigquals = uu____9270;
              FStar_Syntax_Syntax.sigmeta = uu____9271;
              FStar_Syntax_Syntax.sigattrs = uu____9272;_},FStar_Pervasives_Native.None
            ),uu____9273)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9322 ->
          let uu____9343 =
            let uu____9344 =
              let uu____9349 = name_not_found lid in
              (uu____9349, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9344 in
          FStar_Exn.raise uu____9343
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9366 = lookup_qname env lid in
      match uu____9366 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9391,uvs,t,uu____9394,uu____9395,uu____9396);
              FStar_Syntax_Syntax.sigrng = uu____9397;
              FStar_Syntax_Syntax.sigquals = uu____9398;
              FStar_Syntax_Syntax.sigmeta = uu____9399;
              FStar_Syntax_Syntax.sigattrs = uu____9400;_},FStar_Pervasives_Native.None
            ),uu____9401)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9454 ->
          let uu____9475 =
            let uu____9476 =
              let uu____9481 = name_not_found lid in
              (uu____9481, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9476 in
          FStar_Exn.raise uu____9475
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9500 = lookup_qname env lid in
      match uu____9500 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9527,uu____9528,uu____9529,uu____9530,uu____9531,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9533;
              FStar_Syntax_Syntax.sigquals = uu____9534;
              FStar_Syntax_Syntax.sigmeta = uu____9535;
              FStar_Syntax_Syntax.sigattrs = uu____9536;_},uu____9537),uu____9538)
          -> (true, dcs)
      | uu____9599 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9630 = lookup_qname env lid in
      match uu____9630 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9651,uu____9652,uu____9653,l,uu____9655,uu____9656);
              FStar_Syntax_Syntax.sigrng = uu____9657;
              FStar_Syntax_Syntax.sigquals = uu____9658;
              FStar_Syntax_Syntax.sigmeta = uu____9659;
              FStar_Syntax_Syntax.sigattrs = uu____9660;_},uu____9661),uu____9662)
          -> l
      | uu____9717 ->
          let uu____9738 =
            let uu____9739 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9739 in
          failwith uu____9738
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
        let uu____9776 = lookup_qname env lid in
        match uu____9776 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9804) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9855,lbs),uu____9857) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9885 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9885
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9917 -> FStar_Pervasives_Native.None)
        | uu____9922 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9959 = lookup_qname env ftv in
      match uu____9959 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9983) ->
          let uu____10028 = effect_signature se in
          (match uu____10028 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10049,t),r) ->
               let uu____10064 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10064)
      | uu____10065 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10094 = try_lookup_effect_lid env ftv in
      match uu____10094 with
      | FStar_Pervasives_Native.None  ->
          let uu____10097 =
            let uu____10098 =
              let uu____10103 = name_not_found ftv in
              (uu____10103, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10098 in
          FStar_Exn.raise uu____10097
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
        let uu____10123 = lookup_qname env lid0 in
        match uu____10123 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10154);
                FStar_Syntax_Syntax.sigrng = uu____10155;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10157;
                FStar_Syntax_Syntax.sigattrs = uu____10158;_},FStar_Pervasives_Native.None
              ),uu____10159)
            ->
            let lid1 =
              let uu____10213 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____10213 in
            let uu____10214 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_10218  ->
                      match uu___117_10218 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10219 -> false)) in
            if uu____10214
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10233 =
                      let uu____10234 =
                        let uu____10235 = get_range env in
                        FStar_Range.string_of_range uu____10235 in
                      let uu____10236 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10237 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10234 uu____10236 uu____10237 in
                    failwith uu____10233) in
               match (binders, univs1) with
               | ([],uu____10244) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10261,uu____10262::uu____10263::uu____10264) ->
                   let uu____10269 =
                     let uu____10270 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10271 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10270 uu____10271 in
                   failwith uu____10269
               | uu____10278 ->
                   let uu____10283 =
                     let uu____10288 =
                       let uu____10289 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10289) in
                     inst_tscheme_with uu____10288 insts in
                   (match uu____10283 with
                    | (uu____10300,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10303 =
                          let uu____10304 = FStar_Syntax_Subst.compress t1 in
                          uu____10304.FStar_Syntax_Syntax.n in
                        (match uu____10303 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10351 -> failwith "Impossible")))
        | uu____10358 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10400 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10400 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10413,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10420 = find1 l2 in
            (match uu____10420 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10427 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10427 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10431 = find1 l in
            (match uu____10431 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10447 = lookup_qname env l1 in
      match uu____10447 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10470;
              FStar_Syntax_Syntax.sigrng = uu____10471;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10473;
              FStar_Syntax_Syntax.sigattrs = uu____10474;_},uu____10475),uu____10476)
          -> q
      | uu____10527 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10563 =
          let uu____10564 =
            let uu____10565 = FStar_Util.string_of_int i in
            let uu____10566 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10565 uu____10566 in
          failwith uu____10564 in
        let uu____10567 = lookup_datacon env lid in
        match uu____10567 with
        | (uu____10572,t) ->
            let uu____10574 =
              let uu____10575 = FStar_Syntax_Subst.compress t in
              uu____10575.FStar_Syntax_Syntax.n in
            (match uu____10574 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10579) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10610 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10610
                      FStar_Pervasives_Native.fst)
             | uu____10619 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10628 = lookup_qname env l in
      match uu____10628 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10649,uu____10650,uu____10651);
              FStar_Syntax_Syntax.sigrng = uu____10652;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10654;
              FStar_Syntax_Syntax.sigattrs = uu____10655;_},uu____10656),uu____10657)
          ->
          FStar_Util.for_some
            (fun uu___118_10710  ->
               match uu___118_10710 with
               | FStar_Syntax_Syntax.Projector uu____10711 -> true
               | uu____10716 -> false) quals
      | uu____10717 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10746 = lookup_qname env lid in
      match uu____10746 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10767,uu____10768,uu____10769,uu____10770,uu____10771,uu____10772);
              FStar_Syntax_Syntax.sigrng = uu____10773;
              FStar_Syntax_Syntax.sigquals = uu____10774;
              FStar_Syntax_Syntax.sigmeta = uu____10775;
              FStar_Syntax_Syntax.sigattrs = uu____10776;_},uu____10777),uu____10778)
          -> true
      | uu____10833 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10862 = lookup_qname env lid in
      match uu____10862 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10883,uu____10884,uu____10885,uu____10886,uu____10887,uu____10888);
              FStar_Syntax_Syntax.sigrng = uu____10889;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10891;
              FStar_Syntax_Syntax.sigattrs = uu____10892;_},uu____10893),uu____10894)
          ->
          FStar_Util.for_some
            (fun uu___119_10955  ->
               match uu___119_10955 with
               | FStar_Syntax_Syntax.RecordType uu____10956 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10965 -> true
               | uu____10974 -> false) quals
      | uu____10975 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11004 = lookup_qname env lid in
      match uu____11004 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11025,uu____11026);
              FStar_Syntax_Syntax.sigrng = uu____11027;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11029;
              FStar_Syntax_Syntax.sigattrs = uu____11030;_},uu____11031),uu____11032)
          ->
          FStar_Util.for_some
            (fun uu___120_11089  ->
               match uu___120_11089 with
               | FStar_Syntax_Syntax.Action uu____11090 -> true
               | uu____11091 -> false) quals
      | uu____11092 -> false
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
      let uu____11124 =
        let uu____11125 = FStar_Syntax_Util.un_uinst head1 in
        uu____11125.FStar_Syntax_Syntax.n in
      match uu____11124 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11129 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11196 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11212) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11229 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11236 ->
                 FStar_Pervasives_Native.Some true
             | uu____11253 -> FStar_Pervasives_Native.Some false) in
      let uu____11254 =
        let uu____11257 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11257 mapper in
      match uu____11254 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11305 = lookup_qname env lid in
      match uu____11305 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11326,uu____11327,tps,uu____11329,uu____11330,uu____11331);
              FStar_Syntax_Syntax.sigrng = uu____11332;
              FStar_Syntax_Syntax.sigquals = uu____11333;
              FStar_Syntax_Syntax.sigmeta = uu____11334;
              FStar_Syntax_Syntax.sigattrs = uu____11335;_},uu____11336),uu____11337)
          -> FStar_List.length tps
      | uu____11400 ->
          let uu____11421 =
            let uu____11422 =
              let uu____11427 = name_not_found lid in
              (uu____11427, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11422 in
          FStar_Exn.raise uu____11421
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
           (fun uu____11469  ->
              match uu____11469 with
              | (d,uu____11477) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11490 = effect_decl_opt env l in
      match uu____11490 with
      | FStar_Pervasives_Native.None  ->
          let uu____11505 =
            let uu____11506 =
              let uu____11511 = name_not_found l in
              (uu____11511, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11506 in
          FStar_Exn.raise uu____11505
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
            (let uu____11577 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11630  ->
                       match uu____11630 with
                       | (m1,m2,uu____11643,uu____11644,uu____11645) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11577 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11662 =
                   let uu____11663 =
                     let uu____11668 =
                       let uu____11669 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11670 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11669
                         uu____11670 in
                     (uu____11668, (env.range)) in
                   FStar_Errors.Error uu____11663 in
                 FStar_Exn.raise uu____11662
             | FStar_Pervasives_Native.Some
                 (uu____11677,uu____11678,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11721 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11721)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11748 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11774  ->
                match uu____11774 with
                | (d,uu____11780) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11748 with
      | FStar_Pervasives_Native.None  ->
          let uu____11791 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11791
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11804 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11804 with
           | (uu____11815,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11825)::(wp,uu____11827)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11863 -> failwith "Impossible"))
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
                 let uu____11912 = get_range env in
                 let uu____11913 =
                   let uu____11916 =
                     let uu____11917 =
                       let uu____11932 =
                         let uu____11935 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11935] in
                       (null_wp, uu____11932) in
                     FStar_Syntax_Syntax.Tm_app uu____11917 in
                   FStar_Syntax_Syntax.mk uu____11916 in
                 uu____11913 FStar_Pervasives_Native.None uu____11912 in
               let uu____11941 =
                 let uu____11942 =
                   let uu____11951 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11951] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11942;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11941)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___132_11962 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___132_11962.order);
              joins = (uu___132_11962.joins)
            } in
          let uu___133_11971 = env in
          {
            solver = (uu___133_11971.solver);
            range = (uu___133_11971.range);
            curmodule = (uu___133_11971.curmodule);
            gamma = (uu___133_11971.gamma);
            gamma_cache = (uu___133_11971.gamma_cache);
            modules = (uu___133_11971.modules);
            expected_typ = (uu___133_11971.expected_typ);
            sigtab = (uu___133_11971.sigtab);
            is_pattern = (uu___133_11971.is_pattern);
            instantiate_imp = (uu___133_11971.instantiate_imp);
            effects;
            generalize = (uu___133_11971.generalize);
            letrecs = (uu___133_11971.letrecs);
            top_level = (uu___133_11971.top_level);
            check_uvars = (uu___133_11971.check_uvars);
            use_eq = (uu___133_11971.use_eq);
            is_iface = (uu___133_11971.is_iface);
            admit = (uu___133_11971.admit);
            lax = (uu___133_11971.lax);
            lax_universes = (uu___133_11971.lax_universes);
            failhard = (uu___133_11971.failhard);
            nosynth = (uu___133_11971.nosynth);
            tc_term = (uu___133_11971.tc_term);
            type_of = (uu___133_11971.type_of);
            universe_of = (uu___133_11971.universe_of);
            use_bv_sorts = (uu___133_11971.use_bv_sorts);
            qname_and_index = (uu___133_11971.qname_and_index);
            proof_ns = (uu___133_11971.proof_ns);
            synth = (uu___133_11971.synth);
            is_native_tactic = (uu___133_11971.is_native_tactic);
            identifier_info = (uu___133_11971.identifier_info)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____11988 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____11988 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12078 = (e1.mlift).mlift_wp t wp in
                              let uu____12079 = l1 t wp e in
                              l2 t uu____12078 uu____12079))
                | uu____12080 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12119 = inst_tscheme lift_t in
            match uu____12119 with
            | (uu____12126,lift_t1) ->
                let uu____12128 =
                  let uu____12131 =
                    let uu____12132 =
                      let uu____12147 =
                        let uu____12150 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12151 =
                          let uu____12154 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12154] in
                        uu____12150 :: uu____12151 in
                      (lift_t1, uu____12147) in
                    FStar_Syntax_Syntax.Tm_app uu____12132 in
                  FStar_Syntax_Syntax.mk uu____12131 in
                uu____12128 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12195 = inst_tscheme lift_t in
            match uu____12195 with
            | (uu____12202,lift_t1) ->
                let uu____12204 =
                  let uu____12207 =
                    let uu____12208 =
                      let uu____12223 =
                        let uu____12226 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12227 =
                          let uu____12230 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12231 =
                            let uu____12234 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12234] in
                          uu____12230 :: uu____12231 in
                        uu____12226 :: uu____12227 in
                      (lift_t1, uu____12223) in
                    FStar_Syntax_Syntax.Tm_app uu____12208 in
                  FStar_Syntax_Syntax.mk uu____12207 in
                uu____12204 FStar_Pervasives_Native.None
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
              let uu____12272 =
                let uu____12273 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12273
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12272 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12277 =
              let uu____12278 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12278 in
            let uu____12279 =
              let uu____12280 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12298 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12298) in
              FStar_Util.dflt "none" uu____12280 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12277
              uu____12279 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12324  ->
                    match uu____12324 with
                    | (e,uu____12332) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12351 =
            match uu____12351 with
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
              let uu____12389 =
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
                                    (let uu____12410 =
                                       let uu____12419 =
                                         find_edge order1 (i, k) in
                                       let uu____12422 =
                                         find_edge order1 (k, j) in
                                       (uu____12419, uu____12422) in
                                     match uu____12410 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12437 =
                                           compose_edges e1 e2 in
                                         [uu____12437]
                                     | uu____12438 -> []))))) in
              FStar_List.append order1 uu____12389 in
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
                   let uu____12467 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12469 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12469
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12467
                   then
                     let uu____12474 =
                       let uu____12475 =
                         let uu____12480 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12481 = get_range env in
                         (uu____12480, uu____12481) in
                       FStar_Errors.Error uu____12475 in
                     FStar_Exn.raise uu____12474
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
                                            let uu____12606 =
                                              let uu____12615 =
                                                find_edge order2 (i, k) in
                                              let uu____12618 =
                                                find_edge order2 (j, k) in
                                              (uu____12615, uu____12618) in
                                            match uu____12606 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12660,uu____12661)
                                                     ->
                                                     let uu____12668 =
                                                       let uu____12673 =
                                                         let uu____12674 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12674 in
                                                       let uu____12677 =
                                                         let uu____12678 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12678 in
                                                       (uu____12673,
                                                         uu____12677) in
                                                     (match uu____12668 with
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
                                            | uu____12713 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___134_12786 = env.effects in
              { decls = (uu___134_12786.decls); order = order2; joins } in
            let uu___135_12787 = env in
            {
              solver = (uu___135_12787.solver);
              range = (uu___135_12787.range);
              curmodule = (uu___135_12787.curmodule);
              gamma = (uu___135_12787.gamma);
              gamma_cache = (uu___135_12787.gamma_cache);
              modules = (uu___135_12787.modules);
              expected_typ = (uu___135_12787.expected_typ);
              sigtab = (uu___135_12787.sigtab);
              is_pattern = (uu___135_12787.is_pattern);
              instantiate_imp = (uu___135_12787.instantiate_imp);
              effects;
              generalize = (uu___135_12787.generalize);
              letrecs = (uu___135_12787.letrecs);
              top_level = (uu___135_12787.top_level);
              check_uvars = (uu___135_12787.check_uvars);
              use_eq = (uu___135_12787.use_eq);
              is_iface = (uu___135_12787.is_iface);
              admit = (uu___135_12787.admit);
              lax = (uu___135_12787.lax);
              lax_universes = (uu___135_12787.lax_universes);
              failhard = (uu___135_12787.failhard);
              nosynth = (uu___135_12787.nosynth);
              tc_term = (uu___135_12787.tc_term);
              type_of = (uu___135_12787.type_of);
              universe_of = (uu___135_12787.universe_of);
              use_bv_sorts = (uu___135_12787.use_bv_sorts);
              qname_and_index = (uu___135_12787.qname_and_index);
              proof_ns = (uu___135_12787.proof_ns);
              synth = (uu___135_12787.synth);
              is_native_tactic = (uu___135_12787.is_native_tactic);
              identifier_info = (uu___135_12787.identifier_info)
            }))
      | uu____12788 -> env
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
        | uu____12814 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12824 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12824 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12841 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12841 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12859 =
                     let uu____12860 =
                       let uu____12865 =
                         let uu____12866 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12871 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12878 =
                           let uu____12879 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12879 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12866 uu____12871 uu____12878 in
                       (uu____12865, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12860 in
                   FStar_Exn.raise uu____12859)
                else ();
                (let inst1 =
                   let uu____12884 =
                     let uu____12893 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12893 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12910  ->
                        fun uu____12911  ->
                          match (uu____12910, uu____12911) with
                          | ((x,uu____12933),(t,uu____12935)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12884 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12954 =
                     let uu___136_12955 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___136_12955.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___136_12955.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___136_12955.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___136_12955.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12954
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
          let uu____12981 = effect_decl_opt env effect_name in
          match uu____12981 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13014 =
                only_reifiable &&
                  (let uu____13016 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13016) in
              if uu____13014
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13032 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13051 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13080 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13080
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13081 =
                             let uu____13082 =
                               let uu____13087 = get_range env in
                               (message, uu____13087) in
                             FStar_Errors.Error uu____13082 in
                           FStar_Exn.raise uu____13081 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13097 =
                       let uu____13100 = get_range env in
                       let uu____13101 =
                         let uu____13104 =
                           let uu____13105 =
                             let uu____13120 =
                               let uu____13123 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13123; wp] in
                             (repr, uu____13120) in
                           FStar_Syntax_Syntax.Tm_app uu____13105 in
                         FStar_Syntax_Syntax.mk uu____13104 in
                       uu____13101 FStar_Pervasives_Native.None uu____13100 in
                     FStar_Pervasives_Native.Some uu____13097)
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
          let uu____13175 =
            let uu____13176 =
              let uu____13181 =
                let uu____13182 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13182 in
              let uu____13183 = get_range env in (uu____13181, uu____13183) in
            FStar_Errors.Error uu____13176 in
          FStar_Exn.raise uu____13175 in
        let uu____13184 = effect_repr_aux true env c u_c in
        match uu____13184 with
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
      | uu____13224 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13233 =
        let uu____13234 = FStar_Syntax_Subst.compress t in
        uu____13234.FStar_Syntax_Syntax.n in
      match uu____13233 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13237,c) ->
          is_reifiable_comp env c
      | uu____13255 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13279)::uu____13280 -> x :: rest
        | (Binding_sig_inst uu____13289)::uu____13290 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13305 = push1 x rest1 in local :: uu____13305 in
      let uu___137_13308 = env in
      let uu____13309 = push1 s env.gamma in
      {
        solver = (uu___137_13308.solver);
        range = (uu___137_13308.range);
        curmodule = (uu___137_13308.curmodule);
        gamma = uu____13309;
        gamma_cache = (uu___137_13308.gamma_cache);
        modules = (uu___137_13308.modules);
        expected_typ = (uu___137_13308.expected_typ);
        sigtab = (uu___137_13308.sigtab);
        is_pattern = (uu___137_13308.is_pattern);
        instantiate_imp = (uu___137_13308.instantiate_imp);
        effects = (uu___137_13308.effects);
        generalize = (uu___137_13308.generalize);
        letrecs = (uu___137_13308.letrecs);
        top_level = (uu___137_13308.top_level);
        check_uvars = (uu___137_13308.check_uvars);
        use_eq = (uu___137_13308.use_eq);
        is_iface = (uu___137_13308.is_iface);
        admit = (uu___137_13308.admit);
        lax = (uu___137_13308.lax);
        lax_universes = (uu___137_13308.lax_universes);
        failhard = (uu___137_13308.failhard);
        nosynth = (uu___137_13308.nosynth);
        tc_term = (uu___137_13308.tc_term);
        type_of = (uu___137_13308.type_of);
        universe_of = (uu___137_13308.universe_of);
        use_bv_sorts = (uu___137_13308.use_bv_sorts);
        qname_and_index = (uu___137_13308.qname_and_index);
        proof_ns = (uu___137_13308.proof_ns);
        synth = (uu___137_13308.synth);
        is_native_tactic = (uu___137_13308.is_native_tactic);
        identifier_info = (uu___137_13308.identifier_info)
      }
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
      let uu___138_13346 = env in
      {
        solver = (uu___138_13346.solver);
        range = (uu___138_13346.range);
        curmodule = (uu___138_13346.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___138_13346.gamma_cache);
        modules = (uu___138_13346.modules);
        expected_typ = (uu___138_13346.expected_typ);
        sigtab = (uu___138_13346.sigtab);
        is_pattern = (uu___138_13346.is_pattern);
        instantiate_imp = (uu___138_13346.instantiate_imp);
        effects = (uu___138_13346.effects);
        generalize = (uu___138_13346.generalize);
        letrecs = (uu___138_13346.letrecs);
        top_level = (uu___138_13346.top_level);
        check_uvars = (uu___138_13346.check_uvars);
        use_eq = (uu___138_13346.use_eq);
        is_iface = (uu___138_13346.is_iface);
        admit = (uu___138_13346.admit);
        lax = (uu___138_13346.lax);
        lax_universes = (uu___138_13346.lax_universes);
        failhard = (uu___138_13346.failhard);
        nosynth = (uu___138_13346.nosynth);
        tc_term = (uu___138_13346.tc_term);
        type_of = (uu___138_13346.type_of);
        universe_of = (uu___138_13346.universe_of);
        use_bv_sorts = (uu___138_13346.use_bv_sorts);
        qname_and_index = (uu___138_13346.qname_and_index);
        proof_ns = (uu___138_13346.proof_ns);
        synth = (uu___138_13346.synth);
        is_native_tactic = (uu___138_13346.is_native_tactic);
        identifier_info = (uu___138_13346.identifier_info)
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
            (let uu___139_13380 = env in
             {
               solver = (uu___139_13380.solver);
               range = (uu___139_13380.range);
               curmodule = (uu___139_13380.curmodule);
               gamma = rest;
               gamma_cache = (uu___139_13380.gamma_cache);
               modules = (uu___139_13380.modules);
               expected_typ = (uu___139_13380.expected_typ);
               sigtab = (uu___139_13380.sigtab);
               is_pattern = (uu___139_13380.is_pattern);
               instantiate_imp = (uu___139_13380.instantiate_imp);
               effects = (uu___139_13380.effects);
               generalize = (uu___139_13380.generalize);
               letrecs = (uu___139_13380.letrecs);
               top_level = (uu___139_13380.top_level);
               check_uvars = (uu___139_13380.check_uvars);
               use_eq = (uu___139_13380.use_eq);
               is_iface = (uu___139_13380.is_iface);
               admit = (uu___139_13380.admit);
               lax = (uu___139_13380.lax);
               lax_universes = (uu___139_13380.lax_universes);
               failhard = (uu___139_13380.failhard);
               nosynth = (uu___139_13380.nosynth);
               tc_term = (uu___139_13380.tc_term);
               type_of = (uu___139_13380.type_of);
               universe_of = (uu___139_13380.universe_of);
               use_bv_sorts = (uu___139_13380.use_bv_sorts);
               qname_and_index = (uu___139_13380.qname_and_index);
               proof_ns = (uu___139_13380.proof_ns);
               synth = (uu___139_13380.synth);
               is_native_tactic = (uu___139_13380.is_native_tactic);
               identifier_info = (uu___139_13380.identifier_info)
             }))
    | uu____13381 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13405  ->
             match uu____13405 with | (x,uu____13411) -> push_bv env1 x) env
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
            let uu___140_13441 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_13441.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_13441.FStar_Syntax_Syntax.index);
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
      (let uu___141_13476 = env in
       {
         solver = (uu___141_13476.solver);
         range = (uu___141_13476.range);
         curmodule = (uu___141_13476.curmodule);
         gamma = [];
         gamma_cache = (uu___141_13476.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___141_13476.sigtab);
         is_pattern = (uu___141_13476.is_pattern);
         instantiate_imp = (uu___141_13476.instantiate_imp);
         effects = (uu___141_13476.effects);
         generalize = (uu___141_13476.generalize);
         letrecs = (uu___141_13476.letrecs);
         top_level = (uu___141_13476.top_level);
         check_uvars = (uu___141_13476.check_uvars);
         use_eq = (uu___141_13476.use_eq);
         is_iface = (uu___141_13476.is_iface);
         admit = (uu___141_13476.admit);
         lax = (uu___141_13476.lax);
         lax_universes = (uu___141_13476.lax_universes);
         failhard = (uu___141_13476.failhard);
         nosynth = (uu___141_13476.nosynth);
         tc_term = (uu___141_13476.tc_term);
         type_of = (uu___141_13476.type_of);
         universe_of = (uu___141_13476.universe_of);
         use_bv_sorts = (uu___141_13476.use_bv_sorts);
         qname_and_index = (uu___141_13476.qname_and_index);
         proof_ns = (uu___141_13476.proof_ns);
         synth = (uu___141_13476.synth);
         is_native_tactic = (uu___141_13476.is_native_tactic);
         identifier_info = (uu___141_13476.identifier_info)
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
        let uu____13513 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13513 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13541 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13541)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___142_13556 = env in
      {
        solver = (uu___142_13556.solver);
        range = (uu___142_13556.range);
        curmodule = (uu___142_13556.curmodule);
        gamma = (uu___142_13556.gamma);
        gamma_cache = (uu___142_13556.gamma_cache);
        modules = (uu___142_13556.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___142_13556.sigtab);
        is_pattern = (uu___142_13556.is_pattern);
        instantiate_imp = (uu___142_13556.instantiate_imp);
        effects = (uu___142_13556.effects);
        generalize = (uu___142_13556.generalize);
        letrecs = (uu___142_13556.letrecs);
        top_level = (uu___142_13556.top_level);
        check_uvars = (uu___142_13556.check_uvars);
        use_eq = false;
        is_iface = (uu___142_13556.is_iface);
        admit = (uu___142_13556.admit);
        lax = (uu___142_13556.lax);
        lax_universes = (uu___142_13556.lax_universes);
        failhard = (uu___142_13556.failhard);
        nosynth = (uu___142_13556.nosynth);
        tc_term = (uu___142_13556.tc_term);
        type_of = (uu___142_13556.type_of);
        universe_of = (uu___142_13556.universe_of);
        use_bv_sorts = (uu___142_13556.use_bv_sorts);
        qname_and_index = (uu___142_13556.qname_and_index);
        proof_ns = (uu___142_13556.proof_ns);
        synth = (uu___142_13556.synth);
        is_native_tactic = (uu___142_13556.is_native_tactic);
        identifier_info = (uu___142_13556.identifier_info)
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
    let uu____13582 = expected_typ env_ in
    ((let uu___143_13588 = env_ in
      {
        solver = (uu___143_13588.solver);
        range = (uu___143_13588.range);
        curmodule = (uu___143_13588.curmodule);
        gamma = (uu___143_13588.gamma);
        gamma_cache = (uu___143_13588.gamma_cache);
        modules = (uu___143_13588.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___143_13588.sigtab);
        is_pattern = (uu___143_13588.is_pattern);
        instantiate_imp = (uu___143_13588.instantiate_imp);
        effects = (uu___143_13588.effects);
        generalize = (uu___143_13588.generalize);
        letrecs = (uu___143_13588.letrecs);
        top_level = (uu___143_13588.top_level);
        check_uvars = (uu___143_13588.check_uvars);
        use_eq = false;
        is_iface = (uu___143_13588.is_iface);
        admit = (uu___143_13588.admit);
        lax = (uu___143_13588.lax);
        lax_universes = (uu___143_13588.lax_universes);
        failhard = (uu___143_13588.failhard);
        nosynth = (uu___143_13588.nosynth);
        tc_term = (uu___143_13588.tc_term);
        type_of = (uu___143_13588.type_of);
        universe_of = (uu___143_13588.universe_of);
        use_bv_sorts = (uu___143_13588.use_bv_sorts);
        qname_and_index = (uu___143_13588.qname_and_index);
        proof_ns = (uu___143_13588.proof_ns);
        synth = (uu___143_13588.synth);
        is_native_tactic = (uu___143_13588.is_native_tactic);
        identifier_info = (uu___143_13588.identifier_info)
      }), uu____13582)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13603 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___121_13613  ->
                    match uu___121_13613 with
                    | Binding_sig (uu____13616,se) -> [se]
                    | uu____13622 -> [])) in
          FStar_All.pipe_right uu____13603 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___144_13629 = env in
       {
         solver = (uu___144_13629.solver);
         range = (uu___144_13629.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___144_13629.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___144_13629.expected_typ);
         sigtab = (uu___144_13629.sigtab);
         is_pattern = (uu___144_13629.is_pattern);
         instantiate_imp = (uu___144_13629.instantiate_imp);
         effects = (uu___144_13629.effects);
         generalize = (uu___144_13629.generalize);
         letrecs = (uu___144_13629.letrecs);
         top_level = (uu___144_13629.top_level);
         check_uvars = (uu___144_13629.check_uvars);
         use_eq = (uu___144_13629.use_eq);
         is_iface = (uu___144_13629.is_iface);
         admit = (uu___144_13629.admit);
         lax = (uu___144_13629.lax);
         lax_universes = (uu___144_13629.lax_universes);
         failhard = (uu___144_13629.failhard);
         nosynth = (uu___144_13629.nosynth);
         tc_term = (uu___144_13629.tc_term);
         type_of = (uu___144_13629.type_of);
         universe_of = (uu___144_13629.universe_of);
         use_bv_sorts = (uu___144_13629.use_bv_sorts);
         qname_and_index = (uu___144_13629.qname_and_index);
         proof_ns = (uu___144_13629.proof_ns);
         synth = (uu___144_13629.synth);
         is_native_tactic = (uu___144_13629.is_native_tactic);
         identifier_info = (uu___144_13629.identifier_info)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13711)::tl1 -> aux out tl1
      | (Binding_lid (uu____13715,(uu____13716,t)))::tl1 ->
          let uu____13731 =
            let uu____13738 = FStar_Syntax_Free.uvars t in
            ext out uu____13738 in
          aux uu____13731 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13745;
            FStar_Syntax_Syntax.index = uu____13746;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13753 =
            let uu____13760 = FStar_Syntax_Free.uvars t in
            ext out uu____13760 in
          aux uu____13753 tl1
      | (Binding_sig uu____13767)::uu____13768 -> out
      | (Binding_sig_inst uu____13777)::uu____13778 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13834)::tl1 -> aux out tl1
      | (Binding_univ uu____13846)::tl1 -> aux out tl1
      | (Binding_lid (uu____13850,(uu____13851,t)))::tl1 ->
          let uu____13866 =
            let uu____13869 = FStar_Syntax_Free.univs t in
            ext out uu____13869 in
          aux uu____13866 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13872;
            FStar_Syntax_Syntax.index = uu____13873;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13880 =
            let uu____13883 = FStar_Syntax_Free.univs t in
            ext out uu____13883 in
          aux uu____13880 tl1
      | (Binding_sig uu____13886)::uu____13887 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13941)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13957 = FStar_Util.fifo_set_add uname out in
          aux uu____13957 tl1
      | (Binding_lid (uu____13960,(uu____13961,t)))::tl1 ->
          let uu____13976 =
            let uu____13979 = FStar_Syntax_Free.univnames t in
            ext out uu____13979 in
          aux uu____13976 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13982;
            FStar_Syntax_Syntax.index = uu____13983;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13990 =
            let uu____13993 = FStar_Syntax_Free.univnames t in
            ext out uu____13993 in
          aux uu____13990 tl1
      | (Binding_sig uu____13996)::uu____13997 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___122_14022  ->
            match uu___122_14022 with
            | Binding_var x -> [x]
            | Binding_lid uu____14026 -> []
            | Binding_sig uu____14031 -> []
            | Binding_univ uu____14038 -> []
            | Binding_sig_inst uu____14039 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14056 =
      let uu____14059 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14059
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14056 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14084 =
      let uu____14085 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___123_14095  ->
                match uu___123_14095 with
                | Binding_var x ->
                    let uu____14097 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14097
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14100) ->
                    let uu____14101 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14101
                | Binding_sig (ls,uu____14103) ->
                    let uu____14108 =
                      let uu____14109 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14109
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14108
                | Binding_sig_inst (ls,uu____14119,uu____14120) ->
                    let uu____14125 =
                      let uu____14126 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14126
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14125)) in
      FStar_All.pipe_right uu____14085 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14084 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14145 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14145
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14173  ->
                 fun uu____14174  ->
                   match (uu____14173, uu____14174) with
                   | ((b1,uu____14192),(b2,uu____14194)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___124_14241  ->
    match uu___124_14241 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14242 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___125_14261  ->
             match uu___125_14261 with
             | Binding_sig (lids,uu____14267) -> FStar_List.append lids keys
             | uu____14272 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14278  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14314) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14333,uu____14334) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____14371 = list_prefix p path1 in
            if uu____14371 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14385 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14385
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___145_14415 = e in
            {
              solver = (uu___145_14415.solver);
              range = (uu___145_14415.range);
              curmodule = (uu___145_14415.curmodule);
              gamma = (uu___145_14415.gamma);
              gamma_cache = (uu___145_14415.gamma_cache);
              modules = (uu___145_14415.modules);
              expected_typ = (uu___145_14415.expected_typ);
              sigtab = (uu___145_14415.sigtab);
              is_pattern = (uu___145_14415.is_pattern);
              instantiate_imp = (uu___145_14415.instantiate_imp);
              effects = (uu___145_14415.effects);
              generalize = (uu___145_14415.generalize);
              letrecs = (uu___145_14415.letrecs);
              top_level = (uu___145_14415.top_level);
              check_uvars = (uu___145_14415.check_uvars);
              use_eq = (uu___145_14415.use_eq);
              is_iface = (uu___145_14415.is_iface);
              admit = (uu___145_14415.admit);
              lax = (uu___145_14415.lax);
              lax_universes = (uu___145_14415.lax_universes);
              failhard = (uu___145_14415.failhard);
              nosynth = (uu___145_14415.nosynth);
              tc_term = (uu___145_14415.tc_term);
              type_of = (uu___145_14415.type_of);
              universe_of = (uu___145_14415.universe_of);
              use_bv_sorts = (uu___145_14415.use_bv_sorts);
              qname_and_index = (uu___145_14415.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___145_14415.synth);
              is_native_tactic = (uu___145_14415.is_native_tactic);
              identifier_info = (uu___145_14415.identifier_info)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___146_14442 = e in
    {
      solver = (uu___146_14442.solver);
      range = (uu___146_14442.range);
      curmodule = (uu___146_14442.curmodule);
      gamma = (uu___146_14442.gamma);
      gamma_cache = (uu___146_14442.gamma_cache);
      modules = (uu___146_14442.modules);
      expected_typ = (uu___146_14442.expected_typ);
      sigtab = (uu___146_14442.sigtab);
      is_pattern = (uu___146_14442.is_pattern);
      instantiate_imp = (uu___146_14442.instantiate_imp);
      effects = (uu___146_14442.effects);
      generalize = (uu___146_14442.generalize);
      letrecs = (uu___146_14442.letrecs);
      top_level = (uu___146_14442.top_level);
      check_uvars = (uu___146_14442.check_uvars);
      use_eq = (uu___146_14442.use_eq);
      is_iface = (uu___146_14442.is_iface);
      admit = (uu___146_14442.admit);
      lax = (uu___146_14442.lax);
      lax_universes = (uu___146_14442.lax_universes);
      failhard = (uu___146_14442.failhard);
      nosynth = (uu___146_14442.nosynth);
      tc_term = (uu___146_14442.tc_term);
      type_of = (uu___146_14442.type_of);
      universe_of = (uu___146_14442.universe_of);
      use_bv_sorts = (uu___146_14442.use_bv_sorts);
      qname_and_index = (uu___146_14442.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___146_14442.synth);
      is_native_tactic = (uu___146_14442.is_native_tactic);
      identifier_info = (uu___146_14442.identifier_info)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14457::rest ->
        let uu___147_14461 = e in
        {
          solver = (uu___147_14461.solver);
          range = (uu___147_14461.range);
          curmodule = (uu___147_14461.curmodule);
          gamma = (uu___147_14461.gamma);
          gamma_cache = (uu___147_14461.gamma_cache);
          modules = (uu___147_14461.modules);
          expected_typ = (uu___147_14461.expected_typ);
          sigtab = (uu___147_14461.sigtab);
          is_pattern = (uu___147_14461.is_pattern);
          instantiate_imp = (uu___147_14461.instantiate_imp);
          effects = (uu___147_14461.effects);
          generalize = (uu___147_14461.generalize);
          letrecs = (uu___147_14461.letrecs);
          top_level = (uu___147_14461.top_level);
          check_uvars = (uu___147_14461.check_uvars);
          use_eq = (uu___147_14461.use_eq);
          is_iface = (uu___147_14461.is_iface);
          admit = (uu___147_14461.admit);
          lax = (uu___147_14461.lax);
          lax_universes = (uu___147_14461.lax_universes);
          failhard = (uu___147_14461.failhard);
          nosynth = (uu___147_14461.nosynth);
          tc_term = (uu___147_14461.tc_term);
          type_of = (uu___147_14461.type_of);
          universe_of = (uu___147_14461.universe_of);
          use_bv_sorts = (uu___147_14461.use_bv_sorts);
          qname_and_index = (uu___147_14461.qname_and_index);
          proof_ns = rest;
          synth = (uu___147_14461.synth);
          is_native_tactic = (uu___147_14461.is_native_tactic);
          identifier_info = (uu___147_14461.identifier_info)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___148_14474 = e in
      {
        solver = (uu___148_14474.solver);
        range = (uu___148_14474.range);
        curmodule = (uu___148_14474.curmodule);
        gamma = (uu___148_14474.gamma);
        gamma_cache = (uu___148_14474.gamma_cache);
        modules = (uu___148_14474.modules);
        expected_typ = (uu___148_14474.expected_typ);
        sigtab = (uu___148_14474.sigtab);
        is_pattern = (uu___148_14474.is_pattern);
        instantiate_imp = (uu___148_14474.instantiate_imp);
        effects = (uu___148_14474.effects);
        generalize = (uu___148_14474.generalize);
        letrecs = (uu___148_14474.letrecs);
        top_level = (uu___148_14474.top_level);
        check_uvars = (uu___148_14474.check_uvars);
        use_eq = (uu___148_14474.use_eq);
        is_iface = (uu___148_14474.is_iface);
        admit = (uu___148_14474.admit);
        lax = (uu___148_14474.lax);
        lax_universes = (uu___148_14474.lax_universes);
        failhard = (uu___148_14474.failhard);
        nosynth = (uu___148_14474.nosynth);
        tc_term = (uu___148_14474.tc_term);
        type_of = (uu___148_14474.type_of);
        universe_of = (uu___148_14474.universe_of);
        use_bv_sorts = (uu___148_14474.use_bv_sorts);
        qname_and_index = (uu___148_14474.qname_and_index);
        proof_ns = ns;
        synth = (uu___148_14474.synth);
        is_native_tactic = (uu___148_14474.is_native_tactic);
        identifier_info = (uu___148_14474.identifier_info)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14503 =
        FStar_List.map
          (fun fpns  ->
             let uu____14525 =
               let uu____14526 =
                 let uu____14527 =
                   FStar_List.map
                     (fun uu____14539  ->
                        match uu____14539 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14527 in
               Prims.strcat uu____14526 "]" in
             Prims.strcat "[" uu____14525) pns in
      FStar_String.concat ";" uu____14503 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14555  -> ());
    push = (fun uu____14557  -> ());
    pop = (fun uu____14559  -> ());
    mark = (fun uu____14561  -> ());
    reset_mark = (fun uu____14563  -> ());
    commit_mark = (fun uu____14565  -> ());
    encode_modul = (fun uu____14568  -> fun uu____14569  -> ());
    encode_sig = (fun uu____14572  -> fun uu____14573  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14579 =
             let uu____14586 = FStar_Options.peek () in (e, g, uu____14586) in
           [uu____14579]);
    solve = (fun uu____14602  -> fun uu____14603  -> fun uu____14604  -> ());
    is_trivial = (fun uu____14611  -> fun uu____14612  -> false);
    finish = (fun uu____14614  -> ());
    refresh = (fun uu____14616  -> ())
  }