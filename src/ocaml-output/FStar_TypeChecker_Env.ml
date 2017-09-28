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
      | (NoDelta ,uu____4759) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4760,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4761,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4762 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4771 . Prims.unit -> 'Auu____4771 FStar_Util.smap =
  fun uu____4777  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4782 . Prims.unit -> 'Auu____4782 FStar_Util.smap =
  fun uu____4788  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____4863 = new_gamma_cache () in
            let uu____4866 = new_sigtab () in
            let uu____4869 =
              let uu____4870 = FStar_Options.using_facts_from () in
              match uu____4870 with
              | FStar_Pervasives_Native.Some ns ->
                  let uu____4880 =
                    let uu____4889 =
                      FStar_List.map
                        (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                    FStar_List.append uu____4889 [([], false)] in
                  [uu____4880]
              | FStar_Pervasives_Native.None  -> [[]] in
            let uu____4962 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____4863;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____4866;
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
              proof_ns = uu____4869;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____4996  -> false);
              identifier_info = uu____4962
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
  fun uu____5067  ->
    let uu____5068 = FStar_ST.op_Bang query_indices in
    match uu____5068 with
    | [] -> failwith "Empty query indices!"
    | uu____5145 ->
        let uu____5154 =
          let uu____5163 =
            let uu____5170 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5170 in
          let uu____5247 = FStar_ST.op_Bang query_indices in uu____5163 ::
            uu____5247 in
        FStar_ST.op_Colon_Equals query_indices uu____5154
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5389  ->
    let uu____5390 = FStar_ST.op_Bang query_indices in
    match uu____5390 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5558  ->
    match uu____5558 with
    | (l,n1) ->
        let uu____5565 = FStar_ST.op_Bang query_indices in
        (match uu____5565 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5730 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5748  ->
    let uu____5749 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5749
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5844 =
       let uu____5847 = FStar_ST.op_Bang stack in env :: uu____5847 in
     FStar_ST.op_Colon_Equals stack uu____5844);
    (let uu___126_5950 = env in
     let uu____5951 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5954 = FStar_Util.smap_copy (sigtab env) in
     let uu____5957 =
       let uu____5960 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5960 in
     {
       solver = (uu___126_5950.solver);
       range = (uu___126_5950.range);
       curmodule = (uu___126_5950.curmodule);
       gamma = (uu___126_5950.gamma);
       gamma_cache = uu____5951;
       modules = (uu___126_5950.modules);
       expected_typ = (uu___126_5950.expected_typ);
       sigtab = uu____5954;
       is_pattern = (uu___126_5950.is_pattern);
       instantiate_imp = (uu___126_5950.instantiate_imp);
       effects = (uu___126_5950.effects);
       generalize = (uu___126_5950.generalize);
       letrecs = (uu___126_5950.letrecs);
       top_level = (uu___126_5950.top_level);
       check_uvars = (uu___126_5950.check_uvars);
       use_eq = (uu___126_5950.use_eq);
       is_iface = (uu___126_5950.is_iface);
       admit = (uu___126_5950.admit);
       lax = (uu___126_5950.lax);
       lax_universes = (uu___126_5950.lax_universes);
       failhard = (uu___126_5950.failhard);
       nosynth = (uu___126_5950.nosynth);
       tc_term = (uu___126_5950.tc_term);
       type_of = (uu___126_5950.type_of);
       universe_of = (uu___126_5950.universe_of);
       use_bv_sorts = (uu___126_5950.use_bv_sorts);
       qname_and_index = (uu___126_5950.qname_and_index);
       proof_ns = (uu___126_5950.proof_ns);
       synth = (uu___126_5950.synth);
       is_native_tactic = (uu___126_5950.is_native_tactic);
       identifier_info = uu____5957
     })
let pop_stack: Prims.unit -> env =
  fun uu____6024  ->
    let uu____6025 = FStar_ST.op_Bang stack in
    match uu____6025 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6133 -> failwith "Impossible: Too many pops"
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
        let uu____6181 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6207  ->
                  match uu____6207 with
                  | (m,uu____6213) -> FStar_Ident.lid_equals l m)) in
        (match uu____6181 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___127_6220 = env in
               {
                 solver = (uu___127_6220.solver);
                 range = (uu___127_6220.range);
                 curmodule = (uu___127_6220.curmodule);
                 gamma = (uu___127_6220.gamma);
                 gamma_cache = (uu___127_6220.gamma_cache);
                 modules = (uu___127_6220.modules);
                 expected_typ = (uu___127_6220.expected_typ);
                 sigtab = (uu___127_6220.sigtab);
                 is_pattern = (uu___127_6220.is_pattern);
                 instantiate_imp = (uu___127_6220.instantiate_imp);
                 effects = (uu___127_6220.effects);
                 generalize = (uu___127_6220.generalize);
                 letrecs = (uu___127_6220.letrecs);
                 top_level = (uu___127_6220.top_level);
                 check_uvars = (uu___127_6220.check_uvars);
                 use_eq = (uu___127_6220.use_eq);
                 is_iface = (uu___127_6220.is_iface);
                 admit = (uu___127_6220.admit);
                 lax = (uu___127_6220.lax);
                 lax_universes = (uu___127_6220.lax_universes);
                 failhard = (uu___127_6220.failhard);
                 nosynth = (uu___127_6220.nosynth);
                 tc_term = (uu___127_6220.tc_term);
                 type_of = (uu___127_6220.type_of);
                 universe_of = (uu___127_6220.universe_of);
                 use_bv_sorts = (uu___127_6220.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___127_6220.proof_ns);
                 synth = (uu___127_6220.synth);
                 is_native_tactic = (uu___127_6220.is_native_tactic);
                 identifier_info = (uu___127_6220.identifier_info)
               }))
         | FStar_Pervasives_Native.Some (uu____6225,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___128_6233 = env in
               {
                 solver = (uu___128_6233.solver);
                 range = (uu___128_6233.range);
                 curmodule = (uu___128_6233.curmodule);
                 gamma = (uu___128_6233.gamma);
                 gamma_cache = (uu___128_6233.gamma_cache);
                 modules = (uu___128_6233.modules);
                 expected_typ = (uu___128_6233.expected_typ);
                 sigtab = (uu___128_6233.sigtab);
                 is_pattern = (uu___128_6233.is_pattern);
                 instantiate_imp = (uu___128_6233.instantiate_imp);
                 effects = (uu___128_6233.effects);
                 generalize = (uu___128_6233.generalize);
                 letrecs = (uu___128_6233.letrecs);
                 top_level = (uu___128_6233.top_level);
                 check_uvars = (uu___128_6233.check_uvars);
                 use_eq = (uu___128_6233.use_eq);
                 is_iface = (uu___128_6233.is_iface);
                 admit = (uu___128_6233.admit);
                 lax = (uu___128_6233.lax);
                 lax_universes = (uu___128_6233.lax_universes);
                 failhard = (uu___128_6233.failhard);
                 nosynth = (uu___128_6233.nosynth);
                 tc_term = (uu___128_6233.tc_term);
                 type_of = (uu___128_6233.type_of);
                 universe_of = (uu___128_6233.universe_of);
                 use_bv_sorts = (uu___128_6233.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___128_6233.proof_ns);
                 synth = (uu___128_6233.synth);
                 is_native_tactic = (uu___128_6233.is_native_tactic);
                 identifier_info = (uu___128_6233.identifier_info)
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
        (let uu___129_6255 = e in
         {
           solver = (uu___129_6255.solver);
           range = r;
           curmodule = (uu___129_6255.curmodule);
           gamma = (uu___129_6255.gamma);
           gamma_cache = (uu___129_6255.gamma_cache);
           modules = (uu___129_6255.modules);
           expected_typ = (uu___129_6255.expected_typ);
           sigtab = (uu___129_6255.sigtab);
           is_pattern = (uu___129_6255.is_pattern);
           instantiate_imp = (uu___129_6255.instantiate_imp);
           effects = (uu___129_6255.effects);
           generalize = (uu___129_6255.generalize);
           letrecs = (uu___129_6255.letrecs);
           top_level = (uu___129_6255.top_level);
           check_uvars = (uu___129_6255.check_uvars);
           use_eq = (uu___129_6255.use_eq);
           is_iface = (uu___129_6255.is_iface);
           admit = (uu___129_6255.admit);
           lax = (uu___129_6255.lax);
           lax_universes = (uu___129_6255.lax_universes);
           failhard = (uu___129_6255.failhard);
           nosynth = (uu___129_6255.nosynth);
           tc_term = (uu___129_6255.tc_term);
           type_of = (uu___129_6255.type_of);
           universe_of = (uu___129_6255.universe_of);
           use_bv_sorts = (uu___129_6255.use_bv_sorts);
           qname_and_index = (uu___129_6255.qname_and_index);
           proof_ns = (uu___129_6255.proof_ns);
           synth = (uu___129_6255.synth);
           is_native_tactic = (uu___129_6255.is_native_tactic);
           identifier_info = (uu___129_6255.identifier_info)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6268 =
        let uu____6269 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6269 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6268
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6374 =
          let uu____6375 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6375 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6374
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6480 =
          let uu____6481 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6481 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6480
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6587 =
        let uu____6588 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6588 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6587
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___130_6699 = env in
      {
        solver = (uu___130_6699.solver);
        range = (uu___130_6699.range);
        curmodule = lid;
        gamma = (uu___130_6699.gamma);
        gamma_cache = (uu___130_6699.gamma_cache);
        modules = (uu___130_6699.modules);
        expected_typ = (uu___130_6699.expected_typ);
        sigtab = (uu___130_6699.sigtab);
        is_pattern = (uu___130_6699.is_pattern);
        instantiate_imp = (uu___130_6699.instantiate_imp);
        effects = (uu___130_6699.effects);
        generalize = (uu___130_6699.generalize);
        letrecs = (uu___130_6699.letrecs);
        top_level = (uu___130_6699.top_level);
        check_uvars = (uu___130_6699.check_uvars);
        use_eq = (uu___130_6699.use_eq);
        is_iface = (uu___130_6699.is_iface);
        admit = (uu___130_6699.admit);
        lax = (uu___130_6699.lax);
        lax_universes = (uu___130_6699.lax_universes);
        failhard = (uu___130_6699.failhard);
        nosynth = (uu___130_6699.nosynth);
        tc_term = (uu___130_6699.tc_term);
        type_of = (uu___130_6699.type_of);
        universe_of = (uu___130_6699.universe_of);
        use_bv_sorts = (uu___130_6699.use_bv_sorts);
        qname_and_index = (uu___130_6699.qname_and_index);
        proof_ns = (uu___130_6699.proof_ns);
        synth = (uu___130_6699.synth);
        is_native_tactic = (uu___130_6699.is_native_tactic);
        identifier_info = (uu___130_6699.identifier_info)
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
    let uu____6730 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6730
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6734  ->
    let uu____6735 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6735
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
      | ((formals,t),uu____6775) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6799 = FStar_Syntax_Subst.subst vs t in (us, uu____6799)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___113_6813  ->
    match uu___113_6813 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6837  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6852 = inst_tscheme t in
      match uu____6852 with
      | (us,t1) ->
          let uu____6863 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6863)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6879  ->
          match uu____6879 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6894 =
                         let uu____6895 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6896 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6897 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6898 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6895 uu____6896 uu____6897 uu____6898 in
                       failwith uu____6894)
                    else ();
                    (let uu____6900 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6900))
               | uu____6907 ->
                   let uu____6908 =
                     let uu____6909 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6909 in
                   failwith uu____6908)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6914 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6919 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6924 -> false
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
             | ([],uu____6960) -> Maybe
             | (uu____6967,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6986 -> No in
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
          let uu____7093 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7093 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___114_7138  ->
                   match uu___114_7138 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7181 =
                           let uu____7200 =
                             let uu____7215 = inst_tscheme t in
                             FStar_Util.Inl uu____7215 in
                           (uu____7200, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7181
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7281,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7283);
                                     FStar_Syntax_Syntax.sigrng = uu____7284;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7285;
                                     FStar_Syntax_Syntax.sigmeta = uu____7286;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7287;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7307 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7307
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7353 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7360 -> cache t in
                       let uu____7361 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7361 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7436 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7436 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7522 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7602 = find_in_sigtab env lid in
         match uu____7602 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7701) ->
          add_sigelts env ses
      | uu____7710 ->
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
            | uu____7724 -> ()))
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
        (fun uu___115_7753  ->
           match uu___115_7753 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7771 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7806,lb::[]),uu____7808) ->
          let uu____7821 =
            let uu____7830 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7839 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7830, uu____7839) in
          FStar_Pervasives_Native.Some uu____7821
      | FStar_Syntax_Syntax.Sig_let ((uu____7852,lbs),uu____7854) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7890 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7902 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7902
                   then
                     let uu____7913 =
                       let uu____7922 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7931 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7922, uu____7931) in
                     FStar_Pervasives_Native.Some uu____7913
                   else FStar_Pervasives_Native.None)
      | uu____7953 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7987 =
          let uu____7996 =
            let uu____8001 =
              let uu____8002 =
                let uu____8005 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8005 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8002) in
            inst_tscheme uu____8001 in
          (uu____7996, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7987
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8025,uu____8026) ->
        let uu____8031 =
          let uu____8040 =
            let uu____8045 =
              let uu____8046 =
                let uu____8049 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8049 in
              (us, uu____8046) in
            inst_tscheme uu____8045 in
          (uu____8040, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8031
    | uu____8066 -> FStar_Pervasives_Native.None
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
      let mapper uu____8126 =
        match uu____8126 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8222,uvs,t,uu____8225,uu____8226,uu____8227);
                    FStar_Syntax_Syntax.sigrng = uu____8228;
                    FStar_Syntax_Syntax.sigquals = uu____8229;
                    FStar_Syntax_Syntax.sigmeta = uu____8230;
                    FStar_Syntax_Syntax.sigattrs = uu____8231;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8252 =
                   let uu____8261 = inst_tscheme (uvs, t) in
                   (uu____8261, rng) in
                 FStar_Pervasives_Native.Some uu____8252
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8281;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8283;
                    FStar_Syntax_Syntax.sigattrs = uu____8284;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8301 =
                   let uu____8302 = in_cur_mod env l in uu____8302 = Yes in
                 if uu____8301
                 then
                   let uu____8313 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8313
                    then
                      let uu____8326 =
                        let uu____8335 = inst_tscheme (uvs, t) in
                        (uu____8335, rng) in
                      FStar_Pervasives_Native.Some uu____8326
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8362 =
                      let uu____8371 = inst_tscheme (uvs, t) in
                      (uu____8371, rng) in
                    FStar_Pervasives_Native.Some uu____8362)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8392,uu____8393);
                    FStar_Syntax_Syntax.sigrng = uu____8394;
                    FStar_Syntax_Syntax.sigquals = uu____8395;
                    FStar_Syntax_Syntax.sigmeta = uu____8396;
                    FStar_Syntax_Syntax.sigattrs = uu____8397;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8436 =
                        let uu____8445 = inst_tscheme (uvs, k) in
                        (uu____8445, rng) in
                      FStar_Pervasives_Native.Some uu____8436
                  | uu____8462 ->
                      let uu____8463 =
                        let uu____8472 =
                          let uu____8477 =
                            let uu____8478 =
                              let uu____8481 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8481 in
                            (uvs, uu____8478) in
                          inst_tscheme uu____8477 in
                        (uu____8472, rng) in
                      FStar_Pervasives_Native.Some uu____8463)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8502,uu____8503);
                    FStar_Syntax_Syntax.sigrng = uu____8504;
                    FStar_Syntax_Syntax.sigquals = uu____8505;
                    FStar_Syntax_Syntax.sigmeta = uu____8506;
                    FStar_Syntax_Syntax.sigattrs = uu____8507;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8547 =
                        let uu____8556 = inst_tscheme_with (uvs, k) us in
                        (uu____8556, rng) in
                      FStar_Pervasives_Native.Some uu____8547
                  | uu____8573 ->
                      let uu____8574 =
                        let uu____8583 =
                          let uu____8588 =
                            let uu____8589 =
                              let uu____8592 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8592 in
                            (uvs, uu____8589) in
                          inst_tscheme_with uu____8588 us in
                        (uu____8583, rng) in
                      FStar_Pervasives_Native.Some uu____8574)
             | FStar_Util.Inr se ->
                 let uu____8626 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8647;
                        FStar_Syntax_Syntax.sigrng = uu____8648;
                        FStar_Syntax_Syntax.sigquals = uu____8649;
                        FStar_Syntax_Syntax.sigmeta = uu____8650;
                        FStar_Syntax_Syntax.sigattrs = uu____8651;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8666 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8626
                   (FStar_Util.map_option
                      (fun uu____8714  ->
                         match uu____8714 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8745 =
        let uu____8756 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8756 mapper in
      match uu____8745 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___131_8849 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___131_8849.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___131_8849.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8876 = lookup_qname env l in
      match uu____8876 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8915 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8965 = try_lookup_bv env bv in
      match uu____8965 with
      | FStar_Pervasives_Native.None  ->
          let uu____8980 =
            let uu____8981 =
              let uu____8986 = variable_not_found bv in (uu____8986, bvr) in
            FStar_Errors.Error uu____8981 in
          FStar_Exn.raise uu____8980
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8997 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8998 = FStar_Range.set_use_range r bvr in
          (uu____8997, uu____8998)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9017 = try_lookup_lid_aux env l in
      match uu____9017 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____9083 =
            let uu____9092 =
              let uu____9097 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____9097) in
            (uu____9092, r1) in
          FStar_Pervasives_Native.Some uu____9083
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9126 = try_lookup_lid env l in
      match uu____9126 with
      | FStar_Pervasives_Native.None  ->
          let uu____9153 =
            let uu____9154 =
              let uu____9159 = name_not_found l in
              (uu____9159, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9154 in
          FStar_Exn.raise uu____9153
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___116_9197  ->
              match uu___116_9197 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9199 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9216 = lookup_qname env lid in
      match uu____9216 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9245,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9248;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9250;
              FStar_Syntax_Syntax.sigattrs = uu____9251;_},FStar_Pervasives_Native.None
            ),uu____9252)
          ->
          let uu____9301 =
            let uu____9312 =
              let uu____9317 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9317) in
            (uu____9312, q) in
          FStar_Pervasives_Native.Some uu____9301
      | uu____9334 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9373 = lookup_qname env lid in
      match uu____9373 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9398,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9401;
              FStar_Syntax_Syntax.sigquals = uu____9402;
              FStar_Syntax_Syntax.sigmeta = uu____9403;
              FStar_Syntax_Syntax.sigattrs = uu____9404;_},FStar_Pervasives_Native.None
            ),uu____9405)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9454 ->
          let uu____9475 =
            let uu____9476 =
              let uu____9481 = name_not_found lid in
              (uu____9481, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9476 in
          FStar_Exn.raise uu____9475
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9498 = lookup_qname env lid in
      match uu____9498 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9523,uvs,t,uu____9526,uu____9527,uu____9528);
              FStar_Syntax_Syntax.sigrng = uu____9529;
              FStar_Syntax_Syntax.sigquals = uu____9530;
              FStar_Syntax_Syntax.sigmeta = uu____9531;
              FStar_Syntax_Syntax.sigattrs = uu____9532;_},FStar_Pervasives_Native.None
            ),uu____9533)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9586 ->
          let uu____9607 =
            let uu____9608 =
              let uu____9613 = name_not_found lid in
              (uu____9613, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9608 in
          FStar_Exn.raise uu____9607
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9632 = lookup_qname env lid in
      match uu____9632 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9659,uu____9660,uu____9661,uu____9662,uu____9663,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9665;
              FStar_Syntax_Syntax.sigquals = uu____9666;
              FStar_Syntax_Syntax.sigmeta = uu____9667;
              FStar_Syntax_Syntax.sigattrs = uu____9668;_},uu____9669),uu____9670)
          -> (true, dcs)
      | uu____9731 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9762 = lookup_qname env lid in
      match uu____9762 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9783,uu____9784,uu____9785,l,uu____9787,uu____9788);
              FStar_Syntax_Syntax.sigrng = uu____9789;
              FStar_Syntax_Syntax.sigquals = uu____9790;
              FStar_Syntax_Syntax.sigmeta = uu____9791;
              FStar_Syntax_Syntax.sigattrs = uu____9792;_},uu____9793),uu____9794)
          -> l
      | uu____9849 ->
          let uu____9870 =
            let uu____9871 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9871 in
          failwith uu____9870
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
        let uu____9908 = lookup_qname env lid in
        match uu____9908 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9936) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9987,lbs),uu____9989) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10017 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10017
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10049 -> FStar_Pervasives_Native.None)
        | uu____10054 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10091 = lookup_qname env ftv in
      match uu____10091 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10115) ->
          let uu____10160 = effect_signature se in
          (match uu____10160 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10181,t),r) ->
               let uu____10196 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10196)
      | uu____10197 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10226 = try_lookup_effect_lid env ftv in
      match uu____10226 with
      | FStar_Pervasives_Native.None  ->
          let uu____10229 =
            let uu____10230 =
              let uu____10235 = name_not_found ftv in
              (uu____10235, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10230 in
          FStar_Exn.raise uu____10229
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
        let uu____10255 = lookup_qname env lid0 in
        match uu____10255 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10286);
                FStar_Syntax_Syntax.sigrng = uu____10287;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10289;
                FStar_Syntax_Syntax.sigattrs = uu____10290;_},FStar_Pervasives_Native.None
              ),uu____10291)
            ->
            let lid1 =
              let uu____10345 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____10345 in
            let uu____10346 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_10350  ->
                      match uu___117_10350 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10351 -> false)) in
            if uu____10346
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10365 =
                      let uu____10366 =
                        let uu____10367 = get_range env in
                        FStar_Range.string_of_range uu____10367 in
                      let uu____10368 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10369 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10366 uu____10368 uu____10369 in
                    failwith uu____10365) in
               match (binders, univs1) with
               | ([],uu____10376) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10393,uu____10394::uu____10395::uu____10396) ->
                   let uu____10401 =
                     let uu____10402 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10403 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10402 uu____10403 in
                   failwith uu____10401
               | uu____10410 ->
                   let uu____10415 =
                     let uu____10420 =
                       let uu____10421 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10421) in
                     inst_tscheme_with uu____10420 insts in
                   (match uu____10415 with
                    | (uu____10432,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10435 =
                          let uu____10436 = FStar_Syntax_Subst.compress t1 in
                          uu____10436.FStar_Syntax_Syntax.n in
                        (match uu____10435 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10483 -> failwith "Impossible")))
        | uu____10490 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10532 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10532 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10545,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10552 = find1 l2 in
            (match uu____10552 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10559 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10559 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10563 = find1 l in
            (match uu____10563 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10579 = lookup_qname env l1 in
      match uu____10579 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10602;
              FStar_Syntax_Syntax.sigrng = uu____10603;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10605;
              FStar_Syntax_Syntax.sigattrs = uu____10606;_},uu____10607),uu____10608)
          -> q
      | uu____10659 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10695 =
          let uu____10696 =
            let uu____10697 = FStar_Util.string_of_int i in
            let uu____10698 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10697 uu____10698 in
          failwith uu____10696 in
        let uu____10699 = lookup_datacon env lid in
        match uu____10699 with
        | (uu____10704,t) ->
            let uu____10706 =
              let uu____10707 = FStar_Syntax_Subst.compress t in
              uu____10707.FStar_Syntax_Syntax.n in
            (match uu____10706 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10711) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10742 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10742
                      FStar_Pervasives_Native.fst)
             | uu____10751 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10760 = lookup_qname env l in
      match uu____10760 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10781,uu____10782,uu____10783);
              FStar_Syntax_Syntax.sigrng = uu____10784;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10786;
              FStar_Syntax_Syntax.sigattrs = uu____10787;_},uu____10788),uu____10789)
          ->
          FStar_Util.for_some
            (fun uu___118_10842  ->
               match uu___118_10842 with
               | FStar_Syntax_Syntax.Projector uu____10843 -> true
               | uu____10848 -> false) quals
      | uu____10849 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10878 = lookup_qname env lid in
      match uu____10878 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10899,uu____10900,uu____10901,uu____10902,uu____10903,uu____10904);
              FStar_Syntax_Syntax.sigrng = uu____10905;
              FStar_Syntax_Syntax.sigquals = uu____10906;
              FStar_Syntax_Syntax.sigmeta = uu____10907;
              FStar_Syntax_Syntax.sigattrs = uu____10908;_},uu____10909),uu____10910)
          -> true
      | uu____10965 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10994 = lookup_qname env lid in
      match uu____10994 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11015,uu____11016,uu____11017,uu____11018,uu____11019,uu____11020);
              FStar_Syntax_Syntax.sigrng = uu____11021;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11023;
              FStar_Syntax_Syntax.sigattrs = uu____11024;_},uu____11025),uu____11026)
          ->
          FStar_Util.for_some
            (fun uu___119_11087  ->
               match uu___119_11087 with
               | FStar_Syntax_Syntax.RecordType uu____11088 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11097 -> true
               | uu____11106 -> false) quals
      | uu____11107 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11136 = lookup_qname env lid in
      match uu____11136 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11157,uu____11158);
              FStar_Syntax_Syntax.sigrng = uu____11159;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11161;
              FStar_Syntax_Syntax.sigattrs = uu____11162;_},uu____11163),uu____11164)
          ->
          FStar_Util.for_some
            (fun uu___120_11221  ->
               match uu___120_11221 with
               | FStar_Syntax_Syntax.Action uu____11222 -> true
               | uu____11223 -> false) quals
      | uu____11224 -> false
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
      let uu____11256 =
        let uu____11257 = FStar_Syntax_Util.un_uinst head1 in
        uu____11257.FStar_Syntax_Syntax.n in
      match uu____11256 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11261 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11328 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11344) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11361 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11368 ->
                 FStar_Pervasives_Native.Some true
             | uu____11385 -> FStar_Pervasives_Native.Some false) in
      let uu____11386 =
        let uu____11389 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11389 mapper in
      match uu____11386 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11437 = lookup_qname env lid in
      match uu____11437 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11458,uu____11459,tps,uu____11461,uu____11462,uu____11463);
              FStar_Syntax_Syntax.sigrng = uu____11464;
              FStar_Syntax_Syntax.sigquals = uu____11465;
              FStar_Syntax_Syntax.sigmeta = uu____11466;
              FStar_Syntax_Syntax.sigattrs = uu____11467;_},uu____11468),uu____11469)
          -> FStar_List.length tps
      | uu____11532 ->
          let uu____11553 =
            let uu____11554 =
              let uu____11559 = name_not_found lid in
              (uu____11559, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11554 in
          FStar_Exn.raise uu____11553
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
           (fun uu____11601  ->
              match uu____11601 with
              | (d,uu____11609) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11622 = effect_decl_opt env l in
      match uu____11622 with
      | FStar_Pervasives_Native.None  ->
          let uu____11637 =
            let uu____11638 =
              let uu____11643 = name_not_found l in
              (uu____11643, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11638 in
          FStar_Exn.raise uu____11637
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
            (let uu____11709 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11762  ->
                       match uu____11762 with
                       | (m1,m2,uu____11775,uu____11776,uu____11777) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11709 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11794 =
                   let uu____11795 =
                     let uu____11800 =
                       let uu____11801 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11802 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11801
                         uu____11802 in
                     (uu____11800, (env.range)) in
                   FStar_Errors.Error uu____11795 in
                 FStar_Exn.raise uu____11794
             | FStar_Pervasives_Native.Some
                 (uu____11809,uu____11810,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11853 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11853)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11880 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11906  ->
                match uu____11906 with
                | (d,uu____11912) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11880 with
      | FStar_Pervasives_Native.None  ->
          let uu____11923 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11923
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11936 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11936 with
           | (uu____11947,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11957)::(wp,uu____11959)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11995 -> failwith "Impossible"))
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
                 let uu____12044 = get_range env in
                 let uu____12045 =
                   let uu____12048 =
                     let uu____12049 =
                       let uu____12064 =
                         let uu____12067 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12067] in
                       (null_wp, uu____12064) in
                     FStar_Syntax_Syntax.Tm_app uu____12049 in
                   FStar_Syntax_Syntax.mk uu____12048 in
                 uu____12045 FStar_Pervasives_Native.None uu____12044 in
               let uu____12073 =
                 let uu____12074 =
                   let uu____12083 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12083] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12074;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12073)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___132_12094 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___132_12094.order);
              joins = (uu___132_12094.joins)
            } in
          let uu___133_12103 = env in
          {
            solver = (uu___133_12103.solver);
            range = (uu___133_12103.range);
            curmodule = (uu___133_12103.curmodule);
            gamma = (uu___133_12103.gamma);
            gamma_cache = (uu___133_12103.gamma_cache);
            modules = (uu___133_12103.modules);
            expected_typ = (uu___133_12103.expected_typ);
            sigtab = (uu___133_12103.sigtab);
            is_pattern = (uu___133_12103.is_pattern);
            instantiate_imp = (uu___133_12103.instantiate_imp);
            effects;
            generalize = (uu___133_12103.generalize);
            letrecs = (uu___133_12103.letrecs);
            top_level = (uu___133_12103.top_level);
            check_uvars = (uu___133_12103.check_uvars);
            use_eq = (uu___133_12103.use_eq);
            is_iface = (uu___133_12103.is_iface);
            admit = (uu___133_12103.admit);
            lax = (uu___133_12103.lax);
            lax_universes = (uu___133_12103.lax_universes);
            failhard = (uu___133_12103.failhard);
            nosynth = (uu___133_12103.nosynth);
            tc_term = (uu___133_12103.tc_term);
            type_of = (uu___133_12103.type_of);
            universe_of = (uu___133_12103.universe_of);
            use_bv_sorts = (uu___133_12103.use_bv_sorts);
            qname_and_index = (uu___133_12103.qname_and_index);
            proof_ns = (uu___133_12103.proof_ns);
            synth = (uu___133_12103.synth);
            is_native_tactic = (uu___133_12103.is_native_tactic);
            identifier_info = (uu___133_12103.identifier_info)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12120 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12120 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12210 = (e1.mlift).mlift_wp t wp in
                              let uu____12211 = l1 t wp e in
                              l2 t uu____12210 uu____12211))
                | uu____12212 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12251 = inst_tscheme lift_t in
            match uu____12251 with
            | (uu____12258,lift_t1) ->
                let uu____12260 =
                  let uu____12263 =
                    let uu____12264 =
                      let uu____12279 =
                        let uu____12282 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12283 =
                          let uu____12286 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12286] in
                        uu____12282 :: uu____12283 in
                      (lift_t1, uu____12279) in
                    FStar_Syntax_Syntax.Tm_app uu____12264 in
                  FStar_Syntax_Syntax.mk uu____12263 in
                uu____12260 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12327 = inst_tscheme lift_t in
            match uu____12327 with
            | (uu____12334,lift_t1) ->
                let uu____12336 =
                  let uu____12339 =
                    let uu____12340 =
                      let uu____12355 =
                        let uu____12358 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12359 =
                          let uu____12362 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12363 =
                            let uu____12366 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12366] in
                          uu____12362 :: uu____12363 in
                        uu____12358 :: uu____12359 in
                      (lift_t1, uu____12355) in
                    FStar_Syntax_Syntax.Tm_app uu____12340 in
                  FStar_Syntax_Syntax.mk uu____12339 in
                uu____12336 FStar_Pervasives_Native.None
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
              let uu____12404 =
                let uu____12405 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12405
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12404 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12409 =
              let uu____12410 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12410 in
            let uu____12411 =
              let uu____12412 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12430 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12430) in
              FStar_Util.dflt "none" uu____12412 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12409
              uu____12411 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12456  ->
                    match uu____12456 with
                    | (e,uu____12464) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12483 =
            match uu____12483 with
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
              let uu____12521 =
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
                                    (let uu____12542 =
                                       let uu____12551 =
                                         find_edge order1 (i, k) in
                                       let uu____12554 =
                                         find_edge order1 (k, j) in
                                       (uu____12551, uu____12554) in
                                     match uu____12542 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12569 =
                                           compose_edges e1 e2 in
                                         [uu____12569]
                                     | uu____12570 -> []))))) in
              FStar_List.append order1 uu____12521 in
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
                   let uu____12599 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12601 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12601
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12599
                   then
                     let uu____12606 =
                       let uu____12607 =
                         let uu____12612 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12613 = get_range env in
                         (uu____12612, uu____12613) in
                       FStar_Errors.Error uu____12607 in
                     FStar_Exn.raise uu____12606
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
                                            let uu____12738 =
                                              let uu____12747 =
                                                find_edge order2 (i, k) in
                                              let uu____12750 =
                                                find_edge order2 (j, k) in
                                              (uu____12747, uu____12750) in
                                            match uu____12738 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12792,uu____12793)
                                                     ->
                                                     let uu____12800 =
                                                       let uu____12805 =
                                                         let uu____12806 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12806 in
                                                       let uu____12809 =
                                                         let uu____12810 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12810 in
                                                       (uu____12805,
                                                         uu____12809) in
                                                     (match uu____12800 with
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
                                            | uu____12845 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___134_12918 = env.effects in
              { decls = (uu___134_12918.decls); order = order2; joins } in
            let uu___135_12919 = env in
            {
              solver = (uu___135_12919.solver);
              range = (uu___135_12919.range);
              curmodule = (uu___135_12919.curmodule);
              gamma = (uu___135_12919.gamma);
              gamma_cache = (uu___135_12919.gamma_cache);
              modules = (uu___135_12919.modules);
              expected_typ = (uu___135_12919.expected_typ);
              sigtab = (uu___135_12919.sigtab);
              is_pattern = (uu___135_12919.is_pattern);
              instantiate_imp = (uu___135_12919.instantiate_imp);
              effects;
              generalize = (uu___135_12919.generalize);
              letrecs = (uu___135_12919.letrecs);
              top_level = (uu___135_12919.top_level);
              check_uvars = (uu___135_12919.check_uvars);
              use_eq = (uu___135_12919.use_eq);
              is_iface = (uu___135_12919.is_iface);
              admit = (uu___135_12919.admit);
              lax = (uu___135_12919.lax);
              lax_universes = (uu___135_12919.lax_universes);
              failhard = (uu___135_12919.failhard);
              nosynth = (uu___135_12919.nosynth);
              tc_term = (uu___135_12919.tc_term);
              type_of = (uu___135_12919.type_of);
              universe_of = (uu___135_12919.universe_of);
              use_bv_sorts = (uu___135_12919.use_bv_sorts);
              qname_and_index = (uu___135_12919.qname_and_index);
              proof_ns = (uu___135_12919.proof_ns);
              synth = (uu___135_12919.synth);
              is_native_tactic = (uu___135_12919.is_native_tactic);
              identifier_info = (uu___135_12919.identifier_info)
            }))
      | uu____12920 -> env
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
        | uu____12946 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12956 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12956 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12973 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12973 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12991 =
                     let uu____12992 =
                       let uu____12997 =
                         let uu____12998 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13003 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13010 =
                           let uu____13011 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13011 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12998 uu____13003 uu____13010 in
                       (uu____12997, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12992 in
                   FStar_Exn.raise uu____12991)
                else ();
                (let inst1 =
                   let uu____13016 =
                     let uu____13025 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13025 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13042  ->
                        fun uu____13043  ->
                          match (uu____13042, uu____13043) with
                          | ((x,uu____13065),(t,uu____13067)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13016 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13086 =
                     let uu___136_13087 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___136_13087.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___136_13087.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___136_13087.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___136_13087.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13086
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
          let uu____13113 = effect_decl_opt env effect_name in
          match uu____13113 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13146 =
                only_reifiable &&
                  (let uu____13148 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13148) in
              if uu____13146
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13164 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13183 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13212 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13212
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13213 =
                             let uu____13214 =
                               let uu____13219 = get_range env in
                               (message, uu____13219) in
                             FStar_Errors.Error uu____13214 in
                           FStar_Exn.raise uu____13213 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13229 =
                       let uu____13232 = get_range env in
                       let uu____13233 =
                         let uu____13236 =
                           let uu____13237 =
                             let uu____13252 =
                               let uu____13255 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13255; wp] in
                             (repr, uu____13252) in
                           FStar_Syntax_Syntax.Tm_app uu____13237 in
                         FStar_Syntax_Syntax.mk uu____13236 in
                       uu____13233 FStar_Pervasives_Native.None uu____13232 in
                     FStar_Pervasives_Native.Some uu____13229)
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
          let uu____13307 =
            let uu____13308 =
              let uu____13313 =
                let uu____13314 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13314 in
              let uu____13315 = get_range env in (uu____13313, uu____13315) in
            FStar_Errors.Error uu____13308 in
          FStar_Exn.raise uu____13307 in
        let uu____13316 = effect_repr_aux true env c u_c in
        match uu____13316 with
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
      let uu____13365 =
        let uu____13366 = FStar_Syntax_Subst.compress t in
        uu____13366.FStar_Syntax_Syntax.n in
      match uu____13365 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13369,c) ->
          is_reifiable_comp env c
      | uu____13387 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13411)::uu____13412 -> x :: rest
        | (Binding_sig_inst uu____13421)::uu____13422 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13437 = push1 x rest1 in local :: uu____13437 in
      let uu___137_13440 = env in
      let uu____13441 = push1 s env.gamma in
      {
        solver = (uu___137_13440.solver);
        range = (uu___137_13440.range);
        curmodule = (uu___137_13440.curmodule);
        gamma = uu____13441;
        gamma_cache = (uu___137_13440.gamma_cache);
        modules = (uu___137_13440.modules);
        expected_typ = (uu___137_13440.expected_typ);
        sigtab = (uu___137_13440.sigtab);
        is_pattern = (uu___137_13440.is_pattern);
        instantiate_imp = (uu___137_13440.instantiate_imp);
        effects = (uu___137_13440.effects);
        generalize = (uu___137_13440.generalize);
        letrecs = (uu___137_13440.letrecs);
        top_level = (uu___137_13440.top_level);
        check_uvars = (uu___137_13440.check_uvars);
        use_eq = (uu___137_13440.use_eq);
        is_iface = (uu___137_13440.is_iface);
        admit = (uu___137_13440.admit);
        lax = (uu___137_13440.lax);
        lax_universes = (uu___137_13440.lax_universes);
        failhard = (uu___137_13440.failhard);
        nosynth = (uu___137_13440.nosynth);
        tc_term = (uu___137_13440.tc_term);
        type_of = (uu___137_13440.type_of);
        universe_of = (uu___137_13440.universe_of);
        use_bv_sorts = (uu___137_13440.use_bv_sorts);
        qname_and_index = (uu___137_13440.qname_and_index);
        proof_ns = (uu___137_13440.proof_ns);
        synth = (uu___137_13440.synth);
        is_native_tactic = (uu___137_13440.is_native_tactic);
        identifier_info = (uu___137_13440.identifier_info)
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
      let uu___138_13478 = env in
      {
        solver = (uu___138_13478.solver);
        range = (uu___138_13478.range);
        curmodule = (uu___138_13478.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___138_13478.gamma_cache);
        modules = (uu___138_13478.modules);
        expected_typ = (uu___138_13478.expected_typ);
        sigtab = (uu___138_13478.sigtab);
        is_pattern = (uu___138_13478.is_pattern);
        instantiate_imp = (uu___138_13478.instantiate_imp);
        effects = (uu___138_13478.effects);
        generalize = (uu___138_13478.generalize);
        letrecs = (uu___138_13478.letrecs);
        top_level = (uu___138_13478.top_level);
        check_uvars = (uu___138_13478.check_uvars);
        use_eq = (uu___138_13478.use_eq);
        is_iface = (uu___138_13478.is_iface);
        admit = (uu___138_13478.admit);
        lax = (uu___138_13478.lax);
        lax_universes = (uu___138_13478.lax_universes);
        failhard = (uu___138_13478.failhard);
        nosynth = (uu___138_13478.nosynth);
        tc_term = (uu___138_13478.tc_term);
        type_of = (uu___138_13478.type_of);
        universe_of = (uu___138_13478.universe_of);
        use_bv_sorts = (uu___138_13478.use_bv_sorts);
        qname_and_index = (uu___138_13478.qname_and_index);
        proof_ns = (uu___138_13478.proof_ns);
        synth = (uu___138_13478.synth);
        is_native_tactic = (uu___138_13478.is_native_tactic);
        identifier_info = (uu___138_13478.identifier_info)
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
            (let uu___139_13512 = env in
             {
               solver = (uu___139_13512.solver);
               range = (uu___139_13512.range);
               curmodule = (uu___139_13512.curmodule);
               gamma = rest;
               gamma_cache = (uu___139_13512.gamma_cache);
               modules = (uu___139_13512.modules);
               expected_typ = (uu___139_13512.expected_typ);
               sigtab = (uu___139_13512.sigtab);
               is_pattern = (uu___139_13512.is_pattern);
               instantiate_imp = (uu___139_13512.instantiate_imp);
               effects = (uu___139_13512.effects);
               generalize = (uu___139_13512.generalize);
               letrecs = (uu___139_13512.letrecs);
               top_level = (uu___139_13512.top_level);
               check_uvars = (uu___139_13512.check_uvars);
               use_eq = (uu___139_13512.use_eq);
               is_iface = (uu___139_13512.is_iface);
               admit = (uu___139_13512.admit);
               lax = (uu___139_13512.lax);
               lax_universes = (uu___139_13512.lax_universes);
               failhard = (uu___139_13512.failhard);
               nosynth = (uu___139_13512.nosynth);
               tc_term = (uu___139_13512.tc_term);
               type_of = (uu___139_13512.type_of);
               universe_of = (uu___139_13512.universe_of);
               use_bv_sorts = (uu___139_13512.use_bv_sorts);
               qname_and_index = (uu___139_13512.qname_and_index);
               proof_ns = (uu___139_13512.proof_ns);
               synth = (uu___139_13512.synth);
               is_native_tactic = (uu___139_13512.is_native_tactic);
               identifier_info = (uu___139_13512.identifier_info)
             }))
    | uu____13513 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13537  ->
             match uu____13537 with | (x,uu____13543) -> push_bv env1 x) env
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
            let uu___140_13573 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___140_13573.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___140_13573.FStar_Syntax_Syntax.index);
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
      (let uu___141_13608 = env in
       {
         solver = (uu___141_13608.solver);
         range = (uu___141_13608.range);
         curmodule = (uu___141_13608.curmodule);
         gamma = [];
         gamma_cache = (uu___141_13608.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___141_13608.sigtab);
         is_pattern = (uu___141_13608.is_pattern);
         instantiate_imp = (uu___141_13608.instantiate_imp);
         effects = (uu___141_13608.effects);
         generalize = (uu___141_13608.generalize);
         letrecs = (uu___141_13608.letrecs);
         top_level = (uu___141_13608.top_level);
         check_uvars = (uu___141_13608.check_uvars);
         use_eq = (uu___141_13608.use_eq);
         is_iface = (uu___141_13608.is_iface);
         admit = (uu___141_13608.admit);
         lax = (uu___141_13608.lax);
         lax_universes = (uu___141_13608.lax_universes);
         failhard = (uu___141_13608.failhard);
         nosynth = (uu___141_13608.nosynth);
         tc_term = (uu___141_13608.tc_term);
         type_of = (uu___141_13608.type_of);
         universe_of = (uu___141_13608.universe_of);
         use_bv_sorts = (uu___141_13608.use_bv_sorts);
         qname_and_index = (uu___141_13608.qname_and_index);
         proof_ns = (uu___141_13608.proof_ns);
         synth = (uu___141_13608.synth);
         is_native_tactic = (uu___141_13608.is_native_tactic);
         identifier_info = (uu___141_13608.identifier_info)
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
        let uu____13645 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13645 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13673 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13673)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___142_13688 = env in
      {
        solver = (uu___142_13688.solver);
        range = (uu___142_13688.range);
        curmodule = (uu___142_13688.curmodule);
        gamma = (uu___142_13688.gamma);
        gamma_cache = (uu___142_13688.gamma_cache);
        modules = (uu___142_13688.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___142_13688.sigtab);
        is_pattern = (uu___142_13688.is_pattern);
        instantiate_imp = (uu___142_13688.instantiate_imp);
        effects = (uu___142_13688.effects);
        generalize = (uu___142_13688.generalize);
        letrecs = (uu___142_13688.letrecs);
        top_level = (uu___142_13688.top_level);
        check_uvars = (uu___142_13688.check_uvars);
        use_eq = false;
        is_iface = (uu___142_13688.is_iface);
        admit = (uu___142_13688.admit);
        lax = (uu___142_13688.lax);
        lax_universes = (uu___142_13688.lax_universes);
        failhard = (uu___142_13688.failhard);
        nosynth = (uu___142_13688.nosynth);
        tc_term = (uu___142_13688.tc_term);
        type_of = (uu___142_13688.type_of);
        universe_of = (uu___142_13688.universe_of);
        use_bv_sorts = (uu___142_13688.use_bv_sorts);
        qname_and_index = (uu___142_13688.qname_and_index);
        proof_ns = (uu___142_13688.proof_ns);
        synth = (uu___142_13688.synth);
        is_native_tactic = (uu___142_13688.is_native_tactic);
        identifier_info = (uu___142_13688.identifier_info)
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
    let uu____13714 = expected_typ env_ in
    ((let uu___143_13720 = env_ in
      {
        solver = (uu___143_13720.solver);
        range = (uu___143_13720.range);
        curmodule = (uu___143_13720.curmodule);
        gamma = (uu___143_13720.gamma);
        gamma_cache = (uu___143_13720.gamma_cache);
        modules = (uu___143_13720.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___143_13720.sigtab);
        is_pattern = (uu___143_13720.is_pattern);
        instantiate_imp = (uu___143_13720.instantiate_imp);
        effects = (uu___143_13720.effects);
        generalize = (uu___143_13720.generalize);
        letrecs = (uu___143_13720.letrecs);
        top_level = (uu___143_13720.top_level);
        check_uvars = (uu___143_13720.check_uvars);
        use_eq = false;
        is_iface = (uu___143_13720.is_iface);
        admit = (uu___143_13720.admit);
        lax = (uu___143_13720.lax);
        lax_universes = (uu___143_13720.lax_universes);
        failhard = (uu___143_13720.failhard);
        nosynth = (uu___143_13720.nosynth);
        tc_term = (uu___143_13720.tc_term);
        type_of = (uu___143_13720.type_of);
        universe_of = (uu___143_13720.universe_of);
        use_bv_sorts = (uu___143_13720.use_bv_sorts);
        qname_and_index = (uu___143_13720.qname_and_index);
        proof_ns = (uu___143_13720.proof_ns);
        synth = (uu___143_13720.synth);
        is_native_tactic = (uu___143_13720.is_native_tactic);
        identifier_info = (uu___143_13720.identifier_info)
      }), uu____13714)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13735 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___121_13745  ->
                    match uu___121_13745 with
                    | Binding_sig (uu____13748,se) -> [se]
                    | uu____13754 -> [])) in
          FStar_All.pipe_right uu____13735 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___144_13761 = env in
       {
         solver = (uu___144_13761.solver);
         range = (uu___144_13761.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___144_13761.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___144_13761.expected_typ);
         sigtab = (uu___144_13761.sigtab);
         is_pattern = (uu___144_13761.is_pattern);
         instantiate_imp = (uu___144_13761.instantiate_imp);
         effects = (uu___144_13761.effects);
         generalize = (uu___144_13761.generalize);
         letrecs = (uu___144_13761.letrecs);
         top_level = (uu___144_13761.top_level);
         check_uvars = (uu___144_13761.check_uvars);
         use_eq = (uu___144_13761.use_eq);
         is_iface = (uu___144_13761.is_iface);
         admit = (uu___144_13761.admit);
         lax = (uu___144_13761.lax);
         lax_universes = (uu___144_13761.lax_universes);
         failhard = (uu___144_13761.failhard);
         nosynth = (uu___144_13761.nosynth);
         tc_term = (uu___144_13761.tc_term);
         type_of = (uu___144_13761.type_of);
         universe_of = (uu___144_13761.universe_of);
         use_bv_sorts = (uu___144_13761.use_bv_sorts);
         qname_and_index = (uu___144_13761.qname_and_index);
         proof_ns = (uu___144_13761.proof_ns);
         synth = (uu___144_13761.synth);
         is_native_tactic = (uu___144_13761.is_native_tactic);
         identifier_info = (uu___144_13761.identifier_info)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13843)::tl1 -> aux out tl1
      | (Binding_lid (uu____13847,(uu____13848,t)))::tl1 ->
          let uu____13863 =
            let uu____13870 = FStar_Syntax_Free.uvars t in
            ext out uu____13870 in
          aux uu____13863 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13877;
            FStar_Syntax_Syntax.index = uu____13878;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13885 =
            let uu____13892 = FStar_Syntax_Free.uvars t in
            ext out uu____13892 in
          aux uu____13885 tl1
      | (Binding_sig uu____13899)::uu____13900 -> out
      | (Binding_sig_inst uu____13909)::uu____13910 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13966)::tl1 -> aux out tl1
      | (Binding_univ uu____13978)::tl1 -> aux out tl1
      | (Binding_lid (uu____13982,(uu____13983,t)))::tl1 ->
          let uu____13998 =
            let uu____14001 = FStar_Syntax_Free.univs t in
            ext out uu____14001 in
          aux uu____13998 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14004;
            FStar_Syntax_Syntax.index = uu____14005;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14012 =
            let uu____14015 = FStar_Syntax_Free.univs t in
            ext out uu____14015 in
          aux uu____14012 tl1
      | (Binding_sig uu____14018)::uu____14019 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14073)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14089 = FStar_Util.fifo_set_add uname out in
          aux uu____14089 tl1
      | (Binding_lid (uu____14092,(uu____14093,t)))::tl1 ->
          let uu____14108 =
            let uu____14111 = FStar_Syntax_Free.univnames t in
            ext out uu____14111 in
          aux uu____14108 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14114;
            FStar_Syntax_Syntax.index = uu____14115;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14122 =
            let uu____14125 = FStar_Syntax_Free.univnames t in
            ext out uu____14125 in
          aux uu____14122 tl1
      | (Binding_sig uu____14128)::uu____14129 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___122_14154  ->
            match uu___122_14154 with
            | Binding_var x -> [x]
            | Binding_lid uu____14158 -> []
            | Binding_sig uu____14163 -> []
            | Binding_univ uu____14170 -> []
            | Binding_sig_inst uu____14171 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14188 =
      let uu____14191 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14191
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14188 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14216 =
      let uu____14217 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___123_14227  ->
                match uu___123_14227 with
                | Binding_var x ->
                    let uu____14229 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14229
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14232) ->
                    let uu____14233 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14233
                | Binding_sig (ls,uu____14235) ->
                    let uu____14240 =
                      let uu____14241 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14241
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14240
                | Binding_sig_inst (ls,uu____14251,uu____14252) ->
                    let uu____14257 =
                      let uu____14258 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14258
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14257)) in
      FStar_All.pipe_right uu____14217 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14216 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14277 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14277
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14305  ->
                 fun uu____14306  ->
                   match (uu____14305, uu____14306) with
                   | ((b1,uu____14324),(b2,uu____14326)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___124_14373  ->
    match uu___124_14373 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14374 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___125_14393  ->
             match uu___125_14393 with
             | Binding_sig (lids,uu____14399) -> FStar_List.append lids keys
             | uu____14404 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14410  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14446) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14465,uu____14466) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____14503 = list_prefix p path1 in
            if uu____14503 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14517 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14517
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___145_14547 = e in
            {
              solver = (uu___145_14547.solver);
              range = (uu___145_14547.range);
              curmodule = (uu___145_14547.curmodule);
              gamma = (uu___145_14547.gamma);
              gamma_cache = (uu___145_14547.gamma_cache);
              modules = (uu___145_14547.modules);
              expected_typ = (uu___145_14547.expected_typ);
              sigtab = (uu___145_14547.sigtab);
              is_pattern = (uu___145_14547.is_pattern);
              instantiate_imp = (uu___145_14547.instantiate_imp);
              effects = (uu___145_14547.effects);
              generalize = (uu___145_14547.generalize);
              letrecs = (uu___145_14547.letrecs);
              top_level = (uu___145_14547.top_level);
              check_uvars = (uu___145_14547.check_uvars);
              use_eq = (uu___145_14547.use_eq);
              is_iface = (uu___145_14547.is_iface);
              admit = (uu___145_14547.admit);
              lax = (uu___145_14547.lax);
              lax_universes = (uu___145_14547.lax_universes);
              failhard = (uu___145_14547.failhard);
              nosynth = (uu___145_14547.nosynth);
              tc_term = (uu___145_14547.tc_term);
              type_of = (uu___145_14547.type_of);
              universe_of = (uu___145_14547.universe_of);
              use_bv_sorts = (uu___145_14547.use_bv_sorts);
              qname_and_index = (uu___145_14547.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___145_14547.synth);
              is_native_tactic = (uu___145_14547.is_native_tactic);
              identifier_info = (uu___145_14547.identifier_info)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___146_14574 = e in
    {
      solver = (uu___146_14574.solver);
      range = (uu___146_14574.range);
      curmodule = (uu___146_14574.curmodule);
      gamma = (uu___146_14574.gamma);
      gamma_cache = (uu___146_14574.gamma_cache);
      modules = (uu___146_14574.modules);
      expected_typ = (uu___146_14574.expected_typ);
      sigtab = (uu___146_14574.sigtab);
      is_pattern = (uu___146_14574.is_pattern);
      instantiate_imp = (uu___146_14574.instantiate_imp);
      effects = (uu___146_14574.effects);
      generalize = (uu___146_14574.generalize);
      letrecs = (uu___146_14574.letrecs);
      top_level = (uu___146_14574.top_level);
      check_uvars = (uu___146_14574.check_uvars);
      use_eq = (uu___146_14574.use_eq);
      is_iface = (uu___146_14574.is_iface);
      admit = (uu___146_14574.admit);
      lax = (uu___146_14574.lax);
      lax_universes = (uu___146_14574.lax_universes);
      failhard = (uu___146_14574.failhard);
      nosynth = (uu___146_14574.nosynth);
      tc_term = (uu___146_14574.tc_term);
      type_of = (uu___146_14574.type_of);
      universe_of = (uu___146_14574.universe_of);
      use_bv_sorts = (uu___146_14574.use_bv_sorts);
      qname_and_index = (uu___146_14574.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___146_14574.synth);
      is_native_tactic = (uu___146_14574.is_native_tactic);
      identifier_info = (uu___146_14574.identifier_info)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____14589::rest ->
        let uu___147_14593 = e in
        {
          solver = (uu___147_14593.solver);
          range = (uu___147_14593.range);
          curmodule = (uu___147_14593.curmodule);
          gamma = (uu___147_14593.gamma);
          gamma_cache = (uu___147_14593.gamma_cache);
          modules = (uu___147_14593.modules);
          expected_typ = (uu___147_14593.expected_typ);
          sigtab = (uu___147_14593.sigtab);
          is_pattern = (uu___147_14593.is_pattern);
          instantiate_imp = (uu___147_14593.instantiate_imp);
          effects = (uu___147_14593.effects);
          generalize = (uu___147_14593.generalize);
          letrecs = (uu___147_14593.letrecs);
          top_level = (uu___147_14593.top_level);
          check_uvars = (uu___147_14593.check_uvars);
          use_eq = (uu___147_14593.use_eq);
          is_iface = (uu___147_14593.is_iface);
          admit = (uu___147_14593.admit);
          lax = (uu___147_14593.lax);
          lax_universes = (uu___147_14593.lax_universes);
          failhard = (uu___147_14593.failhard);
          nosynth = (uu___147_14593.nosynth);
          tc_term = (uu___147_14593.tc_term);
          type_of = (uu___147_14593.type_of);
          universe_of = (uu___147_14593.universe_of);
          use_bv_sorts = (uu___147_14593.use_bv_sorts);
          qname_and_index = (uu___147_14593.qname_and_index);
          proof_ns = rest;
          synth = (uu___147_14593.synth);
          is_native_tactic = (uu___147_14593.is_native_tactic);
          identifier_info = (uu___147_14593.identifier_info)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___148_14606 = e in
      {
        solver = (uu___148_14606.solver);
        range = (uu___148_14606.range);
        curmodule = (uu___148_14606.curmodule);
        gamma = (uu___148_14606.gamma);
        gamma_cache = (uu___148_14606.gamma_cache);
        modules = (uu___148_14606.modules);
        expected_typ = (uu___148_14606.expected_typ);
        sigtab = (uu___148_14606.sigtab);
        is_pattern = (uu___148_14606.is_pattern);
        instantiate_imp = (uu___148_14606.instantiate_imp);
        effects = (uu___148_14606.effects);
        generalize = (uu___148_14606.generalize);
        letrecs = (uu___148_14606.letrecs);
        top_level = (uu___148_14606.top_level);
        check_uvars = (uu___148_14606.check_uvars);
        use_eq = (uu___148_14606.use_eq);
        is_iface = (uu___148_14606.is_iface);
        admit = (uu___148_14606.admit);
        lax = (uu___148_14606.lax);
        lax_universes = (uu___148_14606.lax_universes);
        failhard = (uu___148_14606.failhard);
        nosynth = (uu___148_14606.nosynth);
        tc_term = (uu___148_14606.tc_term);
        type_of = (uu___148_14606.type_of);
        universe_of = (uu___148_14606.universe_of);
        use_bv_sorts = (uu___148_14606.use_bv_sorts);
        qname_and_index = (uu___148_14606.qname_and_index);
        proof_ns = ns;
        synth = (uu___148_14606.synth);
        is_native_tactic = (uu___148_14606.is_native_tactic);
        identifier_info = (uu___148_14606.identifier_info)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14635 =
        FStar_List.map
          (fun fpns  ->
             let uu____14657 =
               let uu____14658 =
                 let uu____14659 =
                   FStar_List.map
                     (fun uu____14671  ->
                        match uu____14671 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14659 in
               Prims.strcat uu____14658 "]" in
             Prims.strcat "[" uu____14657) pns in
      FStar_String.concat ";" uu____14635 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14687  -> ());
    push = (fun uu____14689  -> ());
    pop = (fun uu____14691  -> ());
    encode_modul = (fun uu____14694  -> fun uu____14695  -> ());
    encode_sig = (fun uu____14698  -> fun uu____14699  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14705 =
             let uu____14712 = FStar_Options.peek () in (e, g, uu____14712) in
           [uu____14705]);
    solve = (fun uu____14728  -> fun uu____14729  -> fun uu____14730  -> ());
    is_trivial = (fun uu____14737  -> fun uu____14738  -> false);
    finish = (fun uu____14740  -> ());
    refresh = (fun uu____14742  -> ())
  }