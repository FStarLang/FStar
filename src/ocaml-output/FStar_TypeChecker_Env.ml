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
  FStar_Pervasives_Native.tuple3
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
  | UnfoldTac
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
      FStar_Pervasives_Native.option;}
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
  mlift: mlift;}
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
      FStar_Pervasives_Native.tuple5 Prims.list;}
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
type name_prefix = Prims.string Prims.list
type flat_proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
type proof_namespace = flat_proof_namespace Prims.list
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
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
  refresh: Prims.unit -> Prims.unit;}
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
      FStar_Pervasives_Native.tuple6 Prims.list;}
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;_} -> __fname__nosynth
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
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
    Prims.list
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____4631) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4632,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4633,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4634 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4643 . Prims.unit -> 'Auu____4643 FStar_Util.smap =
  fun uu____4649  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4654 . Prims.unit -> 'Auu____4654 FStar_Util.smap =
  fun uu____4660  -> FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
         FStar_Pervasives_Native.tuple3)
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____4709 = new_gamma_cache () in
          let uu____4712 = new_sigtab () in
          let uu____4715 =
            let uu____4716 = FStar_Options.using_facts_from () in
            match uu____4716 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____4726 =
                  let uu____4735 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____4735 [([], false)] in
                [uu____4726]
            | FStar_Pervasives_Native.None  -> [[]] in
          let uu____4808 =
            FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____4709;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____4712;
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
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = FStar_Pervasives_Native.None;
            proof_ns = uu____4715;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____4842  -> false);
            identifier_info = uu____4808
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
  fun uu____4913  ->
    let uu____4914 = FStar_ST.op_Bang query_indices in
    match uu____4914 with
    | [] -> failwith "Empty query indices!"
    | uu____4971 ->
        let uu____4980 =
          let uu____4989 =
            let uu____4996 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____4996 in
          let uu____5053 = FStar_ST.op_Bang query_indices in uu____4989 ::
            uu____5053 in
        FStar_ST.op_Colon_Equals query_indices uu____4980
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5155  ->
    let uu____5156 = FStar_ST.op_Bang query_indices in
    match uu____5156 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5284  ->
    match uu____5284 with
    | (l,n1) ->
        let uu____5291 = FStar_ST.op_Bang query_indices in
        (match uu____5291 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5416 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5434  ->
    let uu____5435 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5435
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____5495  ->
    let uu____5496 = FStar_ST.op_Bang query_indices in
    match uu____5496 with
    | hd1::uu____5548::tl1 ->
        FStar_ST.op_Colon_Equals query_indices (hd1 :: tl1)
    | uu____5630 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5657 =
       let uu____5660 = FStar_ST.op_Bang stack in env :: uu____5660 in
     FStar_ST.op_Colon_Equals stack uu____5657);
    (let uu___124_5699 = env in
     let uu____5700 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5703 = FStar_Util.smap_copy (sigtab env) in
     let uu____5706 =
       let uu____5709 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5709 in
     {
       solver = (uu___124_5699.solver);
       range = (uu___124_5699.range);
       curmodule = (uu___124_5699.curmodule);
       gamma = (uu___124_5699.gamma);
       gamma_cache = uu____5700;
       modules = (uu___124_5699.modules);
       expected_typ = (uu___124_5699.expected_typ);
       sigtab = uu____5703;
       is_pattern = (uu___124_5699.is_pattern);
       instantiate_imp = (uu___124_5699.instantiate_imp);
       effects = (uu___124_5699.effects);
       generalize = (uu___124_5699.generalize);
       letrecs = (uu___124_5699.letrecs);
       top_level = (uu___124_5699.top_level);
       check_uvars = (uu___124_5699.check_uvars);
       use_eq = (uu___124_5699.use_eq);
       is_iface = (uu___124_5699.is_iface);
       admit = (uu___124_5699.admit);
       lax = (uu___124_5699.lax);
       lax_universes = (uu___124_5699.lax_universes);
       failhard = (uu___124_5699.failhard);
       nosynth = (uu___124_5699.nosynth);
       type_of = (uu___124_5699.type_of);
       universe_of = (uu___124_5699.universe_of);
       use_bv_sorts = (uu___124_5699.use_bv_sorts);
       qname_and_index = (uu___124_5699.qname_and_index);
       proof_ns = (uu___124_5699.proof_ns);
       synth = (uu___124_5699.synth);
       is_native_tactic = (uu___124_5699.is_native_tactic);
       identifier_info = uu____5706
     })
let pop_stack: Prims.unit -> env =
  fun uu____5737  ->
    let uu____5738 = FStar_ST.op_Bang stack in
    match uu____5738 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____5782 -> failwith "Impossible: Too many pops"
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
    (let uu____5822 = pop_stack () in ());
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
        let uu____5850 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____5876  ->
                  match uu____5876 with
                  | (m,uu____5882) -> FStar_Ident.lid_equals l m)) in
        (match uu____5850 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___125_5889 = env in
               {
                 solver = (uu___125_5889.solver);
                 range = (uu___125_5889.range);
                 curmodule = (uu___125_5889.curmodule);
                 gamma = (uu___125_5889.gamma);
                 gamma_cache = (uu___125_5889.gamma_cache);
                 modules = (uu___125_5889.modules);
                 expected_typ = (uu___125_5889.expected_typ);
                 sigtab = (uu___125_5889.sigtab);
                 is_pattern = (uu___125_5889.is_pattern);
                 instantiate_imp = (uu___125_5889.instantiate_imp);
                 effects = (uu___125_5889.effects);
                 generalize = (uu___125_5889.generalize);
                 letrecs = (uu___125_5889.letrecs);
                 top_level = (uu___125_5889.top_level);
                 check_uvars = (uu___125_5889.check_uvars);
                 use_eq = (uu___125_5889.use_eq);
                 is_iface = (uu___125_5889.is_iface);
                 admit = (uu___125_5889.admit);
                 lax = (uu___125_5889.lax);
                 lax_universes = (uu___125_5889.lax_universes);
                 failhard = (uu___125_5889.failhard);
                 nosynth = (uu___125_5889.nosynth);
                 type_of = (uu___125_5889.type_of);
                 universe_of = (uu___125_5889.universe_of);
                 use_bv_sorts = (uu___125_5889.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___125_5889.proof_ns);
                 synth = (uu___125_5889.synth);
                 is_native_tactic = (uu___125_5889.is_native_tactic);
                 identifier_info = (uu___125_5889.identifier_info)
               }))
         | FStar_Pervasives_Native.Some (uu____5894,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___126_5902 = env in
               {
                 solver = (uu___126_5902.solver);
                 range = (uu___126_5902.range);
                 curmodule = (uu___126_5902.curmodule);
                 gamma = (uu___126_5902.gamma);
                 gamma_cache = (uu___126_5902.gamma_cache);
                 modules = (uu___126_5902.modules);
                 expected_typ = (uu___126_5902.expected_typ);
                 sigtab = (uu___126_5902.sigtab);
                 is_pattern = (uu___126_5902.is_pattern);
                 instantiate_imp = (uu___126_5902.instantiate_imp);
                 effects = (uu___126_5902.effects);
                 generalize = (uu___126_5902.generalize);
                 letrecs = (uu___126_5902.letrecs);
                 top_level = (uu___126_5902.top_level);
                 check_uvars = (uu___126_5902.check_uvars);
                 use_eq = (uu___126_5902.use_eq);
                 is_iface = (uu___126_5902.is_iface);
                 admit = (uu___126_5902.admit);
                 lax = (uu___126_5902.lax);
                 lax_universes = (uu___126_5902.lax_universes);
                 failhard = (uu___126_5902.failhard);
                 nosynth = (uu___126_5902.nosynth);
                 type_of = (uu___126_5902.type_of);
                 universe_of = (uu___126_5902.universe_of);
                 use_bv_sorts = (uu___126_5902.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___126_5902.proof_ns);
                 synth = (uu___126_5902.synth);
                 is_native_tactic = (uu___126_5902.is_native_tactic);
                 identifier_info = (uu___126_5902.identifier_info)
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
        (let uu___127_5924 = e in
         {
           solver = (uu___127_5924.solver);
           range = r;
           curmodule = (uu___127_5924.curmodule);
           gamma = (uu___127_5924.gamma);
           gamma_cache = (uu___127_5924.gamma_cache);
           modules = (uu___127_5924.modules);
           expected_typ = (uu___127_5924.expected_typ);
           sigtab = (uu___127_5924.sigtab);
           is_pattern = (uu___127_5924.is_pattern);
           instantiate_imp = (uu___127_5924.instantiate_imp);
           effects = (uu___127_5924.effects);
           generalize = (uu___127_5924.generalize);
           letrecs = (uu___127_5924.letrecs);
           top_level = (uu___127_5924.top_level);
           check_uvars = (uu___127_5924.check_uvars);
           use_eq = (uu___127_5924.use_eq);
           is_iface = (uu___127_5924.is_iface);
           admit = (uu___127_5924.admit);
           lax = (uu___127_5924.lax);
           lax_universes = (uu___127_5924.lax_universes);
           failhard = (uu___127_5924.failhard);
           nosynth = (uu___127_5924.nosynth);
           type_of = (uu___127_5924.type_of);
           universe_of = (uu___127_5924.universe_of);
           use_bv_sorts = (uu___127_5924.use_bv_sorts);
           qname_and_index = (uu___127_5924.qname_and_index);
           proof_ns = (uu___127_5924.proof_ns);
           synth = (uu___127_5924.synth);
           is_native_tactic = (uu___127_5924.is_native_tactic);
           identifier_info = (uu___127_5924.identifier_info)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____5937 =
        let uu____5938 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____5938 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5937
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____5971 =
          let uu____5972 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____5972 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5971
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6005 =
          let uu____6006 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6006 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6005
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6040 =
        let uu____6041 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6041 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6040
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___128_6080 = env in
      {
        solver = (uu___128_6080.solver);
        range = (uu___128_6080.range);
        curmodule = lid;
        gamma = (uu___128_6080.gamma);
        gamma_cache = (uu___128_6080.gamma_cache);
        modules = (uu___128_6080.modules);
        expected_typ = (uu___128_6080.expected_typ);
        sigtab = (uu___128_6080.sigtab);
        is_pattern = (uu___128_6080.is_pattern);
        instantiate_imp = (uu___128_6080.instantiate_imp);
        effects = (uu___128_6080.effects);
        generalize = (uu___128_6080.generalize);
        letrecs = (uu___128_6080.letrecs);
        top_level = (uu___128_6080.top_level);
        check_uvars = (uu___128_6080.check_uvars);
        use_eq = (uu___128_6080.use_eq);
        is_iface = (uu___128_6080.is_iface);
        admit = (uu___128_6080.admit);
        lax = (uu___128_6080.lax);
        lax_universes = (uu___128_6080.lax_universes);
        failhard = (uu___128_6080.failhard);
        nosynth = (uu___128_6080.nosynth);
        type_of = (uu___128_6080.type_of);
        universe_of = (uu___128_6080.universe_of);
        use_bv_sorts = (uu___128_6080.use_bv_sorts);
        qname_and_index = (uu___128_6080.qname_and_index);
        proof_ns = (uu___128_6080.proof_ns);
        synth = (uu___128_6080.synth);
        is_native_tactic = (uu___128_6080.is_native_tactic);
        identifier_info = (uu___128_6080.identifier_info)
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
    let uu____6111 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6111
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6115  ->
    let uu____6116 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6116
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
      | ((formals,t),uu____6156) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6180 = FStar_Syntax_Subst.subst vs t in (us, uu____6180)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___111_6194  ->
    match uu___111_6194 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6218  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6233 = inst_tscheme t in
      match uu____6233 with
      | (us,t1) ->
          let uu____6244 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6244)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6260  ->
          match uu____6260 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6275 =
                         let uu____6276 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6277 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6278 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6279 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6276 uu____6277 uu____6278 uu____6279 in
                       failwith uu____6275)
                    else ();
                    (let uu____6281 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6281))
               | uu____6288 ->
                   let uu____6289 =
                     let uu____6290 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6290 in
                   failwith uu____6289)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6295 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6300 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6305 -> false
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
             | ([],uu____6341) -> Maybe
             | (uu____6348,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6367 -> No in
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
          let uu____6474 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6474 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___112_6519  ->
                   match uu___112_6519 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____6562 =
                           let uu____6581 =
                             let uu____6596 = inst_tscheme t in
                             FStar_Util.Inl uu____6596 in
                           (uu____6581, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____6562
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6662,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6664);
                                     FStar_Syntax_Syntax.sigrng = uu____6665;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6666;
                                     FStar_Syntax_Syntax.sigmeta = uu____6667;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6668;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6688 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6688
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____6734 ->
                             FStar_Pervasives_Native.Some t
                         | uu____6741 -> cache t in
                       let uu____6742 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6742 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____6817 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6817 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____6903 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____6983 = find_in_sigtab env lid in
         match uu____6983 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7082) ->
          add_sigelts env ses
      | uu____7091 ->
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
            | uu____7105 -> ()))
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
        (fun uu___113_7134  ->
           match uu___113_7134 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7152 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7187,lb::[]),uu____7189) ->
          let uu____7202 =
            let uu____7211 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7220 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7211, uu____7220) in
          FStar_Pervasives_Native.Some uu____7202
      | FStar_Syntax_Syntax.Sig_let ((uu____7233,lbs),uu____7235) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7271 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7283 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7283
                   then
                     let uu____7294 =
                       let uu____7303 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7312 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7303, uu____7312) in
                     FStar_Pervasives_Native.Some uu____7294
                   else FStar_Pervasives_Native.None)
      | uu____7334 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7368 =
          let uu____7377 =
            let uu____7382 =
              let uu____7383 =
                let uu____7386 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7386 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7383) in
            inst_tscheme uu____7382 in
          (uu____7377, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7368
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7406,uu____7407) ->
        let uu____7412 =
          let uu____7421 =
            let uu____7426 =
              let uu____7427 =
                let uu____7430 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7430 in
              (us, uu____7427) in
            inst_tscheme uu____7426 in
          (uu____7421, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7412
    | uu____7447 -> FStar_Pervasives_Native.None
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
      let mapper uu____7507 =
        match uu____7507 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____7603,uvs,t,uu____7606,uu____7607,uu____7608);
                    FStar_Syntax_Syntax.sigrng = uu____7609;
                    FStar_Syntax_Syntax.sigquals = uu____7610;
                    FStar_Syntax_Syntax.sigmeta = uu____7611;
                    FStar_Syntax_Syntax.sigattrs = uu____7612;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7633 =
                   let uu____7642 = inst_tscheme (uvs, t) in
                   (uu____7642, rng) in
                 FStar_Pervasives_Native.Some uu____7633
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7662;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7664;
                    FStar_Syntax_Syntax.sigattrs = uu____7665;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7682 =
                   let uu____7683 = in_cur_mod env l in uu____7683 = Yes in
                 if uu____7682
                 then
                   let uu____7694 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7694
                    then
                      let uu____7707 =
                        let uu____7716 = inst_tscheme (uvs, t) in
                        (uu____7716, rng) in
                      FStar_Pervasives_Native.Some uu____7707
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____7743 =
                      let uu____7752 = inst_tscheme (uvs, t) in
                      (uu____7752, rng) in
                    FStar_Pervasives_Native.Some uu____7743)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7773,uu____7774);
                    FStar_Syntax_Syntax.sigrng = uu____7775;
                    FStar_Syntax_Syntax.sigquals = uu____7776;
                    FStar_Syntax_Syntax.sigmeta = uu____7777;
                    FStar_Syntax_Syntax.sigattrs = uu____7778;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____7817 =
                        let uu____7826 = inst_tscheme (uvs, k) in
                        (uu____7826, rng) in
                      FStar_Pervasives_Native.Some uu____7817
                  | uu____7843 ->
                      let uu____7844 =
                        let uu____7853 =
                          let uu____7858 =
                            let uu____7859 =
                              let uu____7862 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7862 in
                            (uvs, uu____7859) in
                          inst_tscheme uu____7858 in
                        (uu____7853, rng) in
                      FStar_Pervasives_Native.Some uu____7844)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7883,uu____7884);
                    FStar_Syntax_Syntax.sigrng = uu____7885;
                    FStar_Syntax_Syntax.sigquals = uu____7886;
                    FStar_Syntax_Syntax.sigmeta = uu____7887;
                    FStar_Syntax_Syntax.sigattrs = uu____7888;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____7928 =
                        let uu____7937 = inst_tscheme_with (uvs, k) us in
                        (uu____7937, rng) in
                      FStar_Pervasives_Native.Some uu____7928
                  | uu____7954 ->
                      let uu____7955 =
                        let uu____7964 =
                          let uu____7969 =
                            let uu____7970 =
                              let uu____7973 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7973 in
                            (uvs, uu____7970) in
                          inst_tscheme_with uu____7969 us in
                        (uu____7964, rng) in
                      FStar_Pervasives_Native.Some uu____7955)
             | FStar_Util.Inr se ->
                 let uu____8007 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8028;
                        FStar_Syntax_Syntax.sigrng = uu____8029;
                        FStar_Syntax_Syntax.sigquals = uu____8030;
                        FStar_Syntax_Syntax.sigmeta = uu____8031;
                        FStar_Syntax_Syntax.sigattrs = uu____8032;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8047 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8007
                   (FStar_Util.map_option
                      (fun uu____8095  ->
                         match uu____8095 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8126 =
        let uu____8137 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8137 mapper in
      match uu____8126 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___129_8230 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___129_8230.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___129_8230.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8257 = lookup_qname env l in
      match uu____8257 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8296 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8346 = try_lookup_bv env bv in
      match uu____8346 with
      | FStar_Pervasives_Native.None  ->
          let uu____8361 =
            let uu____8362 =
              let uu____8367 = variable_not_found bv in (uu____8367, bvr) in
            FStar_Errors.Error uu____8362 in
          FStar_Exn.raise uu____8361
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8378 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8379 = FStar_Range.set_use_range r bvr in
          (uu____8378, uu____8379)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8398 = try_lookup_lid_aux env l in
      match uu____8398 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____8464 =
            let uu____8473 =
              let uu____8478 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____8478) in
            (uu____8473, r1) in
          FStar_Pervasives_Native.Some uu____8464
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8507 = try_lookup_lid env l in
      match uu____8507 with
      | FStar_Pervasives_Native.None  ->
          let uu____8534 =
            let uu____8535 =
              let uu____8540 = name_not_found l in
              (uu____8540, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____8535 in
          FStar_Exn.raise uu____8534
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___114_8578  ->
              match uu___114_8578 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____8580 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____8597 = lookup_qname env lid in
      match uu____8597 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8626,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8629;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8631;
              FStar_Syntax_Syntax.sigattrs = uu____8632;_},FStar_Pervasives_Native.None
            ),uu____8633)
          ->
          let uu____8682 =
            let uu____8693 =
              let uu____8698 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8698) in
            (uu____8693, q) in
          FStar_Pervasives_Native.Some uu____8682
      | uu____8715 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8754 = lookup_qname env lid in
      match uu____8754 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8779,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8782;
              FStar_Syntax_Syntax.sigquals = uu____8783;
              FStar_Syntax_Syntax.sigmeta = uu____8784;
              FStar_Syntax_Syntax.sigattrs = uu____8785;_},FStar_Pervasives_Native.None
            ),uu____8786)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8835 ->
          let uu____8856 =
            let uu____8857 =
              let uu____8862 = name_not_found lid in
              (uu____8862, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8857 in
          FStar_Exn.raise uu____8856
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8879 = lookup_qname env lid in
      match uu____8879 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8904,uvs,t,uu____8907,uu____8908,uu____8909);
              FStar_Syntax_Syntax.sigrng = uu____8910;
              FStar_Syntax_Syntax.sigquals = uu____8911;
              FStar_Syntax_Syntax.sigmeta = uu____8912;
              FStar_Syntax_Syntax.sigattrs = uu____8913;_},FStar_Pervasives_Native.None
            ),uu____8914)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8967 ->
          let uu____8988 =
            let uu____8989 =
              let uu____8994 = name_not_found lid in
              (uu____8994, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8989 in
          FStar_Exn.raise uu____8988
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9013 = lookup_qname env lid in
      match uu____9013 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9040,uu____9041,uu____9042,uu____9043,uu____9044,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9046;
              FStar_Syntax_Syntax.sigquals = uu____9047;
              FStar_Syntax_Syntax.sigmeta = uu____9048;
              FStar_Syntax_Syntax.sigattrs = uu____9049;_},uu____9050),uu____9051)
          -> (true, dcs)
      | uu____9112 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9143 = lookup_qname env lid in
      match uu____9143 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9164,uu____9165,uu____9166,l,uu____9168,uu____9169);
              FStar_Syntax_Syntax.sigrng = uu____9170;
              FStar_Syntax_Syntax.sigquals = uu____9171;
              FStar_Syntax_Syntax.sigmeta = uu____9172;
              FStar_Syntax_Syntax.sigattrs = uu____9173;_},uu____9174),uu____9175)
          -> l
      | uu____9230 ->
          let uu____9251 =
            let uu____9252 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9252 in
          failwith uu____9251
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
        let uu____9289 = lookup_qname env lid in
        match uu____9289 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9317) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9368,lbs),uu____9370) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9398 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9398
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9430 -> FStar_Pervasives_Native.None)
        | uu____9435 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9472 = lookup_qname env ftv in
      match uu____9472 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9496) ->
          let uu____9541 = effect_signature se in
          (match uu____9541 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9562,t),r) ->
               let uu____9577 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____9577)
      | uu____9578 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9607 = try_lookup_effect_lid env ftv in
      match uu____9607 with
      | FStar_Pervasives_Native.None  ->
          let uu____9610 =
            let uu____9611 =
              let uu____9616 = name_not_found ftv in
              (uu____9616, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____9611 in
          FStar_Exn.raise uu____9610
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
        let uu____9636 = lookup_qname env lid0 in
        match uu____9636 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____9667);
                FStar_Syntax_Syntax.sigrng = uu____9668;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____9670;
                FStar_Syntax_Syntax.sigattrs = uu____9671;_},FStar_Pervasives_Native.None
              ),uu____9672)
            ->
            let lid1 =
              let uu____9726 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____9726 in
            let uu____9727 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___115_9731  ->
                      match uu___115_9731 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9732 -> false)) in
            if uu____9727
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____9746 =
                      let uu____9747 =
                        let uu____9748 = get_range env in
                        FStar_Range.string_of_range uu____9748 in
                      let uu____9749 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____9750 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____9747 uu____9749 uu____9750 in
                    failwith uu____9746) in
               match (binders, univs1) with
               | ([],uu____9757) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____9774,uu____9775::uu____9776::uu____9777) ->
                   let uu____9782 =
                     let uu____9783 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____9784 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____9783 uu____9784 in
                   failwith uu____9782
               | uu____9791 ->
                   let uu____9796 =
                     let uu____9801 =
                       let uu____9802 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____9802) in
                     inst_tscheme_with uu____9801 insts in
                   (match uu____9796 with
                    | (uu____9813,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____9816 =
                          let uu____9817 = FStar_Syntax_Subst.compress t1 in
                          uu____9817.FStar_Syntax_Syntax.n in
                        (match uu____9816 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____9864 -> failwith "Impossible")))
        | uu____9871 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____9913 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____9913 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____9926,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____9933 = find1 l2 in
            (match uu____9933 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____9940 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____9940 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____9944 = find1 l in
            (match uu____9944 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____9960 = lookup_qname env l1 in
      match uu____9960 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____9983;
              FStar_Syntax_Syntax.sigrng = uu____9984;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9986;
              FStar_Syntax_Syntax.sigattrs = uu____9987;_},uu____9988),uu____9989)
          -> q
      | uu____10040 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10076 =
          let uu____10077 =
            let uu____10078 = FStar_Util.string_of_int i in
            let uu____10079 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10078 uu____10079 in
          failwith uu____10077 in
        let uu____10080 = lookup_datacon env lid in
        match uu____10080 with
        | (uu____10085,t) ->
            let uu____10087 =
              let uu____10088 = FStar_Syntax_Subst.compress t in
              uu____10088.FStar_Syntax_Syntax.n in
            (match uu____10087 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10092) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10123 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10123
                      FStar_Pervasives_Native.fst)
             | uu____10132 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10141 = lookup_qname env l in
      match uu____10141 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10162,uu____10163,uu____10164);
              FStar_Syntax_Syntax.sigrng = uu____10165;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10167;
              FStar_Syntax_Syntax.sigattrs = uu____10168;_},uu____10169),uu____10170)
          ->
          FStar_Util.for_some
            (fun uu___116_10223  ->
               match uu___116_10223 with
               | FStar_Syntax_Syntax.Projector uu____10224 -> true
               | uu____10229 -> false) quals
      | uu____10230 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10259 = lookup_qname env lid in
      match uu____10259 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10280,uu____10281,uu____10282,uu____10283,uu____10284,uu____10285);
              FStar_Syntax_Syntax.sigrng = uu____10286;
              FStar_Syntax_Syntax.sigquals = uu____10287;
              FStar_Syntax_Syntax.sigmeta = uu____10288;
              FStar_Syntax_Syntax.sigattrs = uu____10289;_},uu____10290),uu____10291)
          -> true
      | uu____10346 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10375 = lookup_qname env lid in
      match uu____10375 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10396,uu____10397,uu____10398,uu____10399,uu____10400,uu____10401);
              FStar_Syntax_Syntax.sigrng = uu____10402;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10404;
              FStar_Syntax_Syntax.sigattrs = uu____10405;_},uu____10406),uu____10407)
          ->
          FStar_Util.for_some
            (fun uu___117_10468  ->
               match uu___117_10468 with
               | FStar_Syntax_Syntax.RecordType uu____10469 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10478 -> true
               | uu____10487 -> false) quals
      | uu____10488 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10517 = lookup_qname env lid in
      match uu____10517 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____10538,uu____10539);
              FStar_Syntax_Syntax.sigrng = uu____10540;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10542;
              FStar_Syntax_Syntax.sigattrs = uu____10543;_},uu____10544),uu____10545)
          ->
          FStar_Util.for_some
            (fun uu___118_10602  ->
               match uu___118_10602 with
               | FStar_Syntax_Syntax.Action uu____10603 -> true
               | uu____10604 -> false) quals
      | uu____10605 -> false
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
      let uu____10637 =
        let uu____10638 = FStar_Syntax_Util.un_uinst head1 in
        uu____10638.FStar_Syntax_Syntax.n in
      match uu____10637 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10642 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10709 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10725) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10742 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10749 ->
                 FStar_Pervasives_Native.Some true
             | uu____10766 -> FStar_Pervasives_Native.Some false) in
      let uu____10767 =
        let uu____10770 = lookup_qname env lid in
        FStar_Util.bind_opt uu____10770 mapper in
      match uu____10767 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____10818 = lookup_qname env lid in
      match uu____10818 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10839,uu____10840,tps,uu____10842,uu____10843,uu____10844);
              FStar_Syntax_Syntax.sigrng = uu____10845;
              FStar_Syntax_Syntax.sigquals = uu____10846;
              FStar_Syntax_Syntax.sigmeta = uu____10847;
              FStar_Syntax_Syntax.sigattrs = uu____10848;_},uu____10849),uu____10850)
          -> FStar_List.length tps
      | uu____10913 ->
          let uu____10934 =
            let uu____10935 =
              let uu____10940 = name_not_found lid in
              (uu____10940, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____10935 in
          FStar_Exn.raise uu____10934
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
           (fun uu____10982  ->
              match uu____10982 with
              | (d,uu____10990) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11003 = effect_decl_opt env l in
      match uu____11003 with
      | FStar_Pervasives_Native.None  ->
          let uu____11018 =
            let uu____11019 =
              let uu____11024 = name_not_found l in
              (uu____11024, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11019 in
          FStar_Exn.raise uu____11018
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
            (let uu____11090 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11143  ->
                       match uu____11143 with
                       | (m1,m2,uu____11156,uu____11157,uu____11158) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11090 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11175 =
                   let uu____11176 =
                     let uu____11181 =
                       let uu____11182 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11183 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11182
                         uu____11183 in
                     (uu____11181, (env.range)) in
                   FStar_Errors.Error uu____11176 in
                 FStar_Exn.raise uu____11175
             | FStar_Pervasives_Native.Some
                 (uu____11190,uu____11191,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11234 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11234)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11261 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11287  ->
                match uu____11287 with
                | (d,uu____11293) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11261 with
      | FStar_Pervasives_Native.None  ->
          let uu____11304 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11304
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11317 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11317 with
           | (uu____11328,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11338)::(wp,uu____11340)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11376 -> failwith "Impossible"))
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
                 let uu____11425 = get_range env in
                 let uu____11426 =
                   let uu____11429 =
                     let uu____11430 =
                       let uu____11445 =
                         let uu____11448 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11448] in
                       (null_wp, uu____11445) in
                     FStar_Syntax_Syntax.Tm_app uu____11430 in
                   FStar_Syntax_Syntax.mk uu____11429 in
                 uu____11426 FStar_Pervasives_Native.None uu____11425 in
               let uu____11454 =
                 let uu____11455 =
                   let uu____11464 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11464] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11455;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11454)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___130_11475 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___130_11475.order);
              joins = (uu___130_11475.joins)
            } in
          let uu___131_11484 = env in
          {
            solver = (uu___131_11484.solver);
            range = (uu___131_11484.range);
            curmodule = (uu___131_11484.curmodule);
            gamma = (uu___131_11484.gamma);
            gamma_cache = (uu___131_11484.gamma_cache);
            modules = (uu___131_11484.modules);
            expected_typ = (uu___131_11484.expected_typ);
            sigtab = (uu___131_11484.sigtab);
            is_pattern = (uu___131_11484.is_pattern);
            instantiate_imp = (uu___131_11484.instantiate_imp);
            effects;
            generalize = (uu___131_11484.generalize);
            letrecs = (uu___131_11484.letrecs);
            top_level = (uu___131_11484.top_level);
            check_uvars = (uu___131_11484.check_uvars);
            use_eq = (uu___131_11484.use_eq);
            is_iface = (uu___131_11484.is_iface);
            admit = (uu___131_11484.admit);
            lax = (uu___131_11484.lax);
            lax_universes = (uu___131_11484.lax_universes);
            failhard = (uu___131_11484.failhard);
            nosynth = (uu___131_11484.nosynth);
            type_of = (uu___131_11484.type_of);
            universe_of = (uu___131_11484.universe_of);
            use_bv_sorts = (uu___131_11484.use_bv_sorts);
            qname_and_index = (uu___131_11484.qname_and_index);
            proof_ns = (uu___131_11484.proof_ns);
            synth = (uu___131_11484.synth);
            is_native_tactic = (uu___131_11484.is_native_tactic);
            identifier_info = (uu___131_11484.identifier_info)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____11501 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____11501 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____11591 = (e1.mlift).mlift_wp t wp in
                              let uu____11592 = l1 t wp e in
                              l2 t uu____11591 uu____11592))
                | uu____11593 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____11632 = inst_tscheme lift_t in
            match uu____11632 with
            | (uu____11639,lift_t1) ->
                let uu____11641 =
                  let uu____11644 =
                    let uu____11645 =
                      let uu____11660 =
                        let uu____11663 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11664 =
                          let uu____11667 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____11667] in
                        uu____11663 :: uu____11664 in
                      (lift_t1, uu____11660) in
                    FStar_Syntax_Syntax.Tm_app uu____11645 in
                  FStar_Syntax_Syntax.mk uu____11644 in
                uu____11641 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____11708 = inst_tscheme lift_t in
            match uu____11708 with
            | (uu____11715,lift_t1) ->
                let uu____11717 =
                  let uu____11720 =
                    let uu____11721 =
                      let uu____11736 =
                        let uu____11739 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11740 =
                          let uu____11743 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____11744 =
                            let uu____11747 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11747] in
                          uu____11743 :: uu____11744 in
                        uu____11739 :: uu____11740 in
                      (lift_t1, uu____11736) in
                    FStar_Syntax_Syntax.Tm_app uu____11721 in
                  FStar_Syntax_Syntax.mk uu____11720 in
                uu____11717 FStar_Pervasives_Native.None
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
              let uu____11785 =
                let uu____11786 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____11786
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____11785 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____11790 =
              let uu____11791 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____11791 in
            let uu____11792 =
              let uu____11793 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11811 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____11811) in
              FStar_Util.dflt "none" uu____11793 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11790
              uu____11792 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11837  ->
                    match uu____11837 with
                    | (e,uu____11845) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____11864 =
            match uu____11864 with
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
              let uu____11902 =
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
                                    (let uu____11923 =
                                       let uu____11932 =
                                         find_edge order1 (i, k) in
                                       let uu____11935 =
                                         find_edge order1 (k, j) in
                                       (uu____11932, uu____11935) in
                                     match uu____11923 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____11950 =
                                           compose_edges e1 e2 in
                                         [uu____11950]
                                     | uu____11951 -> []))))) in
              FStar_List.append order1 uu____11902 in
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
                   let uu____11980 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____11982 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____11982
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____11980
                   then
                     let uu____11987 =
                       let uu____11988 =
                         let uu____11993 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____11994 = get_range env in
                         (uu____11993, uu____11994) in
                       FStar_Errors.Error uu____11988 in
                     FStar_Exn.raise uu____11987
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
                                            let uu____12119 =
                                              let uu____12128 =
                                                find_edge order2 (i, k) in
                                              let uu____12131 =
                                                find_edge order2 (j, k) in
                                              (uu____12128, uu____12131) in
                                            match uu____12119 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12173,uu____12174)
                                                     ->
                                                     let uu____12181 =
                                                       let uu____12186 =
                                                         let uu____12187 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12187 in
                                                       let uu____12190 =
                                                         let uu____12191 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12191 in
                                                       (uu____12186,
                                                         uu____12190) in
                                                     (match uu____12181 with
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
                                            | uu____12226 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___132_12299 = env.effects in
              { decls = (uu___132_12299.decls); order = order2; joins } in
            let uu___133_12300 = env in
            {
              solver = (uu___133_12300.solver);
              range = (uu___133_12300.range);
              curmodule = (uu___133_12300.curmodule);
              gamma = (uu___133_12300.gamma);
              gamma_cache = (uu___133_12300.gamma_cache);
              modules = (uu___133_12300.modules);
              expected_typ = (uu___133_12300.expected_typ);
              sigtab = (uu___133_12300.sigtab);
              is_pattern = (uu___133_12300.is_pattern);
              instantiate_imp = (uu___133_12300.instantiate_imp);
              effects;
              generalize = (uu___133_12300.generalize);
              letrecs = (uu___133_12300.letrecs);
              top_level = (uu___133_12300.top_level);
              check_uvars = (uu___133_12300.check_uvars);
              use_eq = (uu___133_12300.use_eq);
              is_iface = (uu___133_12300.is_iface);
              admit = (uu___133_12300.admit);
              lax = (uu___133_12300.lax);
              lax_universes = (uu___133_12300.lax_universes);
              failhard = (uu___133_12300.failhard);
              nosynth = (uu___133_12300.nosynth);
              type_of = (uu___133_12300.type_of);
              universe_of = (uu___133_12300.universe_of);
              use_bv_sorts = (uu___133_12300.use_bv_sorts);
              qname_and_index = (uu___133_12300.qname_and_index);
              proof_ns = (uu___133_12300.proof_ns);
              synth = (uu___133_12300.synth);
              is_native_tactic = (uu___133_12300.is_native_tactic);
              identifier_info = (uu___133_12300.identifier_info)
            }))
      | uu____12301 -> env
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
        | uu____12327 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12337 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12337 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12354 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12354 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12372 =
                     let uu____12373 =
                       let uu____12378 =
                         let uu____12379 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12384 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12391 =
                           let uu____12392 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12392 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12379 uu____12384 uu____12391 in
                       (uu____12378, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12373 in
                   FStar_Exn.raise uu____12372)
                else ();
                (let inst1 =
                   let uu____12397 =
                     let uu____12406 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12406 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12423  ->
                        fun uu____12424  ->
                          match (uu____12423, uu____12424) with
                          | ((x,uu____12446),(t,uu____12448)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12397 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12467 =
                     let uu___134_12468 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___134_12468.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___134_12468.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___134_12468.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___134_12468.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12467
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
          let uu____12493 =
            let uu____12502 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____12502 in
          match uu____12493 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12527 =
                only_reifiable &&
                  (let uu____12529 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____12529) in
              if uu____12527
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12545 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____12547 =
                       let uu____12560 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____12560) in
                     (match uu____12547 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____12606 =
                            let uu____12609 = get_range env in
                            let uu____12610 =
                              let uu____12613 =
                                let uu____12614 =
                                  let uu____12629 =
                                    let uu____12632 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____12632; wp] in
                                  (repr, uu____12629) in
                                FStar_Syntax_Syntax.Tm_app uu____12614 in
                              FStar_Syntax_Syntax.mk uu____12613 in
                            uu____12610 FStar_Pervasives_Native.None
                              uu____12609 in
                          FStar_Pervasives_Native.Some uu____12606))
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
          let uu____12684 =
            let uu____12685 =
              let uu____12690 =
                let uu____12691 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____12691 in
              let uu____12692 = get_range env in (uu____12690, uu____12692) in
            FStar_Errors.Error uu____12685 in
          FStar_Exn.raise uu____12684 in
        let uu____12693 = effect_repr_aux true env c u_c in
        match uu____12693 with
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
      | uu____12733 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____12742 =
        let uu____12743 = FStar_Syntax_Subst.compress t in
        uu____12743.FStar_Syntax_Syntax.n in
      match uu____12742 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12746,c) ->
          is_reifiable_comp env c
      | uu____12764 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12788)::uu____12789 -> x :: rest
        | (Binding_sig_inst uu____12798)::uu____12799 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12814 = push1 x rest1 in local :: uu____12814 in
      let uu___135_12817 = env in
      let uu____12818 = push1 s env.gamma in
      {
        solver = (uu___135_12817.solver);
        range = (uu___135_12817.range);
        curmodule = (uu___135_12817.curmodule);
        gamma = uu____12818;
        gamma_cache = (uu___135_12817.gamma_cache);
        modules = (uu___135_12817.modules);
        expected_typ = (uu___135_12817.expected_typ);
        sigtab = (uu___135_12817.sigtab);
        is_pattern = (uu___135_12817.is_pattern);
        instantiate_imp = (uu___135_12817.instantiate_imp);
        effects = (uu___135_12817.effects);
        generalize = (uu___135_12817.generalize);
        letrecs = (uu___135_12817.letrecs);
        top_level = (uu___135_12817.top_level);
        check_uvars = (uu___135_12817.check_uvars);
        use_eq = (uu___135_12817.use_eq);
        is_iface = (uu___135_12817.is_iface);
        admit = (uu___135_12817.admit);
        lax = (uu___135_12817.lax);
        lax_universes = (uu___135_12817.lax_universes);
        failhard = (uu___135_12817.failhard);
        nosynth = (uu___135_12817.nosynth);
        type_of = (uu___135_12817.type_of);
        universe_of = (uu___135_12817.universe_of);
        use_bv_sorts = (uu___135_12817.use_bv_sorts);
        qname_and_index = (uu___135_12817.qname_and_index);
        proof_ns = (uu___135_12817.proof_ns);
        synth = (uu___135_12817.synth);
        is_native_tactic = (uu___135_12817.is_native_tactic);
        identifier_info = (uu___135_12817.identifier_info)
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
      let uu___136_12855 = env in
      {
        solver = (uu___136_12855.solver);
        range = (uu___136_12855.range);
        curmodule = (uu___136_12855.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___136_12855.gamma_cache);
        modules = (uu___136_12855.modules);
        expected_typ = (uu___136_12855.expected_typ);
        sigtab = (uu___136_12855.sigtab);
        is_pattern = (uu___136_12855.is_pattern);
        instantiate_imp = (uu___136_12855.instantiate_imp);
        effects = (uu___136_12855.effects);
        generalize = (uu___136_12855.generalize);
        letrecs = (uu___136_12855.letrecs);
        top_level = (uu___136_12855.top_level);
        check_uvars = (uu___136_12855.check_uvars);
        use_eq = (uu___136_12855.use_eq);
        is_iface = (uu___136_12855.is_iface);
        admit = (uu___136_12855.admit);
        lax = (uu___136_12855.lax);
        lax_universes = (uu___136_12855.lax_universes);
        failhard = (uu___136_12855.failhard);
        nosynth = (uu___136_12855.nosynth);
        type_of = (uu___136_12855.type_of);
        universe_of = (uu___136_12855.universe_of);
        use_bv_sorts = (uu___136_12855.use_bv_sorts);
        qname_and_index = (uu___136_12855.qname_and_index);
        proof_ns = (uu___136_12855.proof_ns);
        synth = (uu___136_12855.synth);
        is_native_tactic = (uu___136_12855.is_native_tactic);
        identifier_info = (uu___136_12855.identifier_info)
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
            (let uu___137_12889 = env in
             {
               solver = (uu___137_12889.solver);
               range = (uu___137_12889.range);
               curmodule = (uu___137_12889.curmodule);
               gamma = rest;
               gamma_cache = (uu___137_12889.gamma_cache);
               modules = (uu___137_12889.modules);
               expected_typ = (uu___137_12889.expected_typ);
               sigtab = (uu___137_12889.sigtab);
               is_pattern = (uu___137_12889.is_pattern);
               instantiate_imp = (uu___137_12889.instantiate_imp);
               effects = (uu___137_12889.effects);
               generalize = (uu___137_12889.generalize);
               letrecs = (uu___137_12889.letrecs);
               top_level = (uu___137_12889.top_level);
               check_uvars = (uu___137_12889.check_uvars);
               use_eq = (uu___137_12889.use_eq);
               is_iface = (uu___137_12889.is_iface);
               admit = (uu___137_12889.admit);
               lax = (uu___137_12889.lax);
               lax_universes = (uu___137_12889.lax_universes);
               failhard = (uu___137_12889.failhard);
               nosynth = (uu___137_12889.nosynth);
               type_of = (uu___137_12889.type_of);
               universe_of = (uu___137_12889.universe_of);
               use_bv_sorts = (uu___137_12889.use_bv_sorts);
               qname_and_index = (uu___137_12889.qname_and_index);
               proof_ns = (uu___137_12889.proof_ns);
               synth = (uu___137_12889.synth);
               is_native_tactic = (uu___137_12889.is_native_tactic);
               identifier_info = (uu___137_12889.identifier_info)
             }))
    | uu____12890 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12914  ->
             match uu____12914 with | (x,uu____12920) -> push_bv env1 x) env
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
            let uu___138_12950 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___138_12950.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___138_12950.FStar_Syntax_Syntax.index);
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
      (let uu___139_12985 = env in
       {
         solver = (uu___139_12985.solver);
         range = (uu___139_12985.range);
         curmodule = (uu___139_12985.curmodule);
         gamma = [];
         gamma_cache = (uu___139_12985.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___139_12985.sigtab);
         is_pattern = (uu___139_12985.is_pattern);
         instantiate_imp = (uu___139_12985.instantiate_imp);
         effects = (uu___139_12985.effects);
         generalize = (uu___139_12985.generalize);
         letrecs = (uu___139_12985.letrecs);
         top_level = (uu___139_12985.top_level);
         check_uvars = (uu___139_12985.check_uvars);
         use_eq = (uu___139_12985.use_eq);
         is_iface = (uu___139_12985.is_iface);
         admit = (uu___139_12985.admit);
         lax = (uu___139_12985.lax);
         lax_universes = (uu___139_12985.lax_universes);
         failhard = (uu___139_12985.failhard);
         nosynth = (uu___139_12985.nosynth);
         type_of = (uu___139_12985.type_of);
         universe_of = (uu___139_12985.universe_of);
         use_bv_sorts = (uu___139_12985.use_bv_sorts);
         qname_and_index = (uu___139_12985.qname_and_index);
         proof_ns = (uu___139_12985.proof_ns);
         synth = (uu___139_12985.synth);
         is_native_tactic = (uu___139_12985.is_native_tactic);
         identifier_info = (uu___139_12985.identifier_info)
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
        let uu____13022 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13022 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13050 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13050)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___140_13065 = env in
      {
        solver = (uu___140_13065.solver);
        range = (uu___140_13065.range);
        curmodule = (uu___140_13065.curmodule);
        gamma = (uu___140_13065.gamma);
        gamma_cache = (uu___140_13065.gamma_cache);
        modules = (uu___140_13065.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___140_13065.sigtab);
        is_pattern = (uu___140_13065.is_pattern);
        instantiate_imp = (uu___140_13065.instantiate_imp);
        effects = (uu___140_13065.effects);
        generalize = (uu___140_13065.generalize);
        letrecs = (uu___140_13065.letrecs);
        top_level = (uu___140_13065.top_level);
        check_uvars = (uu___140_13065.check_uvars);
        use_eq = false;
        is_iface = (uu___140_13065.is_iface);
        admit = (uu___140_13065.admit);
        lax = (uu___140_13065.lax);
        lax_universes = (uu___140_13065.lax_universes);
        failhard = (uu___140_13065.failhard);
        nosynth = (uu___140_13065.nosynth);
        type_of = (uu___140_13065.type_of);
        universe_of = (uu___140_13065.universe_of);
        use_bv_sorts = (uu___140_13065.use_bv_sorts);
        qname_and_index = (uu___140_13065.qname_and_index);
        proof_ns = (uu___140_13065.proof_ns);
        synth = (uu___140_13065.synth);
        is_native_tactic = (uu___140_13065.is_native_tactic);
        identifier_info = (uu___140_13065.identifier_info)
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
    let uu____13091 = expected_typ env_ in
    ((let uu___141_13097 = env_ in
      {
        solver = (uu___141_13097.solver);
        range = (uu___141_13097.range);
        curmodule = (uu___141_13097.curmodule);
        gamma = (uu___141_13097.gamma);
        gamma_cache = (uu___141_13097.gamma_cache);
        modules = (uu___141_13097.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___141_13097.sigtab);
        is_pattern = (uu___141_13097.is_pattern);
        instantiate_imp = (uu___141_13097.instantiate_imp);
        effects = (uu___141_13097.effects);
        generalize = (uu___141_13097.generalize);
        letrecs = (uu___141_13097.letrecs);
        top_level = (uu___141_13097.top_level);
        check_uvars = (uu___141_13097.check_uvars);
        use_eq = false;
        is_iface = (uu___141_13097.is_iface);
        admit = (uu___141_13097.admit);
        lax = (uu___141_13097.lax);
        lax_universes = (uu___141_13097.lax_universes);
        failhard = (uu___141_13097.failhard);
        nosynth = (uu___141_13097.nosynth);
        type_of = (uu___141_13097.type_of);
        universe_of = (uu___141_13097.universe_of);
        use_bv_sorts = (uu___141_13097.use_bv_sorts);
        qname_and_index = (uu___141_13097.qname_and_index);
        proof_ns = (uu___141_13097.proof_ns);
        synth = (uu___141_13097.synth);
        is_native_tactic = (uu___141_13097.is_native_tactic);
        identifier_info = (uu___141_13097.identifier_info)
      }), uu____13091)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13112 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___119_13122  ->
                    match uu___119_13122 with
                    | Binding_sig (uu____13125,se) -> [se]
                    | uu____13131 -> [])) in
          FStar_All.pipe_right uu____13112 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___142_13138 = env in
       {
         solver = (uu___142_13138.solver);
         range = (uu___142_13138.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___142_13138.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___142_13138.expected_typ);
         sigtab = (uu___142_13138.sigtab);
         is_pattern = (uu___142_13138.is_pattern);
         instantiate_imp = (uu___142_13138.instantiate_imp);
         effects = (uu___142_13138.effects);
         generalize = (uu___142_13138.generalize);
         letrecs = (uu___142_13138.letrecs);
         top_level = (uu___142_13138.top_level);
         check_uvars = (uu___142_13138.check_uvars);
         use_eq = (uu___142_13138.use_eq);
         is_iface = (uu___142_13138.is_iface);
         admit = (uu___142_13138.admit);
         lax = (uu___142_13138.lax);
         lax_universes = (uu___142_13138.lax_universes);
         failhard = (uu___142_13138.failhard);
         nosynth = (uu___142_13138.nosynth);
         type_of = (uu___142_13138.type_of);
         universe_of = (uu___142_13138.universe_of);
         use_bv_sorts = (uu___142_13138.use_bv_sorts);
         qname_and_index = (uu___142_13138.qname_and_index);
         proof_ns = (uu___142_13138.proof_ns);
         synth = (uu___142_13138.synth);
         is_native_tactic = (uu___142_13138.is_native_tactic);
         identifier_info = (uu___142_13138.identifier_info)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13220)::tl1 -> aux out tl1
      | (Binding_lid (uu____13224,(uu____13225,t)))::tl1 ->
          let uu____13240 =
            let uu____13247 = FStar_Syntax_Free.uvars t in
            ext out uu____13247 in
          aux uu____13240 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13254;
            FStar_Syntax_Syntax.index = uu____13255;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13262 =
            let uu____13269 = FStar_Syntax_Free.uvars t in
            ext out uu____13269 in
          aux uu____13262 tl1
      | (Binding_sig uu____13276)::uu____13277 -> out
      | (Binding_sig_inst uu____13286)::uu____13287 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13343)::tl1 -> aux out tl1
      | (Binding_univ uu____13355)::tl1 -> aux out tl1
      | (Binding_lid (uu____13359,(uu____13360,t)))::tl1 ->
          let uu____13375 =
            let uu____13378 = FStar_Syntax_Free.univs t in
            ext out uu____13378 in
          aux uu____13375 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13381;
            FStar_Syntax_Syntax.index = uu____13382;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13389 =
            let uu____13392 = FStar_Syntax_Free.univs t in
            ext out uu____13392 in
          aux uu____13389 tl1
      | (Binding_sig uu____13395)::uu____13396 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13450)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13466 = FStar_Util.fifo_set_add uname out in
          aux uu____13466 tl1
      | (Binding_lid (uu____13469,(uu____13470,t)))::tl1 ->
          let uu____13485 =
            let uu____13488 = FStar_Syntax_Free.univnames t in
            ext out uu____13488 in
          aux uu____13485 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13491;
            FStar_Syntax_Syntax.index = uu____13492;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13499 =
            let uu____13502 = FStar_Syntax_Free.univnames t in
            ext out uu____13502 in
          aux uu____13499 tl1
      | (Binding_sig uu____13505)::uu____13506 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___120_13531  ->
            match uu___120_13531 with
            | Binding_var x -> [x]
            | Binding_lid uu____13535 -> []
            | Binding_sig uu____13540 -> []
            | Binding_univ uu____13547 -> []
            | Binding_sig_inst uu____13548 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____13565 =
      let uu____13568 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____13568
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____13565 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____13593 =
      let uu____13594 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___121_13604  ->
                match uu___121_13604 with
                | Binding_var x ->
                    let uu____13606 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____13606
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13609) ->
                    let uu____13610 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____13610
                | Binding_sig (ls,uu____13612) ->
                    let uu____13617 =
                      let uu____13618 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13618
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____13617
                | Binding_sig_inst (ls,uu____13628,uu____13629) ->
                    let uu____13634 =
                      let uu____13635 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13635
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____13634)) in
      FStar_All.pipe_right uu____13594 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____13593 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____13654 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____13654
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13682  ->
                 fun uu____13683  ->
                   match (uu____13682, uu____13683) with
                   | ((b1,uu____13701),(b2,uu____13703)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___122_13750  ->
    match uu___122_13750 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____13751 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___123_13770  ->
             match uu___123_13770 with
             | Binding_sig (lids,uu____13776) -> FStar_List.append lids keys
             | uu____13781 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13787  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13823) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13842,uu____13843) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13880 = list_prefix p path1 in
            if uu____13880 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13894 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13894
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___143_13924 = e in
            {
              solver = (uu___143_13924.solver);
              range = (uu___143_13924.range);
              curmodule = (uu___143_13924.curmodule);
              gamma = (uu___143_13924.gamma);
              gamma_cache = (uu___143_13924.gamma_cache);
              modules = (uu___143_13924.modules);
              expected_typ = (uu___143_13924.expected_typ);
              sigtab = (uu___143_13924.sigtab);
              is_pattern = (uu___143_13924.is_pattern);
              instantiate_imp = (uu___143_13924.instantiate_imp);
              effects = (uu___143_13924.effects);
              generalize = (uu___143_13924.generalize);
              letrecs = (uu___143_13924.letrecs);
              top_level = (uu___143_13924.top_level);
              check_uvars = (uu___143_13924.check_uvars);
              use_eq = (uu___143_13924.use_eq);
              is_iface = (uu___143_13924.is_iface);
              admit = (uu___143_13924.admit);
              lax = (uu___143_13924.lax);
              lax_universes = (uu___143_13924.lax_universes);
              failhard = (uu___143_13924.failhard);
              nosynth = (uu___143_13924.nosynth);
              type_of = (uu___143_13924.type_of);
              universe_of = (uu___143_13924.universe_of);
              use_bv_sorts = (uu___143_13924.use_bv_sorts);
              qname_and_index = (uu___143_13924.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___143_13924.synth);
              is_native_tactic = (uu___143_13924.is_native_tactic);
              identifier_info = (uu___143_13924.identifier_info)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___144_13951 = e in
    {
      solver = (uu___144_13951.solver);
      range = (uu___144_13951.range);
      curmodule = (uu___144_13951.curmodule);
      gamma = (uu___144_13951.gamma);
      gamma_cache = (uu___144_13951.gamma_cache);
      modules = (uu___144_13951.modules);
      expected_typ = (uu___144_13951.expected_typ);
      sigtab = (uu___144_13951.sigtab);
      is_pattern = (uu___144_13951.is_pattern);
      instantiate_imp = (uu___144_13951.instantiate_imp);
      effects = (uu___144_13951.effects);
      generalize = (uu___144_13951.generalize);
      letrecs = (uu___144_13951.letrecs);
      top_level = (uu___144_13951.top_level);
      check_uvars = (uu___144_13951.check_uvars);
      use_eq = (uu___144_13951.use_eq);
      is_iface = (uu___144_13951.is_iface);
      admit = (uu___144_13951.admit);
      lax = (uu___144_13951.lax);
      lax_universes = (uu___144_13951.lax_universes);
      failhard = (uu___144_13951.failhard);
      nosynth = (uu___144_13951.nosynth);
      type_of = (uu___144_13951.type_of);
      universe_of = (uu___144_13951.universe_of);
      use_bv_sorts = (uu___144_13951.use_bv_sorts);
      qname_and_index = (uu___144_13951.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___144_13951.synth);
      is_native_tactic = (uu___144_13951.is_native_tactic);
      identifier_info = (uu___144_13951.identifier_info)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____13966::rest ->
        let uu___145_13970 = e in
        {
          solver = (uu___145_13970.solver);
          range = (uu___145_13970.range);
          curmodule = (uu___145_13970.curmodule);
          gamma = (uu___145_13970.gamma);
          gamma_cache = (uu___145_13970.gamma_cache);
          modules = (uu___145_13970.modules);
          expected_typ = (uu___145_13970.expected_typ);
          sigtab = (uu___145_13970.sigtab);
          is_pattern = (uu___145_13970.is_pattern);
          instantiate_imp = (uu___145_13970.instantiate_imp);
          effects = (uu___145_13970.effects);
          generalize = (uu___145_13970.generalize);
          letrecs = (uu___145_13970.letrecs);
          top_level = (uu___145_13970.top_level);
          check_uvars = (uu___145_13970.check_uvars);
          use_eq = (uu___145_13970.use_eq);
          is_iface = (uu___145_13970.is_iface);
          admit = (uu___145_13970.admit);
          lax = (uu___145_13970.lax);
          lax_universes = (uu___145_13970.lax_universes);
          failhard = (uu___145_13970.failhard);
          nosynth = (uu___145_13970.nosynth);
          type_of = (uu___145_13970.type_of);
          universe_of = (uu___145_13970.universe_of);
          use_bv_sorts = (uu___145_13970.use_bv_sorts);
          qname_and_index = (uu___145_13970.qname_and_index);
          proof_ns = rest;
          synth = (uu___145_13970.synth);
          is_native_tactic = (uu___145_13970.is_native_tactic);
          identifier_info = (uu___145_13970.identifier_info)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___146_13983 = e in
      {
        solver = (uu___146_13983.solver);
        range = (uu___146_13983.range);
        curmodule = (uu___146_13983.curmodule);
        gamma = (uu___146_13983.gamma);
        gamma_cache = (uu___146_13983.gamma_cache);
        modules = (uu___146_13983.modules);
        expected_typ = (uu___146_13983.expected_typ);
        sigtab = (uu___146_13983.sigtab);
        is_pattern = (uu___146_13983.is_pattern);
        instantiate_imp = (uu___146_13983.instantiate_imp);
        effects = (uu___146_13983.effects);
        generalize = (uu___146_13983.generalize);
        letrecs = (uu___146_13983.letrecs);
        top_level = (uu___146_13983.top_level);
        check_uvars = (uu___146_13983.check_uvars);
        use_eq = (uu___146_13983.use_eq);
        is_iface = (uu___146_13983.is_iface);
        admit = (uu___146_13983.admit);
        lax = (uu___146_13983.lax);
        lax_universes = (uu___146_13983.lax_universes);
        failhard = (uu___146_13983.failhard);
        nosynth = (uu___146_13983.nosynth);
        type_of = (uu___146_13983.type_of);
        universe_of = (uu___146_13983.universe_of);
        use_bv_sorts = (uu___146_13983.use_bv_sorts);
        qname_and_index = (uu___146_13983.qname_and_index);
        proof_ns = ns;
        synth = (uu___146_13983.synth);
        is_native_tactic = (uu___146_13983.is_native_tactic);
        identifier_info = (uu___146_13983.identifier_info)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____14012 =
        FStar_List.map
          (fun fpns  ->
             let uu____14034 =
               let uu____14035 =
                 let uu____14036 =
                   FStar_List.map
                     (fun uu____14048  ->
                        match uu____14048 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____14036 in
               Prims.strcat uu____14035 "]" in
             Prims.strcat "[" uu____14034) pns in
      FStar_String.concat ";" uu____14012 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____14064  -> ());
    push = (fun uu____14066  -> ());
    pop = (fun uu____14068  -> ());
    mark = (fun uu____14070  -> ());
    reset_mark = (fun uu____14072  -> ());
    commit_mark = (fun uu____14074  -> ());
    encode_modul = (fun uu____14077  -> fun uu____14078  -> ());
    encode_sig = (fun uu____14081  -> fun uu____14082  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14088 =
             let uu____14095 = FStar_Options.peek () in (e, g, uu____14095) in
           [uu____14088]);
    solve = (fun uu____14111  -> fun uu____14112  -> fun uu____14113  -> ());
    is_trivial = (fun uu____14120  -> fun uu____14121  -> false);
    finish = (fun uu____14123  -> ());
    refresh = (fun uu____14125  -> ())
  }