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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;_} -> __fname__failhard
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
        failhard = __fname__failhard; type_of = __fname__type_of;
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
      | (NoDelta ,uu____4518) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4519,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4520,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4521 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4530 . Prims.unit -> 'Auu____4530 FStar_Util.smap =
  fun uu____4536  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4541 . Prims.unit -> 'Auu____4541 FStar_Util.smap =
  fun uu____4547  -> FStar_Util.smap_create (Prims.parse_int "100")
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
          let uu____4596 = new_gamma_cache () in
          let uu____4599 = new_sigtab () in
          let uu____4602 =
            let uu____4603 = FStar_Options.using_facts_from () in
            match uu____4603 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____4613 =
                  let uu____4622 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____4622 [([], false)] in
                [uu____4613]
            | FStar_Pervasives_Native.None  -> [[]] in
          let uu____4695 =
            FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____4596;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____4599;
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
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = FStar_Pervasives_Native.None;
            proof_ns = uu____4602;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____4729  -> false);
            identifier_info = uu____4695
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
  fun uu____4800  ->
    let uu____4801 = FStar_ST.op_Bang query_indices in
    match uu____4801 with
    | [] -> failwith "Empty query indices!"
    | uu____4858 ->
        let uu____4867 =
          let uu____4876 =
            let uu____4883 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____4883 in
          let uu____4940 = FStar_ST.op_Bang query_indices in uu____4876 ::
            uu____4940 in
        FStar_ST.op_Colon_Equals query_indices uu____4867
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5042  ->
    let uu____5043 = FStar_ST.op_Bang query_indices in
    match uu____5043 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5171  ->
    match uu____5171 with
    | (l,n1) ->
        let uu____5178 = FStar_ST.op_Bang query_indices in
        (match uu____5178 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5303 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5321  ->
    let uu____5322 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5322
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____5382  ->
    let uu____5383 = FStar_ST.op_Bang query_indices in
    match uu____5383 with
    | hd1::uu____5435::tl1 ->
        FStar_ST.op_Colon_Equals query_indices (hd1 :: tl1)
    | uu____5517 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5544 =
       let uu____5547 = FStar_ST.op_Bang stack in env :: uu____5547 in
     FStar_ST.op_Colon_Equals stack uu____5544);
    (let uu___122_5586 = env in
     let uu____5587 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5590 = FStar_Util.smap_copy (sigtab env) in
     let uu____5593 =
       let uu____5596 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5596 in
     {
       solver = (uu___122_5586.solver);
       range = (uu___122_5586.range);
       curmodule = (uu___122_5586.curmodule);
       gamma = (uu___122_5586.gamma);
       gamma_cache = uu____5587;
       modules = (uu___122_5586.modules);
       expected_typ = (uu___122_5586.expected_typ);
       sigtab = uu____5590;
       is_pattern = (uu___122_5586.is_pattern);
       instantiate_imp = (uu___122_5586.instantiate_imp);
       effects = (uu___122_5586.effects);
       generalize = (uu___122_5586.generalize);
       letrecs = (uu___122_5586.letrecs);
       top_level = (uu___122_5586.top_level);
       check_uvars = (uu___122_5586.check_uvars);
       use_eq = (uu___122_5586.use_eq);
       is_iface = (uu___122_5586.is_iface);
       admit = (uu___122_5586.admit);
       lax = (uu___122_5586.lax);
       lax_universes = (uu___122_5586.lax_universes);
       failhard = (uu___122_5586.failhard);
       type_of = (uu___122_5586.type_of);
       universe_of = (uu___122_5586.universe_of);
       use_bv_sorts = (uu___122_5586.use_bv_sorts);
       qname_and_index = (uu___122_5586.qname_and_index);
       proof_ns = (uu___122_5586.proof_ns);
       synth = (uu___122_5586.synth);
       is_native_tactic = (uu___122_5586.is_native_tactic);
       identifier_info = uu____5593
     })
let pop_stack: Prims.unit -> env =
  fun uu____5624  ->
    let uu____5625 = FStar_ST.op_Bang stack in
    match uu____5625 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____5669 -> failwith "Impossible: Too many pops"
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
    (let uu____5709 = pop_stack () in ());
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
        let uu____5737 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____5763  ->
                  match uu____5763 with
                  | (m,uu____5769) -> FStar_Ident.lid_equals l m)) in
        (match uu____5737 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___123_5776 = env in
               {
                 solver = (uu___123_5776.solver);
                 range = (uu___123_5776.range);
                 curmodule = (uu___123_5776.curmodule);
                 gamma = (uu___123_5776.gamma);
                 gamma_cache = (uu___123_5776.gamma_cache);
                 modules = (uu___123_5776.modules);
                 expected_typ = (uu___123_5776.expected_typ);
                 sigtab = (uu___123_5776.sigtab);
                 is_pattern = (uu___123_5776.is_pattern);
                 instantiate_imp = (uu___123_5776.instantiate_imp);
                 effects = (uu___123_5776.effects);
                 generalize = (uu___123_5776.generalize);
                 letrecs = (uu___123_5776.letrecs);
                 top_level = (uu___123_5776.top_level);
                 check_uvars = (uu___123_5776.check_uvars);
                 use_eq = (uu___123_5776.use_eq);
                 is_iface = (uu___123_5776.is_iface);
                 admit = (uu___123_5776.admit);
                 lax = (uu___123_5776.lax);
                 lax_universes = (uu___123_5776.lax_universes);
                 failhard = (uu___123_5776.failhard);
                 type_of = (uu___123_5776.type_of);
                 universe_of = (uu___123_5776.universe_of);
                 use_bv_sorts = (uu___123_5776.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___123_5776.proof_ns);
                 synth = (uu___123_5776.synth);
                 is_native_tactic = (uu___123_5776.is_native_tactic);
                 identifier_info = (uu___123_5776.identifier_info)
               }))
         | FStar_Pervasives_Native.Some (uu____5781,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___124_5789 = env in
               {
                 solver = (uu___124_5789.solver);
                 range = (uu___124_5789.range);
                 curmodule = (uu___124_5789.curmodule);
                 gamma = (uu___124_5789.gamma);
                 gamma_cache = (uu___124_5789.gamma_cache);
                 modules = (uu___124_5789.modules);
                 expected_typ = (uu___124_5789.expected_typ);
                 sigtab = (uu___124_5789.sigtab);
                 is_pattern = (uu___124_5789.is_pattern);
                 instantiate_imp = (uu___124_5789.instantiate_imp);
                 effects = (uu___124_5789.effects);
                 generalize = (uu___124_5789.generalize);
                 letrecs = (uu___124_5789.letrecs);
                 top_level = (uu___124_5789.top_level);
                 check_uvars = (uu___124_5789.check_uvars);
                 use_eq = (uu___124_5789.use_eq);
                 is_iface = (uu___124_5789.is_iface);
                 admit = (uu___124_5789.admit);
                 lax = (uu___124_5789.lax);
                 lax_universes = (uu___124_5789.lax_universes);
                 failhard = (uu___124_5789.failhard);
                 type_of = (uu___124_5789.type_of);
                 universe_of = (uu___124_5789.universe_of);
                 use_bv_sorts = (uu___124_5789.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___124_5789.proof_ns);
                 synth = (uu___124_5789.synth);
                 is_native_tactic = (uu___124_5789.is_native_tactic);
                 identifier_info = (uu___124_5789.identifier_info)
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
        (let uu___125_5811 = e in
         {
           solver = (uu___125_5811.solver);
           range = r;
           curmodule = (uu___125_5811.curmodule);
           gamma = (uu___125_5811.gamma);
           gamma_cache = (uu___125_5811.gamma_cache);
           modules = (uu___125_5811.modules);
           expected_typ = (uu___125_5811.expected_typ);
           sigtab = (uu___125_5811.sigtab);
           is_pattern = (uu___125_5811.is_pattern);
           instantiate_imp = (uu___125_5811.instantiate_imp);
           effects = (uu___125_5811.effects);
           generalize = (uu___125_5811.generalize);
           letrecs = (uu___125_5811.letrecs);
           top_level = (uu___125_5811.top_level);
           check_uvars = (uu___125_5811.check_uvars);
           use_eq = (uu___125_5811.use_eq);
           is_iface = (uu___125_5811.is_iface);
           admit = (uu___125_5811.admit);
           lax = (uu___125_5811.lax);
           lax_universes = (uu___125_5811.lax_universes);
           failhard = (uu___125_5811.failhard);
           type_of = (uu___125_5811.type_of);
           universe_of = (uu___125_5811.universe_of);
           use_bv_sorts = (uu___125_5811.use_bv_sorts);
           qname_and_index = (uu___125_5811.qname_and_index);
           proof_ns = (uu___125_5811.proof_ns);
           synth = (uu___125_5811.synth);
           is_native_tactic = (uu___125_5811.is_native_tactic);
           identifier_info = (uu___125_5811.identifier_info)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____5824 =
        let uu____5825 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____5825 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5824
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____5858 =
          let uu____5859 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____5859 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5858
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____5892 =
          let uu____5893 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____5893 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5892
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____5927 =
        let uu____5928 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____5928 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5927
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___126_5967 = env in
      {
        solver = (uu___126_5967.solver);
        range = (uu___126_5967.range);
        curmodule = lid;
        gamma = (uu___126_5967.gamma);
        gamma_cache = (uu___126_5967.gamma_cache);
        modules = (uu___126_5967.modules);
        expected_typ = (uu___126_5967.expected_typ);
        sigtab = (uu___126_5967.sigtab);
        is_pattern = (uu___126_5967.is_pattern);
        instantiate_imp = (uu___126_5967.instantiate_imp);
        effects = (uu___126_5967.effects);
        generalize = (uu___126_5967.generalize);
        letrecs = (uu___126_5967.letrecs);
        top_level = (uu___126_5967.top_level);
        check_uvars = (uu___126_5967.check_uvars);
        use_eq = (uu___126_5967.use_eq);
        is_iface = (uu___126_5967.is_iface);
        admit = (uu___126_5967.admit);
        lax = (uu___126_5967.lax);
        lax_universes = (uu___126_5967.lax_universes);
        failhard = (uu___126_5967.failhard);
        type_of = (uu___126_5967.type_of);
        universe_of = (uu___126_5967.universe_of);
        use_bv_sorts = (uu___126_5967.use_bv_sorts);
        qname_and_index = (uu___126_5967.qname_and_index);
        proof_ns = (uu___126_5967.proof_ns);
        synth = (uu___126_5967.synth);
        is_native_tactic = (uu___126_5967.is_native_tactic);
        identifier_info = (uu___126_5967.identifier_info)
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
    let uu____5998 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____5998
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6002  ->
    let uu____6003 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6003
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
      | ((formals,t),uu____6043) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6067 = FStar_Syntax_Subst.subst vs t in (us, uu____6067)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___110_6081  ->
    match uu___110_6081 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6105  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6120 = inst_tscheme t in
      match uu____6120 with
      | (us,t1) ->
          let uu____6131 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6131)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6147  ->
          match uu____6147 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6162 =
                         let uu____6163 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6164 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6165 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6166 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6163 uu____6164 uu____6165 uu____6166 in
                       failwith uu____6162)
                    else ();
                    (let uu____6168 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6168))
               | uu____6175 ->
                   let uu____6176 =
                     let uu____6177 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6177 in
                   failwith uu____6176)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6182 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6187 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6192 -> false
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
             | ([],uu____6228) -> Maybe
             | (uu____6235,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6254 -> No in
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
          let uu____6361 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6361 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___111_6406  ->
                   match uu___111_6406 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____6449 =
                           let uu____6468 =
                             let uu____6483 = inst_tscheme t in
                             FStar_Util.Inl uu____6483 in
                           (uu____6468, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____6449
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6549,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6551);
                                     FStar_Syntax_Syntax.sigrng = uu____6552;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6553;
                                     FStar_Syntax_Syntax.sigmeta = uu____6554;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6555;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6575 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6575
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____6621 ->
                             FStar_Pervasives_Native.Some t
                         | uu____6628 -> cache t in
                       let uu____6629 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6629 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____6704 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6704 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____6790 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____6870 = find_in_sigtab env lid in
         match uu____6870 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6969) ->
          add_sigelts env ses
      | uu____6978 ->
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
            | uu____6992 -> ()))
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
        (fun uu___112_7021  ->
           match uu___112_7021 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7039 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7074,lb::[]),uu____7076) ->
          let uu____7089 =
            let uu____7098 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7107 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7098, uu____7107) in
          FStar_Pervasives_Native.Some uu____7089
      | FStar_Syntax_Syntax.Sig_let ((uu____7120,lbs),uu____7122) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7158 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7170 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7170
                   then
                     let uu____7181 =
                       let uu____7190 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7199 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7190, uu____7199) in
                     FStar_Pervasives_Native.Some uu____7181
                   else FStar_Pervasives_Native.None)
      | uu____7221 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7255 =
          let uu____7264 =
            let uu____7269 =
              let uu____7270 =
                let uu____7273 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7273 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7270) in
            inst_tscheme uu____7269 in
          (uu____7264, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7255
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7293,uu____7294) ->
        let uu____7299 =
          let uu____7308 =
            let uu____7313 =
              let uu____7314 =
                let uu____7317 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7317 in
              (us, uu____7314) in
            inst_tscheme uu____7313 in
          (uu____7308, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7299
    | uu____7334 -> FStar_Pervasives_Native.None
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
      let mapper uu____7394 =
        match uu____7394 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____7490,uvs,t,uu____7493,uu____7494,uu____7495);
                    FStar_Syntax_Syntax.sigrng = uu____7496;
                    FStar_Syntax_Syntax.sigquals = uu____7497;
                    FStar_Syntax_Syntax.sigmeta = uu____7498;
                    FStar_Syntax_Syntax.sigattrs = uu____7499;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7520 =
                   let uu____7529 = inst_tscheme (uvs, t) in
                   (uu____7529, rng) in
                 FStar_Pervasives_Native.Some uu____7520
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7549;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7551;
                    FStar_Syntax_Syntax.sigattrs = uu____7552;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7569 =
                   let uu____7570 = in_cur_mod env l in uu____7570 = Yes in
                 if uu____7569
                 then
                   let uu____7581 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7581
                    then
                      let uu____7594 =
                        let uu____7603 = inst_tscheme (uvs, t) in
                        (uu____7603, rng) in
                      FStar_Pervasives_Native.Some uu____7594
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____7630 =
                      let uu____7639 = inst_tscheme (uvs, t) in
                      (uu____7639, rng) in
                    FStar_Pervasives_Native.Some uu____7630)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7660,uu____7661);
                    FStar_Syntax_Syntax.sigrng = uu____7662;
                    FStar_Syntax_Syntax.sigquals = uu____7663;
                    FStar_Syntax_Syntax.sigmeta = uu____7664;
                    FStar_Syntax_Syntax.sigattrs = uu____7665;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____7704 =
                        let uu____7713 = inst_tscheme (uvs, k) in
                        (uu____7713, rng) in
                      FStar_Pervasives_Native.Some uu____7704
                  | uu____7730 ->
                      let uu____7731 =
                        let uu____7740 =
                          let uu____7745 =
                            let uu____7746 =
                              let uu____7749 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7749 in
                            (uvs, uu____7746) in
                          inst_tscheme uu____7745 in
                        (uu____7740, rng) in
                      FStar_Pervasives_Native.Some uu____7731)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7770,uu____7771);
                    FStar_Syntax_Syntax.sigrng = uu____7772;
                    FStar_Syntax_Syntax.sigquals = uu____7773;
                    FStar_Syntax_Syntax.sigmeta = uu____7774;
                    FStar_Syntax_Syntax.sigattrs = uu____7775;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____7815 =
                        let uu____7824 = inst_tscheme_with (uvs, k) us in
                        (uu____7824, rng) in
                      FStar_Pervasives_Native.Some uu____7815
                  | uu____7841 ->
                      let uu____7842 =
                        let uu____7851 =
                          let uu____7856 =
                            let uu____7857 =
                              let uu____7860 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7860 in
                            (uvs, uu____7857) in
                          inst_tscheme_with uu____7856 us in
                        (uu____7851, rng) in
                      FStar_Pervasives_Native.Some uu____7842)
             | FStar_Util.Inr se ->
                 let uu____7894 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____7915;
                        FStar_Syntax_Syntax.sigrng = uu____7916;
                        FStar_Syntax_Syntax.sigquals = uu____7917;
                        FStar_Syntax_Syntax.sigmeta = uu____7918;
                        FStar_Syntax_Syntax.sigattrs = uu____7919;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____7934 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____7894
                   (FStar_Util.map_option
                      (fun uu____7982  ->
                         match uu____7982 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8013 =
        let uu____8024 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8024 mapper in
      match uu____8013 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___127_8117 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___127_8117.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___127_8117.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8144 = lookup_qname env l in
      match uu____8144 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8183 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8233 = try_lookup_bv env bv in
      match uu____8233 with
      | FStar_Pervasives_Native.None  ->
          let uu____8248 =
            let uu____8249 =
              let uu____8254 = variable_not_found bv in (uu____8254, bvr) in
            FStar_Errors.Error uu____8249 in
          FStar_Exn.raise uu____8248
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8265 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8266 = FStar_Range.set_use_range r bvr in
          (uu____8265, uu____8266)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8285 = try_lookup_lid_aux env l in
      match uu____8285 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____8351 =
            let uu____8360 =
              let uu____8365 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____8365) in
            (uu____8360, r1) in
          FStar_Pervasives_Native.Some uu____8351
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8394 = try_lookup_lid env l in
      match uu____8394 with
      | FStar_Pervasives_Native.None  ->
          let uu____8421 =
            let uu____8422 =
              let uu____8427 = name_not_found l in
              (uu____8427, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____8422 in
          FStar_Exn.raise uu____8421
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___113_8465  ->
              match uu___113_8465 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____8467 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____8484 = lookup_qname env lid in
      match uu____8484 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8513,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8516;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8518;
              FStar_Syntax_Syntax.sigattrs = uu____8519;_},FStar_Pervasives_Native.None
            ),uu____8520)
          ->
          let uu____8569 =
            let uu____8580 =
              let uu____8585 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8585) in
            (uu____8580, q) in
          FStar_Pervasives_Native.Some uu____8569
      | uu____8602 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8641 = lookup_qname env lid in
      match uu____8641 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8666,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8669;
              FStar_Syntax_Syntax.sigquals = uu____8670;
              FStar_Syntax_Syntax.sigmeta = uu____8671;
              FStar_Syntax_Syntax.sigattrs = uu____8672;_},FStar_Pervasives_Native.None
            ),uu____8673)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8722 ->
          let uu____8743 =
            let uu____8744 =
              let uu____8749 = name_not_found lid in
              (uu____8749, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8744 in
          FStar_Exn.raise uu____8743
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8766 = lookup_qname env lid in
      match uu____8766 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8791,uvs,t,uu____8794,uu____8795,uu____8796);
              FStar_Syntax_Syntax.sigrng = uu____8797;
              FStar_Syntax_Syntax.sigquals = uu____8798;
              FStar_Syntax_Syntax.sigmeta = uu____8799;
              FStar_Syntax_Syntax.sigattrs = uu____8800;_},FStar_Pervasives_Native.None
            ),uu____8801)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8854 ->
          let uu____8875 =
            let uu____8876 =
              let uu____8881 = name_not_found lid in
              (uu____8881, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8876 in
          FStar_Exn.raise uu____8875
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8900 = lookup_qname env lid in
      match uu____8900 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____8927,uu____8928,uu____8929,uu____8930,uu____8931,dcs);
              FStar_Syntax_Syntax.sigrng = uu____8933;
              FStar_Syntax_Syntax.sigquals = uu____8934;
              FStar_Syntax_Syntax.sigmeta = uu____8935;
              FStar_Syntax_Syntax.sigattrs = uu____8936;_},uu____8937),uu____8938)
          -> (true, dcs)
      | uu____8999 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9030 = lookup_qname env lid in
      match uu____9030 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9051,uu____9052,uu____9053,l,uu____9055,uu____9056);
              FStar_Syntax_Syntax.sigrng = uu____9057;
              FStar_Syntax_Syntax.sigquals = uu____9058;
              FStar_Syntax_Syntax.sigmeta = uu____9059;
              FStar_Syntax_Syntax.sigattrs = uu____9060;_},uu____9061),uu____9062)
          -> l
      | uu____9117 ->
          let uu____9138 =
            let uu____9139 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9139 in
          failwith uu____9138
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
        let uu____9176 = lookup_qname env lid in
        match uu____9176 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9204) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9255,lbs),uu____9257) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9285 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9285
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9317 -> FStar_Pervasives_Native.None)
        | uu____9322 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9359 = lookup_qname env ftv in
      match uu____9359 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9383) ->
          let uu____9428 = effect_signature se in
          (match uu____9428 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9449,t),r) ->
               let uu____9464 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____9464)
      | uu____9465 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9494 = try_lookup_effect_lid env ftv in
      match uu____9494 with
      | FStar_Pervasives_Native.None  ->
          let uu____9497 =
            let uu____9498 =
              let uu____9503 = name_not_found ftv in
              (uu____9503, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____9498 in
          FStar_Exn.raise uu____9497
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
        let uu____9523 = lookup_qname env lid0 in
        match uu____9523 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____9554);
                FStar_Syntax_Syntax.sigrng = uu____9555;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____9557;
                FStar_Syntax_Syntax.sigattrs = uu____9558;_},FStar_Pervasives_Native.None
              ),uu____9559)
            ->
            let lid1 =
              let uu____9613 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____9613 in
            let uu____9614 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___114_9618  ->
                      match uu___114_9618 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9619 -> false)) in
            if uu____9614
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____9633 =
                      let uu____9634 =
                        let uu____9635 = get_range env in
                        FStar_Range.string_of_range uu____9635 in
                      let uu____9636 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____9637 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____9634 uu____9636 uu____9637 in
                    failwith uu____9633) in
               match (binders, univs1) with
               | ([],uu____9644) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____9661,uu____9662::uu____9663::uu____9664) ->
                   let uu____9669 =
                     let uu____9670 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____9671 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____9670 uu____9671 in
                   failwith uu____9669
               | uu____9678 ->
                   let uu____9683 =
                     let uu____9688 =
                       let uu____9689 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____9689) in
                     inst_tscheme_with uu____9688 insts in
                   (match uu____9683 with
                    | (uu____9700,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____9703 =
                          let uu____9704 = FStar_Syntax_Subst.compress t1 in
                          uu____9704.FStar_Syntax_Syntax.n in
                        (match uu____9703 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____9751 -> failwith "Impossible")))
        | uu____9758 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____9800 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____9800 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____9813,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____9820 = find1 l2 in
            (match uu____9820 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____9827 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____9827 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____9831 = find1 l in
            (match uu____9831 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____9847 = lookup_qname env l1 in
      match uu____9847 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____9870;
              FStar_Syntax_Syntax.sigrng = uu____9871;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9873;
              FStar_Syntax_Syntax.sigattrs = uu____9874;_},uu____9875),uu____9876)
          -> q
      | uu____9927 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____9963 =
          let uu____9964 =
            let uu____9965 = FStar_Util.string_of_int i in
            let uu____9966 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____9965 uu____9966 in
          failwith uu____9964 in
        let uu____9967 = lookup_datacon env lid in
        match uu____9967 with
        | (uu____9972,t) ->
            let uu____9974 =
              let uu____9975 = FStar_Syntax_Subst.compress t in
              uu____9975.FStar_Syntax_Syntax.n in
            (match uu____9974 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9979) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10010 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10010
                      FStar_Pervasives_Native.fst)
             | uu____10019 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10028 = lookup_qname env l in
      match uu____10028 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10049,uu____10050,uu____10051);
              FStar_Syntax_Syntax.sigrng = uu____10052;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10054;
              FStar_Syntax_Syntax.sigattrs = uu____10055;_},uu____10056),uu____10057)
          ->
          FStar_Util.for_some
            (fun uu___115_10110  ->
               match uu___115_10110 with
               | FStar_Syntax_Syntax.Projector uu____10111 -> true
               | uu____10116 -> false) quals
      | uu____10117 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10146 = lookup_qname env lid in
      match uu____10146 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10167,uu____10168,uu____10169,uu____10170,uu____10171,uu____10172);
              FStar_Syntax_Syntax.sigrng = uu____10173;
              FStar_Syntax_Syntax.sigquals = uu____10174;
              FStar_Syntax_Syntax.sigmeta = uu____10175;
              FStar_Syntax_Syntax.sigattrs = uu____10176;_},uu____10177),uu____10178)
          -> true
      | uu____10233 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10262 = lookup_qname env lid in
      match uu____10262 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10283,uu____10284,uu____10285,uu____10286,uu____10287,uu____10288);
              FStar_Syntax_Syntax.sigrng = uu____10289;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10291;
              FStar_Syntax_Syntax.sigattrs = uu____10292;_},uu____10293),uu____10294)
          ->
          FStar_Util.for_some
            (fun uu___116_10355  ->
               match uu___116_10355 with
               | FStar_Syntax_Syntax.RecordType uu____10356 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10365 -> true
               | uu____10374 -> false) quals
      | uu____10375 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10404 = lookup_qname env lid in
      match uu____10404 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____10425,uu____10426);
              FStar_Syntax_Syntax.sigrng = uu____10427;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10429;
              FStar_Syntax_Syntax.sigattrs = uu____10430;_},uu____10431),uu____10432)
          ->
          FStar_Util.for_some
            (fun uu___117_10489  ->
               match uu___117_10489 with
               | FStar_Syntax_Syntax.Action uu____10490 -> true
               | uu____10491 -> false) quals
      | uu____10492 -> false
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
      let uu____10524 =
        let uu____10525 = FStar_Syntax_Util.un_uinst head1 in
        uu____10525.FStar_Syntax_Syntax.n in
      match uu____10524 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10529 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10596 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10612) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10629 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10636 ->
                 FStar_Pervasives_Native.Some true
             | uu____10653 -> FStar_Pervasives_Native.Some false) in
      let uu____10654 =
        let uu____10657 = lookup_qname env lid in
        FStar_Util.bind_opt uu____10657 mapper in
      match uu____10654 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____10705 = lookup_qname env lid in
      match uu____10705 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10726,uu____10727,tps,uu____10729,uu____10730,uu____10731);
              FStar_Syntax_Syntax.sigrng = uu____10732;
              FStar_Syntax_Syntax.sigquals = uu____10733;
              FStar_Syntax_Syntax.sigmeta = uu____10734;
              FStar_Syntax_Syntax.sigattrs = uu____10735;_},uu____10736),uu____10737)
          -> FStar_List.length tps
      | uu____10800 ->
          let uu____10821 =
            let uu____10822 =
              let uu____10827 = name_not_found lid in
              (uu____10827, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____10822 in
          FStar_Exn.raise uu____10821
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
           (fun uu____10869  ->
              match uu____10869 with
              | (d,uu____10877) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____10890 = effect_decl_opt env l in
      match uu____10890 with
      | FStar_Pervasives_Native.None  ->
          let uu____10905 =
            let uu____10906 =
              let uu____10911 = name_not_found l in
              (uu____10911, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____10906 in
          FStar_Exn.raise uu____10905
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
            (let uu____10977 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11030  ->
                       match uu____11030 with
                       | (m1,m2,uu____11043,uu____11044,uu____11045) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____10977 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11062 =
                   let uu____11063 =
                     let uu____11068 =
                       let uu____11069 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11070 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11069
                         uu____11070 in
                     (uu____11068, (env.range)) in
                   FStar_Errors.Error uu____11063 in
                 FStar_Exn.raise uu____11062
             | FStar_Pervasives_Native.Some
                 (uu____11077,uu____11078,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11121 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11121)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11148 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11174  ->
                match uu____11174 with
                | (d,uu____11180) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11148 with
      | FStar_Pervasives_Native.None  ->
          let uu____11191 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11191
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11204 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11204 with
           | (uu____11215,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11225)::(wp,uu____11227)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11263 -> failwith "Impossible"))
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
                 let uu____11312 = get_range env in
                 let uu____11313 =
                   let uu____11316 =
                     let uu____11317 =
                       let uu____11332 =
                         let uu____11335 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11335] in
                       (null_wp, uu____11332) in
                     FStar_Syntax_Syntax.Tm_app uu____11317 in
                   FStar_Syntax_Syntax.mk uu____11316 in
                 uu____11313 FStar_Pervasives_Native.None uu____11312 in
               let uu____11341 =
                 let uu____11342 =
                   let uu____11351 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11351] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11342;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11341)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___128_11362 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___128_11362.order);
              joins = (uu___128_11362.joins)
            } in
          let uu___129_11371 = env in
          {
            solver = (uu___129_11371.solver);
            range = (uu___129_11371.range);
            curmodule = (uu___129_11371.curmodule);
            gamma = (uu___129_11371.gamma);
            gamma_cache = (uu___129_11371.gamma_cache);
            modules = (uu___129_11371.modules);
            expected_typ = (uu___129_11371.expected_typ);
            sigtab = (uu___129_11371.sigtab);
            is_pattern = (uu___129_11371.is_pattern);
            instantiate_imp = (uu___129_11371.instantiate_imp);
            effects;
            generalize = (uu___129_11371.generalize);
            letrecs = (uu___129_11371.letrecs);
            top_level = (uu___129_11371.top_level);
            check_uvars = (uu___129_11371.check_uvars);
            use_eq = (uu___129_11371.use_eq);
            is_iface = (uu___129_11371.is_iface);
            admit = (uu___129_11371.admit);
            lax = (uu___129_11371.lax);
            lax_universes = (uu___129_11371.lax_universes);
            failhard = (uu___129_11371.failhard);
            type_of = (uu___129_11371.type_of);
            universe_of = (uu___129_11371.universe_of);
            use_bv_sorts = (uu___129_11371.use_bv_sorts);
            qname_and_index = (uu___129_11371.qname_and_index);
            proof_ns = (uu___129_11371.proof_ns);
            synth = (uu___129_11371.synth);
            is_native_tactic = (uu___129_11371.is_native_tactic);
            identifier_info = (uu___129_11371.identifier_info)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____11388 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____11388 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____11478 = (e1.mlift).mlift_wp t wp in
                              let uu____11479 = l1 t wp e in
                              l2 t uu____11478 uu____11479))
                | uu____11480 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____11519 = inst_tscheme lift_t in
            match uu____11519 with
            | (uu____11526,lift_t1) ->
                let uu____11528 =
                  let uu____11531 =
                    let uu____11532 =
                      let uu____11547 =
                        let uu____11550 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11551 =
                          let uu____11554 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____11554] in
                        uu____11550 :: uu____11551 in
                      (lift_t1, uu____11547) in
                    FStar_Syntax_Syntax.Tm_app uu____11532 in
                  FStar_Syntax_Syntax.mk uu____11531 in
                uu____11528 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____11595 = inst_tscheme lift_t in
            match uu____11595 with
            | (uu____11602,lift_t1) ->
                let uu____11604 =
                  let uu____11607 =
                    let uu____11608 =
                      let uu____11623 =
                        let uu____11626 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11627 =
                          let uu____11630 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____11631 =
                            let uu____11634 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11634] in
                          uu____11630 :: uu____11631 in
                        uu____11626 :: uu____11627 in
                      (lift_t1, uu____11623) in
                    FStar_Syntax_Syntax.Tm_app uu____11608 in
                  FStar_Syntax_Syntax.mk uu____11607 in
                uu____11604 FStar_Pervasives_Native.None
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
              let uu____11672 =
                let uu____11673 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____11673
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____11672 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____11677 =
              let uu____11678 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____11678 in
            let uu____11679 =
              let uu____11680 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11698 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____11698) in
              FStar_Util.dflt "none" uu____11680 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11677
              uu____11679 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11724  ->
                    match uu____11724 with
                    | (e,uu____11732) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____11751 =
            match uu____11751 with
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
              let uu____11789 =
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
                                    (let uu____11810 =
                                       let uu____11819 =
                                         find_edge order1 (i, k) in
                                       let uu____11822 =
                                         find_edge order1 (k, j) in
                                       (uu____11819, uu____11822) in
                                     match uu____11810 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____11837 =
                                           compose_edges e1 e2 in
                                         [uu____11837]
                                     | uu____11838 -> []))))) in
              FStar_List.append order1 uu____11789 in
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
                   let uu____11867 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____11869 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____11869
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____11867
                   then
                     let uu____11874 =
                       let uu____11875 =
                         let uu____11880 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____11881 = get_range env in
                         (uu____11880, uu____11881) in
                       FStar_Errors.Error uu____11875 in
                     FStar_Exn.raise uu____11874
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
                                            let uu____12006 =
                                              let uu____12015 =
                                                find_edge order2 (i, k) in
                                              let uu____12018 =
                                                find_edge order2 (j, k) in
                                              (uu____12015, uu____12018) in
                                            match uu____12006 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12060,uu____12061)
                                                     ->
                                                     let uu____12068 =
                                                       let uu____12073 =
                                                         let uu____12074 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12074 in
                                                       let uu____12077 =
                                                         let uu____12078 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12078 in
                                                       (uu____12073,
                                                         uu____12077) in
                                                     (match uu____12068 with
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
                                            | uu____12113 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___130_12186 = env.effects in
              { decls = (uu___130_12186.decls); order = order2; joins } in
            let uu___131_12187 = env in
            {
              solver = (uu___131_12187.solver);
              range = (uu___131_12187.range);
              curmodule = (uu___131_12187.curmodule);
              gamma = (uu___131_12187.gamma);
              gamma_cache = (uu___131_12187.gamma_cache);
              modules = (uu___131_12187.modules);
              expected_typ = (uu___131_12187.expected_typ);
              sigtab = (uu___131_12187.sigtab);
              is_pattern = (uu___131_12187.is_pattern);
              instantiate_imp = (uu___131_12187.instantiate_imp);
              effects;
              generalize = (uu___131_12187.generalize);
              letrecs = (uu___131_12187.letrecs);
              top_level = (uu___131_12187.top_level);
              check_uvars = (uu___131_12187.check_uvars);
              use_eq = (uu___131_12187.use_eq);
              is_iface = (uu___131_12187.is_iface);
              admit = (uu___131_12187.admit);
              lax = (uu___131_12187.lax);
              lax_universes = (uu___131_12187.lax_universes);
              failhard = (uu___131_12187.failhard);
              type_of = (uu___131_12187.type_of);
              universe_of = (uu___131_12187.universe_of);
              use_bv_sorts = (uu___131_12187.use_bv_sorts);
              qname_and_index = (uu___131_12187.qname_and_index);
              proof_ns = (uu___131_12187.proof_ns);
              synth = (uu___131_12187.synth);
              is_native_tactic = (uu___131_12187.is_native_tactic);
              identifier_info = (uu___131_12187.identifier_info)
            }))
      | uu____12188 -> env
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
        | uu____12214 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12224 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12224 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12241 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12241 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12259 =
                     let uu____12260 =
                       let uu____12265 =
                         let uu____12266 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12271 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12278 =
                           let uu____12279 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12279 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12266 uu____12271 uu____12278 in
                       (uu____12265, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12260 in
                   FStar_Exn.raise uu____12259)
                else ();
                (let inst1 =
                   let uu____12284 =
                     let uu____12293 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12293 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12310  ->
                        fun uu____12311  ->
                          match (uu____12310, uu____12311) with
                          | ((x,uu____12333),(t,uu____12335)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12284 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12354 =
                     let uu___132_12355 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___132_12355.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___132_12355.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___132_12355.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___132_12355.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12354
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
          let uu____12380 =
            let uu____12389 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____12389 in
          match uu____12380 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12414 =
                only_reifiable &&
                  (let uu____12416 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____12416) in
              if uu____12414
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12432 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____12434 =
                       let uu____12447 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____12447) in
                     (match uu____12434 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____12493 =
                            let uu____12496 = get_range env in
                            let uu____12497 =
                              let uu____12500 =
                                let uu____12501 =
                                  let uu____12516 =
                                    let uu____12519 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____12519; wp] in
                                  (repr, uu____12516) in
                                FStar_Syntax_Syntax.Tm_app uu____12501 in
                              FStar_Syntax_Syntax.mk uu____12500 in
                            uu____12497 FStar_Pervasives_Native.None
                              uu____12496 in
                          FStar_Pervasives_Native.Some uu____12493))
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
          let uu____12571 =
            let uu____12572 =
              let uu____12577 =
                let uu____12578 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____12578 in
              let uu____12579 = get_range env in (uu____12577, uu____12579) in
            FStar_Errors.Error uu____12572 in
          FStar_Exn.raise uu____12571 in
        let uu____12580 = effect_repr_aux true env c u_c in
        match uu____12580 with
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
      | uu____12620 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____12629 =
        let uu____12630 = FStar_Syntax_Subst.compress t in
        uu____12630.FStar_Syntax_Syntax.n in
      match uu____12629 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12633,c) ->
          is_reifiable_comp env c
      | uu____12651 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12675)::uu____12676 -> x :: rest
        | (Binding_sig_inst uu____12685)::uu____12686 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12701 = push1 x rest1 in local :: uu____12701 in
      let uu___133_12704 = env in
      let uu____12705 = push1 s env.gamma in
      {
        solver = (uu___133_12704.solver);
        range = (uu___133_12704.range);
        curmodule = (uu___133_12704.curmodule);
        gamma = uu____12705;
        gamma_cache = (uu___133_12704.gamma_cache);
        modules = (uu___133_12704.modules);
        expected_typ = (uu___133_12704.expected_typ);
        sigtab = (uu___133_12704.sigtab);
        is_pattern = (uu___133_12704.is_pattern);
        instantiate_imp = (uu___133_12704.instantiate_imp);
        effects = (uu___133_12704.effects);
        generalize = (uu___133_12704.generalize);
        letrecs = (uu___133_12704.letrecs);
        top_level = (uu___133_12704.top_level);
        check_uvars = (uu___133_12704.check_uvars);
        use_eq = (uu___133_12704.use_eq);
        is_iface = (uu___133_12704.is_iface);
        admit = (uu___133_12704.admit);
        lax = (uu___133_12704.lax);
        lax_universes = (uu___133_12704.lax_universes);
        failhard = (uu___133_12704.failhard);
        type_of = (uu___133_12704.type_of);
        universe_of = (uu___133_12704.universe_of);
        use_bv_sorts = (uu___133_12704.use_bv_sorts);
        qname_and_index = (uu___133_12704.qname_and_index);
        proof_ns = (uu___133_12704.proof_ns);
        synth = (uu___133_12704.synth);
        is_native_tactic = (uu___133_12704.is_native_tactic);
        identifier_info = (uu___133_12704.identifier_info)
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
      let uu___134_12742 = env in
      {
        solver = (uu___134_12742.solver);
        range = (uu___134_12742.range);
        curmodule = (uu___134_12742.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___134_12742.gamma_cache);
        modules = (uu___134_12742.modules);
        expected_typ = (uu___134_12742.expected_typ);
        sigtab = (uu___134_12742.sigtab);
        is_pattern = (uu___134_12742.is_pattern);
        instantiate_imp = (uu___134_12742.instantiate_imp);
        effects = (uu___134_12742.effects);
        generalize = (uu___134_12742.generalize);
        letrecs = (uu___134_12742.letrecs);
        top_level = (uu___134_12742.top_level);
        check_uvars = (uu___134_12742.check_uvars);
        use_eq = (uu___134_12742.use_eq);
        is_iface = (uu___134_12742.is_iface);
        admit = (uu___134_12742.admit);
        lax = (uu___134_12742.lax);
        lax_universes = (uu___134_12742.lax_universes);
        failhard = (uu___134_12742.failhard);
        type_of = (uu___134_12742.type_of);
        universe_of = (uu___134_12742.universe_of);
        use_bv_sorts = (uu___134_12742.use_bv_sorts);
        qname_and_index = (uu___134_12742.qname_and_index);
        proof_ns = (uu___134_12742.proof_ns);
        synth = (uu___134_12742.synth);
        is_native_tactic = (uu___134_12742.is_native_tactic);
        identifier_info = (uu___134_12742.identifier_info)
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
            (let uu___135_12776 = env in
             {
               solver = (uu___135_12776.solver);
               range = (uu___135_12776.range);
               curmodule = (uu___135_12776.curmodule);
               gamma = rest;
               gamma_cache = (uu___135_12776.gamma_cache);
               modules = (uu___135_12776.modules);
               expected_typ = (uu___135_12776.expected_typ);
               sigtab = (uu___135_12776.sigtab);
               is_pattern = (uu___135_12776.is_pattern);
               instantiate_imp = (uu___135_12776.instantiate_imp);
               effects = (uu___135_12776.effects);
               generalize = (uu___135_12776.generalize);
               letrecs = (uu___135_12776.letrecs);
               top_level = (uu___135_12776.top_level);
               check_uvars = (uu___135_12776.check_uvars);
               use_eq = (uu___135_12776.use_eq);
               is_iface = (uu___135_12776.is_iface);
               admit = (uu___135_12776.admit);
               lax = (uu___135_12776.lax);
               lax_universes = (uu___135_12776.lax_universes);
               failhard = (uu___135_12776.failhard);
               type_of = (uu___135_12776.type_of);
               universe_of = (uu___135_12776.universe_of);
               use_bv_sorts = (uu___135_12776.use_bv_sorts);
               qname_and_index = (uu___135_12776.qname_and_index);
               proof_ns = (uu___135_12776.proof_ns);
               synth = (uu___135_12776.synth);
               is_native_tactic = (uu___135_12776.is_native_tactic);
               identifier_info = (uu___135_12776.identifier_info)
             }))
    | uu____12777 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12801  ->
             match uu____12801 with | (x,uu____12807) -> push_bv env1 x) env
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
            let uu___136_12837 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___136_12837.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___136_12837.FStar_Syntax_Syntax.index);
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
      (let uu___137_12872 = env in
       {
         solver = (uu___137_12872.solver);
         range = (uu___137_12872.range);
         curmodule = (uu___137_12872.curmodule);
         gamma = [];
         gamma_cache = (uu___137_12872.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___137_12872.sigtab);
         is_pattern = (uu___137_12872.is_pattern);
         instantiate_imp = (uu___137_12872.instantiate_imp);
         effects = (uu___137_12872.effects);
         generalize = (uu___137_12872.generalize);
         letrecs = (uu___137_12872.letrecs);
         top_level = (uu___137_12872.top_level);
         check_uvars = (uu___137_12872.check_uvars);
         use_eq = (uu___137_12872.use_eq);
         is_iface = (uu___137_12872.is_iface);
         admit = (uu___137_12872.admit);
         lax = (uu___137_12872.lax);
         lax_universes = (uu___137_12872.lax_universes);
         failhard = (uu___137_12872.failhard);
         type_of = (uu___137_12872.type_of);
         universe_of = (uu___137_12872.universe_of);
         use_bv_sorts = (uu___137_12872.use_bv_sorts);
         qname_and_index = (uu___137_12872.qname_and_index);
         proof_ns = (uu___137_12872.proof_ns);
         synth = (uu___137_12872.synth);
         is_native_tactic = (uu___137_12872.is_native_tactic);
         identifier_info = (uu___137_12872.identifier_info)
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
        let uu____12909 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____12909 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____12937 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____12937)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___138_12952 = env in
      {
        solver = (uu___138_12952.solver);
        range = (uu___138_12952.range);
        curmodule = (uu___138_12952.curmodule);
        gamma = (uu___138_12952.gamma);
        gamma_cache = (uu___138_12952.gamma_cache);
        modules = (uu___138_12952.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___138_12952.sigtab);
        is_pattern = (uu___138_12952.is_pattern);
        instantiate_imp = (uu___138_12952.instantiate_imp);
        effects = (uu___138_12952.effects);
        generalize = (uu___138_12952.generalize);
        letrecs = (uu___138_12952.letrecs);
        top_level = (uu___138_12952.top_level);
        check_uvars = (uu___138_12952.check_uvars);
        use_eq = false;
        is_iface = (uu___138_12952.is_iface);
        admit = (uu___138_12952.admit);
        lax = (uu___138_12952.lax);
        lax_universes = (uu___138_12952.lax_universes);
        failhard = (uu___138_12952.failhard);
        type_of = (uu___138_12952.type_of);
        universe_of = (uu___138_12952.universe_of);
        use_bv_sorts = (uu___138_12952.use_bv_sorts);
        qname_and_index = (uu___138_12952.qname_and_index);
        proof_ns = (uu___138_12952.proof_ns);
        synth = (uu___138_12952.synth);
        is_native_tactic = (uu___138_12952.is_native_tactic);
        identifier_info = (uu___138_12952.identifier_info)
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
    let uu____12978 = expected_typ env_ in
    ((let uu___139_12984 = env_ in
      {
        solver = (uu___139_12984.solver);
        range = (uu___139_12984.range);
        curmodule = (uu___139_12984.curmodule);
        gamma = (uu___139_12984.gamma);
        gamma_cache = (uu___139_12984.gamma_cache);
        modules = (uu___139_12984.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___139_12984.sigtab);
        is_pattern = (uu___139_12984.is_pattern);
        instantiate_imp = (uu___139_12984.instantiate_imp);
        effects = (uu___139_12984.effects);
        generalize = (uu___139_12984.generalize);
        letrecs = (uu___139_12984.letrecs);
        top_level = (uu___139_12984.top_level);
        check_uvars = (uu___139_12984.check_uvars);
        use_eq = false;
        is_iface = (uu___139_12984.is_iface);
        admit = (uu___139_12984.admit);
        lax = (uu___139_12984.lax);
        lax_universes = (uu___139_12984.lax_universes);
        failhard = (uu___139_12984.failhard);
        type_of = (uu___139_12984.type_of);
        universe_of = (uu___139_12984.universe_of);
        use_bv_sorts = (uu___139_12984.use_bv_sorts);
        qname_and_index = (uu___139_12984.qname_and_index);
        proof_ns = (uu___139_12984.proof_ns);
        synth = (uu___139_12984.synth);
        is_native_tactic = (uu___139_12984.is_native_tactic);
        identifier_info = (uu___139_12984.identifier_info)
      }), uu____12978)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____12999 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___118_13009  ->
                    match uu___118_13009 with
                    | Binding_sig (uu____13012,se) -> [se]
                    | uu____13018 -> [])) in
          FStar_All.pipe_right uu____12999 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___140_13025 = env in
       {
         solver = (uu___140_13025.solver);
         range = (uu___140_13025.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___140_13025.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___140_13025.expected_typ);
         sigtab = (uu___140_13025.sigtab);
         is_pattern = (uu___140_13025.is_pattern);
         instantiate_imp = (uu___140_13025.instantiate_imp);
         effects = (uu___140_13025.effects);
         generalize = (uu___140_13025.generalize);
         letrecs = (uu___140_13025.letrecs);
         top_level = (uu___140_13025.top_level);
         check_uvars = (uu___140_13025.check_uvars);
         use_eq = (uu___140_13025.use_eq);
         is_iface = (uu___140_13025.is_iface);
         admit = (uu___140_13025.admit);
         lax = (uu___140_13025.lax);
         lax_universes = (uu___140_13025.lax_universes);
         failhard = (uu___140_13025.failhard);
         type_of = (uu___140_13025.type_of);
         universe_of = (uu___140_13025.universe_of);
         use_bv_sorts = (uu___140_13025.use_bv_sorts);
         qname_and_index = (uu___140_13025.qname_and_index);
         proof_ns = (uu___140_13025.proof_ns);
         synth = (uu___140_13025.synth);
         is_native_tactic = (uu___140_13025.is_native_tactic);
         identifier_info = (uu___140_13025.identifier_info)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13107)::tl1 -> aux out tl1
      | (Binding_lid (uu____13111,(uu____13112,t)))::tl1 ->
          let uu____13127 =
            let uu____13134 = FStar_Syntax_Free.uvars t in
            ext out uu____13134 in
          aux uu____13127 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13141;
            FStar_Syntax_Syntax.index = uu____13142;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13149 =
            let uu____13156 = FStar_Syntax_Free.uvars t in
            ext out uu____13156 in
          aux uu____13149 tl1
      | (Binding_sig uu____13163)::uu____13164 -> out
      | (Binding_sig_inst uu____13173)::uu____13174 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13230)::tl1 -> aux out tl1
      | (Binding_univ uu____13242)::tl1 -> aux out tl1
      | (Binding_lid (uu____13246,(uu____13247,t)))::tl1 ->
          let uu____13262 =
            let uu____13265 = FStar_Syntax_Free.univs t in
            ext out uu____13265 in
          aux uu____13262 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13268;
            FStar_Syntax_Syntax.index = uu____13269;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13276 =
            let uu____13279 = FStar_Syntax_Free.univs t in
            ext out uu____13279 in
          aux uu____13276 tl1
      | (Binding_sig uu____13282)::uu____13283 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13337)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13353 = FStar_Util.fifo_set_add uname out in
          aux uu____13353 tl1
      | (Binding_lid (uu____13356,(uu____13357,t)))::tl1 ->
          let uu____13372 =
            let uu____13375 = FStar_Syntax_Free.univnames t in
            ext out uu____13375 in
          aux uu____13372 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13378;
            FStar_Syntax_Syntax.index = uu____13379;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13386 =
            let uu____13389 = FStar_Syntax_Free.univnames t in
            ext out uu____13389 in
          aux uu____13386 tl1
      | (Binding_sig uu____13392)::uu____13393 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___119_13418  ->
            match uu___119_13418 with
            | Binding_var x -> [x]
            | Binding_lid uu____13422 -> []
            | Binding_sig uu____13427 -> []
            | Binding_univ uu____13434 -> []
            | Binding_sig_inst uu____13435 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____13452 =
      let uu____13455 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____13455
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____13452 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____13480 =
      let uu____13481 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___120_13491  ->
                match uu___120_13491 with
                | Binding_var x ->
                    let uu____13493 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____13493
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13496) ->
                    let uu____13497 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____13497
                | Binding_sig (ls,uu____13499) ->
                    let uu____13504 =
                      let uu____13505 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13505
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____13504
                | Binding_sig_inst (ls,uu____13515,uu____13516) ->
                    let uu____13521 =
                      let uu____13522 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13522
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____13521)) in
      FStar_All.pipe_right uu____13481 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____13480 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____13541 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____13541
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13569  ->
                 fun uu____13570  ->
                   match (uu____13569, uu____13570) with
                   | ((b1,uu____13588),(b2,uu____13590)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___121_13652  ->
             match uu___121_13652 with
             | Binding_sig (lids,uu____13658) -> FStar_List.append lids keys
             | uu____13663 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13669  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13705) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13724,uu____13725) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13762 = list_prefix p path1 in
            if uu____13762 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13776 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13776
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___141_13806 = e in
            {
              solver = (uu___141_13806.solver);
              range = (uu___141_13806.range);
              curmodule = (uu___141_13806.curmodule);
              gamma = (uu___141_13806.gamma);
              gamma_cache = (uu___141_13806.gamma_cache);
              modules = (uu___141_13806.modules);
              expected_typ = (uu___141_13806.expected_typ);
              sigtab = (uu___141_13806.sigtab);
              is_pattern = (uu___141_13806.is_pattern);
              instantiate_imp = (uu___141_13806.instantiate_imp);
              effects = (uu___141_13806.effects);
              generalize = (uu___141_13806.generalize);
              letrecs = (uu___141_13806.letrecs);
              top_level = (uu___141_13806.top_level);
              check_uvars = (uu___141_13806.check_uvars);
              use_eq = (uu___141_13806.use_eq);
              is_iface = (uu___141_13806.is_iface);
              admit = (uu___141_13806.admit);
              lax = (uu___141_13806.lax);
              lax_universes = (uu___141_13806.lax_universes);
              failhard = (uu___141_13806.failhard);
              type_of = (uu___141_13806.type_of);
              universe_of = (uu___141_13806.universe_of);
              use_bv_sorts = (uu___141_13806.use_bv_sorts);
              qname_and_index = (uu___141_13806.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___141_13806.synth);
              is_native_tactic = (uu___141_13806.is_native_tactic);
              identifier_info = (uu___141_13806.identifier_info)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___142_13833 = e in
    {
      solver = (uu___142_13833.solver);
      range = (uu___142_13833.range);
      curmodule = (uu___142_13833.curmodule);
      gamma = (uu___142_13833.gamma);
      gamma_cache = (uu___142_13833.gamma_cache);
      modules = (uu___142_13833.modules);
      expected_typ = (uu___142_13833.expected_typ);
      sigtab = (uu___142_13833.sigtab);
      is_pattern = (uu___142_13833.is_pattern);
      instantiate_imp = (uu___142_13833.instantiate_imp);
      effects = (uu___142_13833.effects);
      generalize = (uu___142_13833.generalize);
      letrecs = (uu___142_13833.letrecs);
      top_level = (uu___142_13833.top_level);
      check_uvars = (uu___142_13833.check_uvars);
      use_eq = (uu___142_13833.use_eq);
      is_iface = (uu___142_13833.is_iface);
      admit = (uu___142_13833.admit);
      lax = (uu___142_13833.lax);
      lax_universes = (uu___142_13833.lax_universes);
      failhard = (uu___142_13833.failhard);
      type_of = (uu___142_13833.type_of);
      universe_of = (uu___142_13833.universe_of);
      use_bv_sorts = (uu___142_13833.use_bv_sorts);
      qname_and_index = (uu___142_13833.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___142_13833.synth);
      is_native_tactic = (uu___142_13833.is_native_tactic);
      identifier_info = (uu___142_13833.identifier_info)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____13848::rest ->
        let uu___143_13852 = e in
        {
          solver = (uu___143_13852.solver);
          range = (uu___143_13852.range);
          curmodule = (uu___143_13852.curmodule);
          gamma = (uu___143_13852.gamma);
          gamma_cache = (uu___143_13852.gamma_cache);
          modules = (uu___143_13852.modules);
          expected_typ = (uu___143_13852.expected_typ);
          sigtab = (uu___143_13852.sigtab);
          is_pattern = (uu___143_13852.is_pattern);
          instantiate_imp = (uu___143_13852.instantiate_imp);
          effects = (uu___143_13852.effects);
          generalize = (uu___143_13852.generalize);
          letrecs = (uu___143_13852.letrecs);
          top_level = (uu___143_13852.top_level);
          check_uvars = (uu___143_13852.check_uvars);
          use_eq = (uu___143_13852.use_eq);
          is_iface = (uu___143_13852.is_iface);
          admit = (uu___143_13852.admit);
          lax = (uu___143_13852.lax);
          lax_universes = (uu___143_13852.lax_universes);
          failhard = (uu___143_13852.failhard);
          type_of = (uu___143_13852.type_of);
          universe_of = (uu___143_13852.universe_of);
          use_bv_sorts = (uu___143_13852.use_bv_sorts);
          qname_and_index = (uu___143_13852.qname_and_index);
          proof_ns = rest;
          synth = (uu___143_13852.synth);
          is_native_tactic = (uu___143_13852.is_native_tactic);
          identifier_info = (uu___143_13852.identifier_info)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___144_13865 = e in
      {
        solver = (uu___144_13865.solver);
        range = (uu___144_13865.range);
        curmodule = (uu___144_13865.curmodule);
        gamma = (uu___144_13865.gamma);
        gamma_cache = (uu___144_13865.gamma_cache);
        modules = (uu___144_13865.modules);
        expected_typ = (uu___144_13865.expected_typ);
        sigtab = (uu___144_13865.sigtab);
        is_pattern = (uu___144_13865.is_pattern);
        instantiate_imp = (uu___144_13865.instantiate_imp);
        effects = (uu___144_13865.effects);
        generalize = (uu___144_13865.generalize);
        letrecs = (uu___144_13865.letrecs);
        top_level = (uu___144_13865.top_level);
        check_uvars = (uu___144_13865.check_uvars);
        use_eq = (uu___144_13865.use_eq);
        is_iface = (uu___144_13865.is_iface);
        admit = (uu___144_13865.admit);
        lax = (uu___144_13865.lax);
        lax_universes = (uu___144_13865.lax_universes);
        failhard = (uu___144_13865.failhard);
        type_of = (uu___144_13865.type_of);
        universe_of = (uu___144_13865.universe_of);
        use_bv_sorts = (uu___144_13865.use_bv_sorts);
        qname_and_index = (uu___144_13865.qname_and_index);
        proof_ns = ns;
        synth = (uu___144_13865.synth);
        is_native_tactic = (uu___144_13865.is_native_tactic);
        identifier_info = (uu___144_13865.identifier_info)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____13894 =
        FStar_List.map
          (fun fpns  ->
             let uu____13916 =
               let uu____13917 =
                 let uu____13918 =
                   FStar_List.map
                     (fun uu____13930  ->
                        match uu____13930 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____13918 in
               Prims.strcat uu____13917 "]" in
             Prims.strcat "[" uu____13916) pns in
      FStar_String.concat ";" uu____13894 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____13946  -> ());
    push = (fun uu____13948  -> ());
    pop = (fun uu____13950  -> ());
    mark = (fun uu____13952  -> ());
    reset_mark = (fun uu____13954  -> ());
    commit_mark = (fun uu____13956  -> ());
    encode_modul = (fun uu____13959  -> fun uu____13960  -> ());
    encode_sig = (fun uu____13963  -> fun uu____13964  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____13970 =
             let uu____13977 = FStar_Options.peek () in (e, g, uu____13977) in
           [uu____13970]);
    solve = (fun uu____13993  -> fun uu____13994  -> fun uu____13995  -> ());
    is_trivial = (fun uu____14002  -> fun uu____14003  -> false);
    finish = (fun uu____14005  -> ());
    refresh = (fun uu____14007  -> ())
  }