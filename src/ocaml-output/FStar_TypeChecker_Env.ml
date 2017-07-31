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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;_} ->
        __fname__lax_universes
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
      | (NoDelta ,uu____4407) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4408,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4409,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4410 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4419 . Prims.unit -> 'Auu____4419 FStar_Util.smap =
  fun uu____4425  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4430 . Prims.unit -> 'Auu____4430 FStar_Util.smap =
  fun uu____4436  -> FStar_Util.smap_create (Prims.parse_int "100")
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
          let uu____4485 = new_gamma_cache () in
          let uu____4488 = new_sigtab () in
          let uu____4491 =
            let uu____4492 = FStar_Options.using_facts_from () in
            match uu____4492 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____4502 =
                  let uu____4511 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____4511 [([], false)] in
                [uu____4502]
            | FStar_Pervasives_Native.None  -> [[]] in
          let uu____4584 =
            FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____4485;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____4488;
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
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = FStar_Pervasives_Native.None;
            proof_ns = uu____4491;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____4618  -> false);
            identifier_info = uu____4584
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
  fun uu____4689  ->
    let uu____4690 = FStar_ST.op_Bang query_indices in
    match uu____4690 with
    | [] -> failwith "Empty query indices!"
    | uu____4747 ->
        let uu____4756 =
          let uu____4765 =
            let uu____4772 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____4772 in
          let uu____4829 = FStar_ST.op_Bang query_indices in uu____4765 ::
            uu____4829 in
        FStar_ST.op_Colon_Equals query_indices uu____4756
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____4931  ->
    let uu____4932 = FStar_ST.op_Bang query_indices in
    match uu____4932 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5060  ->
    match uu____5060 with
    | (l,n1) ->
        let uu____5067 = FStar_ST.op_Bang query_indices in
        (match uu____5067 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5192 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5210  ->
    let uu____5211 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5211
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____5271  ->
    let uu____5272 = FStar_ST.op_Bang query_indices in
    match uu____5272 with
    | hd1::uu____5324::tl1 ->
        FStar_ST.op_Colon_Equals query_indices (hd1 :: tl1)
    | uu____5406 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5433 =
       let uu____5436 = FStar_ST.op_Bang stack in env :: uu____5436 in
     FStar_ST.op_Colon_Equals stack uu____5433);
    (let uu___121_5475 = env in
     let uu____5476 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5479 = FStar_Util.smap_copy (sigtab env) in
     let uu____5482 =
       let uu____5485 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5485 in
     {
       solver = (uu___121_5475.solver);
       range = (uu___121_5475.range);
       curmodule = (uu___121_5475.curmodule);
       gamma = (uu___121_5475.gamma);
       gamma_cache = uu____5476;
       modules = (uu___121_5475.modules);
       expected_typ = (uu___121_5475.expected_typ);
       sigtab = uu____5479;
       is_pattern = (uu___121_5475.is_pattern);
       instantiate_imp = (uu___121_5475.instantiate_imp);
       effects = (uu___121_5475.effects);
       generalize = (uu___121_5475.generalize);
       letrecs = (uu___121_5475.letrecs);
       top_level = (uu___121_5475.top_level);
       check_uvars = (uu___121_5475.check_uvars);
       use_eq = (uu___121_5475.use_eq);
       is_iface = (uu___121_5475.is_iface);
       admit = (uu___121_5475.admit);
       lax = (uu___121_5475.lax);
       lax_universes = (uu___121_5475.lax_universes);
       type_of = (uu___121_5475.type_of);
       universe_of = (uu___121_5475.universe_of);
       use_bv_sorts = (uu___121_5475.use_bv_sorts);
       qname_and_index = (uu___121_5475.qname_and_index);
       proof_ns = (uu___121_5475.proof_ns);
       synth = (uu___121_5475.synth);
       is_native_tactic = (uu___121_5475.is_native_tactic);
       identifier_info = uu____5482
     })
let pop_stack: Prims.unit -> env =
  fun uu____5513  ->
    let uu____5514 = FStar_ST.op_Bang stack in
    match uu____5514 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____5558 -> failwith "Impossible: Too many pops"
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
    (let uu____5598 = pop_stack () in ());
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
        let uu____5626 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____5652  ->
                  match uu____5652 with
                  | (m,uu____5658) -> FStar_Ident.lid_equals l m)) in
        (match uu____5626 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___122_5665 = env in
               {
                 solver = (uu___122_5665.solver);
                 range = (uu___122_5665.range);
                 curmodule = (uu___122_5665.curmodule);
                 gamma = (uu___122_5665.gamma);
                 gamma_cache = (uu___122_5665.gamma_cache);
                 modules = (uu___122_5665.modules);
                 expected_typ = (uu___122_5665.expected_typ);
                 sigtab = (uu___122_5665.sigtab);
                 is_pattern = (uu___122_5665.is_pattern);
                 instantiate_imp = (uu___122_5665.instantiate_imp);
                 effects = (uu___122_5665.effects);
                 generalize = (uu___122_5665.generalize);
                 letrecs = (uu___122_5665.letrecs);
                 top_level = (uu___122_5665.top_level);
                 check_uvars = (uu___122_5665.check_uvars);
                 use_eq = (uu___122_5665.use_eq);
                 is_iface = (uu___122_5665.is_iface);
                 admit = (uu___122_5665.admit);
                 lax = (uu___122_5665.lax);
                 lax_universes = (uu___122_5665.lax_universes);
                 type_of = (uu___122_5665.type_of);
                 universe_of = (uu___122_5665.universe_of);
                 use_bv_sorts = (uu___122_5665.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___122_5665.proof_ns);
                 synth = (uu___122_5665.synth);
                 is_native_tactic = (uu___122_5665.is_native_tactic);
                 identifier_info = (uu___122_5665.identifier_info)
               }))
         | FStar_Pervasives_Native.Some (uu____5670,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___123_5678 = env in
               {
                 solver = (uu___123_5678.solver);
                 range = (uu___123_5678.range);
                 curmodule = (uu___123_5678.curmodule);
                 gamma = (uu___123_5678.gamma);
                 gamma_cache = (uu___123_5678.gamma_cache);
                 modules = (uu___123_5678.modules);
                 expected_typ = (uu___123_5678.expected_typ);
                 sigtab = (uu___123_5678.sigtab);
                 is_pattern = (uu___123_5678.is_pattern);
                 instantiate_imp = (uu___123_5678.instantiate_imp);
                 effects = (uu___123_5678.effects);
                 generalize = (uu___123_5678.generalize);
                 letrecs = (uu___123_5678.letrecs);
                 top_level = (uu___123_5678.top_level);
                 check_uvars = (uu___123_5678.check_uvars);
                 use_eq = (uu___123_5678.use_eq);
                 is_iface = (uu___123_5678.is_iface);
                 admit = (uu___123_5678.admit);
                 lax = (uu___123_5678.lax);
                 lax_universes = (uu___123_5678.lax_universes);
                 type_of = (uu___123_5678.type_of);
                 universe_of = (uu___123_5678.universe_of);
                 use_bv_sorts = (uu___123_5678.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___123_5678.proof_ns);
                 synth = (uu___123_5678.synth);
                 is_native_tactic = (uu___123_5678.is_native_tactic);
                 identifier_info = (uu___123_5678.identifier_info)
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
        (let uu___124_5700 = e in
         {
           solver = (uu___124_5700.solver);
           range = r;
           curmodule = (uu___124_5700.curmodule);
           gamma = (uu___124_5700.gamma);
           gamma_cache = (uu___124_5700.gamma_cache);
           modules = (uu___124_5700.modules);
           expected_typ = (uu___124_5700.expected_typ);
           sigtab = (uu___124_5700.sigtab);
           is_pattern = (uu___124_5700.is_pattern);
           instantiate_imp = (uu___124_5700.instantiate_imp);
           effects = (uu___124_5700.effects);
           generalize = (uu___124_5700.generalize);
           letrecs = (uu___124_5700.letrecs);
           top_level = (uu___124_5700.top_level);
           check_uvars = (uu___124_5700.check_uvars);
           use_eq = (uu___124_5700.use_eq);
           is_iface = (uu___124_5700.is_iface);
           admit = (uu___124_5700.admit);
           lax = (uu___124_5700.lax);
           lax_universes = (uu___124_5700.lax_universes);
           type_of = (uu___124_5700.type_of);
           universe_of = (uu___124_5700.universe_of);
           use_bv_sorts = (uu___124_5700.use_bv_sorts);
           qname_and_index = (uu___124_5700.qname_and_index);
           proof_ns = (uu___124_5700.proof_ns);
           synth = (uu___124_5700.synth);
           is_native_tactic = (uu___124_5700.is_native_tactic);
           identifier_info = (uu___124_5700.identifier_info)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____5713 =
        let uu____5714 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____5714 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5713
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____5747 =
          let uu____5748 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____5748 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5747
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____5781 =
          let uu____5782 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____5782 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____5781
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____5816 =
        let uu____5817 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____5817 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____5816
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___125_5856 = env in
      {
        solver = (uu___125_5856.solver);
        range = (uu___125_5856.range);
        curmodule = lid;
        gamma = (uu___125_5856.gamma);
        gamma_cache = (uu___125_5856.gamma_cache);
        modules = (uu___125_5856.modules);
        expected_typ = (uu___125_5856.expected_typ);
        sigtab = (uu___125_5856.sigtab);
        is_pattern = (uu___125_5856.is_pattern);
        instantiate_imp = (uu___125_5856.instantiate_imp);
        effects = (uu___125_5856.effects);
        generalize = (uu___125_5856.generalize);
        letrecs = (uu___125_5856.letrecs);
        top_level = (uu___125_5856.top_level);
        check_uvars = (uu___125_5856.check_uvars);
        use_eq = (uu___125_5856.use_eq);
        is_iface = (uu___125_5856.is_iface);
        admit = (uu___125_5856.admit);
        lax = (uu___125_5856.lax);
        lax_universes = (uu___125_5856.lax_universes);
        type_of = (uu___125_5856.type_of);
        universe_of = (uu___125_5856.universe_of);
        use_bv_sorts = (uu___125_5856.use_bv_sorts);
        qname_and_index = (uu___125_5856.qname_and_index);
        proof_ns = (uu___125_5856.proof_ns);
        synth = (uu___125_5856.synth);
        is_native_tactic = (uu___125_5856.is_native_tactic);
        identifier_info = (uu___125_5856.identifier_info)
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
    let uu____5887 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____5887
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____5891  ->
    let uu____5892 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____5892
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
      | ((formals,t),uu____5932) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____5956 = FStar_Syntax_Subst.subst vs t in (us, uu____5956)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___109_5970  ->
    match uu___109_5970 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____5994  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6009 = inst_tscheme t in
      match uu____6009 with
      | (us,t1) ->
          let uu____6020 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6020)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6036  ->
          match uu____6036 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6051 =
                         let uu____6052 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6053 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6054 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6055 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6052 uu____6053 uu____6054 uu____6055 in
                       failwith uu____6051)
                    else ();
                    (let uu____6057 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6057))
               | uu____6064 ->
                   let uu____6065 =
                     let uu____6066 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6066 in
                   failwith uu____6065)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6071 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6076 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6081 -> false
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
             | ([],uu____6117) -> Maybe
             | (uu____6124,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6143 -> No in
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
          let uu____6250 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____6250 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___110_6295  ->
                   match uu___110_6295 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____6338 =
                           let uu____6357 =
                             let uu____6372 = inst_tscheme t in
                             FStar_Util.Inl uu____6372 in
                           (uu____6357, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____6338
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6438,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6440);
                                     FStar_Syntax_Syntax.sigrng = uu____6441;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6442;
                                     FStar_Syntax_Syntax.sigmeta = uu____6443;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6444;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6464 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6464
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____6510 ->
                             FStar_Pervasives_Native.Some t
                         | uu____6517 -> cache t in
                       let uu____6518 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6518 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____6593 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6593 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____6679 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____6759 = find_in_sigtab env lid in
         match uu____6759 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6858) ->
          add_sigelts env ses
      | uu____6867 ->
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
            | uu____6881 -> ()))
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
        (fun uu___111_6910  ->
           match uu___111_6910 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____6928 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____6963,lb::[]),uu____6965) ->
          let uu____6978 =
            let uu____6987 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____6996 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____6987, uu____6996) in
          FStar_Pervasives_Native.Some uu____6978
      | FStar_Syntax_Syntax.Sig_let ((uu____7009,lbs),uu____7011) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7047 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7059 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7059
                   then
                     let uu____7070 =
                       let uu____7079 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7088 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7079, uu____7088) in
                     FStar_Pervasives_Native.Some uu____7070
                   else FStar_Pervasives_Native.None)
      | uu____7110 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7144 =
          let uu____7153 =
            let uu____7158 =
              let uu____7159 =
                let uu____7162 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7162 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7159) in
            inst_tscheme uu____7158 in
          (uu____7153, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7144
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7182,uu____7183) ->
        let uu____7188 =
          let uu____7197 =
            let uu____7202 =
              let uu____7203 =
                let uu____7206 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____7206 in
              (us, uu____7203) in
            inst_tscheme uu____7202 in
          (uu____7197, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7188
    | uu____7223 -> FStar_Pervasives_Native.None
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
      let mapper uu____7283 =
        match uu____7283 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____7379,uvs,t,uu____7382,uu____7383,uu____7384);
                    FStar_Syntax_Syntax.sigrng = uu____7385;
                    FStar_Syntax_Syntax.sigquals = uu____7386;
                    FStar_Syntax_Syntax.sigmeta = uu____7387;
                    FStar_Syntax_Syntax.sigattrs = uu____7388;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7409 =
                   let uu____7418 = inst_tscheme (uvs, t) in
                   (uu____7418, rng) in
                 FStar_Pervasives_Native.Some uu____7409
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7438;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7440;
                    FStar_Syntax_Syntax.sigattrs = uu____7441;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7458 =
                   let uu____7459 = in_cur_mod env l in uu____7459 = Yes in
                 if uu____7458
                 then
                   let uu____7470 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7470
                    then
                      let uu____7483 =
                        let uu____7492 = inst_tscheme (uvs, t) in
                        (uu____7492, rng) in
                      FStar_Pervasives_Native.Some uu____7483
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____7519 =
                      let uu____7528 = inst_tscheme (uvs, t) in
                      (uu____7528, rng) in
                    FStar_Pervasives_Native.Some uu____7519)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7549,uu____7550);
                    FStar_Syntax_Syntax.sigrng = uu____7551;
                    FStar_Syntax_Syntax.sigquals = uu____7552;
                    FStar_Syntax_Syntax.sigmeta = uu____7553;
                    FStar_Syntax_Syntax.sigattrs = uu____7554;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____7593 =
                        let uu____7602 = inst_tscheme (uvs, k) in
                        (uu____7602, rng) in
                      FStar_Pervasives_Native.Some uu____7593
                  | uu____7619 ->
                      let uu____7620 =
                        let uu____7629 =
                          let uu____7634 =
                            let uu____7635 =
                              let uu____7638 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7638 in
                            (uvs, uu____7635) in
                          inst_tscheme uu____7634 in
                        (uu____7629, rng) in
                      FStar_Pervasives_Native.Some uu____7620)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7659,uu____7660);
                    FStar_Syntax_Syntax.sigrng = uu____7661;
                    FStar_Syntax_Syntax.sigquals = uu____7662;
                    FStar_Syntax_Syntax.sigmeta = uu____7663;
                    FStar_Syntax_Syntax.sigattrs = uu____7664;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____7704 =
                        let uu____7713 = inst_tscheme_with (uvs, k) us in
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
                          inst_tscheme_with uu____7745 us in
                        (uu____7740, rng) in
                      FStar_Pervasives_Native.Some uu____7731)
             | FStar_Util.Inr se ->
                 let uu____7783 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____7804;
                        FStar_Syntax_Syntax.sigrng = uu____7805;
                        FStar_Syntax_Syntax.sigquals = uu____7806;
                        FStar_Syntax_Syntax.sigmeta = uu____7807;
                        FStar_Syntax_Syntax.sigattrs = uu____7808;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____7823 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____7783
                   (FStar_Util.map_option
                      (fun uu____7871  ->
                         match uu____7871 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____7902 =
        let uu____7913 = lookup_qname env lid in
        FStar_Util.bind_opt uu____7913 mapper in
      match uu____7902 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___126_8006 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___126_8006.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___126_8006.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8033 = lookup_qname env l in
      match uu____8033 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8072 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8122 = try_lookup_bv env bv in
      match uu____8122 with
      | FStar_Pervasives_Native.None  ->
          let uu____8137 =
            let uu____8138 =
              let uu____8143 = variable_not_found bv in (uu____8143, bvr) in
            FStar_Errors.Error uu____8138 in
          FStar_Exn.raise uu____8137
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8154 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8155 = FStar_Range.set_use_range r bvr in
          (uu____8154, uu____8155)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8174 = try_lookup_lid_aux env l in
      match uu____8174 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____8240 =
            let uu____8249 =
              let uu____8254 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____8254) in
            (uu____8249, r1) in
          FStar_Pervasives_Native.Some uu____8240
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____8283 = try_lookup_lid env l in
      match uu____8283 with
      | FStar_Pervasives_Native.None  ->
          let uu____8310 =
            let uu____8311 =
              let uu____8316 = name_not_found l in
              (uu____8316, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____8311 in
          FStar_Exn.raise uu____8310
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___112_8354  ->
              match uu___112_8354 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____8356 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____8373 = lookup_qname env lid in
      match uu____8373 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8402,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8405;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8407;
              FStar_Syntax_Syntax.sigattrs = uu____8408;_},FStar_Pervasives_Native.None
            ),uu____8409)
          ->
          let uu____8458 =
            let uu____8469 =
              let uu____8474 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8474) in
            (uu____8469, q) in
          FStar_Pervasives_Native.Some uu____8458
      | uu____8491 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8530 = lookup_qname env lid in
      match uu____8530 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8555,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8558;
              FStar_Syntax_Syntax.sigquals = uu____8559;
              FStar_Syntax_Syntax.sigmeta = uu____8560;
              FStar_Syntax_Syntax.sigattrs = uu____8561;_},FStar_Pervasives_Native.None
            ),uu____8562)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8611 ->
          let uu____8632 =
            let uu____8633 =
              let uu____8638 = name_not_found lid in
              (uu____8638, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8633 in
          FStar_Exn.raise uu____8632
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8655 = lookup_qname env lid in
      match uu____8655 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8680,uvs,t,uu____8683,uu____8684,uu____8685);
              FStar_Syntax_Syntax.sigrng = uu____8686;
              FStar_Syntax_Syntax.sigquals = uu____8687;
              FStar_Syntax_Syntax.sigmeta = uu____8688;
              FStar_Syntax_Syntax.sigattrs = uu____8689;_},FStar_Pervasives_Native.None
            ),uu____8690)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8743 ->
          let uu____8764 =
            let uu____8765 =
              let uu____8770 = name_not_found lid in
              (uu____8770, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8765 in
          FStar_Exn.raise uu____8764
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8789 = lookup_qname env lid in
      match uu____8789 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____8816,uu____8817,uu____8818,uu____8819,uu____8820,dcs);
              FStar_Syntax_Syntax.sigrng = uu____8822;
              FStar_Syntax_Syntax.sigquals = uu____8823;
              FStar_Syntax_Syntax.sigmeta = uu____8824;
              FStar_Syntax_Syntax.sigattrs = uu____8825;_},uu____8826),uu____8827)
          -> (true, dcs)
      | uu____8888 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____8919 = lookup_qname env lid in
      match uu____8919 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8940,uu____8941,uu____8942,l,uu____8944,uu____8945);
              FStar_Syntax_Syntax.sigrng = uu____8946;
              FStar_Syntax_Syntax.sigquals = uu____8947;
              FStar_Syntax_Syntax.sigmeta = uu____8948;
              FStar_Syntax_Syntax.sigattrs = uu____8949;_},uu____8950),uu____8951)
          -> l
      | uu____9006 ->
          let uu____9027 =
            let uu____9028 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9028 in
          failwith uu____9027
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
        let uu____9065 = lookup_qname env lid in
        match uu____9065 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9093) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9144,lbs),uu____9146) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9174 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9174
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9206 -> FStar_Pervasives_Native.None)
        | uu____9211 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____9248 = lookup_qname env ftv in
      match uu____9248 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9272) ->
          let uu____9317 = effect_signature se in
          (match uu____9317 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____9338,t),r) ->
               let uu____9353 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____9353)
      | uu____9354 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9383 = try_lookup_effect_lid env ftv in
      match uu____9383 with
      | FStar_Pervasives_Native.None  ->
          let uu____9386 =
            let uu____9387 =
              let uu____9392 = name_not_found ftv in
              (uu____9392, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____9387 in
          FStar_Exn.raise uu____9386
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
        let uu____9412 = lookup_qname env lid0 in
        match uu____9412 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____9443);
                FStar_Syntax_Syntax.sigrng = uu____9444;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____9446;
                FStar_Syntax_Syntax.sigattrs = uu____9447;_},FStar_Pervasives_Native.None
              ),uu____9448)
            ->
            let lid1 =
              let uu____9502 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____9502 in
            let uu____9503 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___113_9507  ->
                      match uu___113_9507 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9508 -> false)) in
            if uu____9503
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____9522 =
                      let uu____9523 =
                        let uu____9524 = get_range env in
                        FStar_Range.string_of_range uu____9524 in
                      let uu____9525 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____9526 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____9523 uu____9525 uu____9526 in
                    failwith uu____9522) in
               match (binders, univs1) with
               | ([],uu____9533) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____9550,uu____9551::uu____9552::uu____9553) ->
                   let uu____9558 =
                     let uu____9559 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____9560 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____9559 uu____9560 in
                   failwith uu____9558
               | uu____9567 ->
                   let uu____9572 =
                     let uu____9577 =
                       let uu____9578 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____9578) in
                     inst_tscheme_with uu____9577 insts in
                   (match uu____9572 with
                    | (uu____9589,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____9592 =
                          let uu____9593 = FStar_Syntax_Subst.compress t1 in
                          uu____9593.FStar_Syntax_Syntax.n in
                        (match uu____9592 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____9640 -> failwith "Impossible")))
        | uu____9647 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____9689 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____9689 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____9702,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____9709 = find1 l2 in
            (match uu____9709 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____9716 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____9716 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____9720 = find1 l in
            (match uu____9720 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____9736 = lookup_qname env l1 in
      match uu____9736 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____9759;
              FStar_Syntax_Syntax.sigrng = uu____9760;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9762;
              FStar_Syntax_Syntax.sigattrs = uu____9763;_},uu____9764),uu____9765)
          -> q
      | uu____9816 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____9852 =
          let uu____9853 =
            let uu____9854 = FStar_Util.string_of_int i in
            let uu____9855 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____9854 uu____9855 in
          failwith uu____9853 in
        let uu____9856 = lookup_datacon env lid in
        match uu____9856 with
        | (uu____9861,t) ->
            let uu____9863 =
              let uu____9864 = FStar_Syntax_Subst.compress t in
              uu____9864.FStar_Syntax_Syntax.n in
            (match uu____9863 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9868) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____9899 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____9899
                      FStar_Pervasives_Native.fst)
             | uu____9908 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9917 = lookup_qname env l in
      match uu____9917 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9938,uu____9939,uu____9940);
              FStar_Syntax_Syntax.sigrng = uu____9941;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9943;
              FStar_Syntax_Syntax.sigattrs = uu____9944;_},uu____9945),uu____9946)
          ->
          FStar_Util.for_some
            (fun uu___114_9999  ->
               match uu___114_9999 with
               | FStar_Syntax_Syntax.Projector uu____10000 -> true
               | uu____10005 -> false) quals
      | uu____10006 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10035 = lookup_qname env lid in
      match uu____10035 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10056,uu____10057,uu____10058,uu____10059,uu____10060,uu____10061);
              FStar_Syntax_Syntax.sigrng = uu____10062;
              FStar_Syntax_Syntax.sigquals = uu____10063;
              FStar_Syntax_Syntax.sigmeta = uu____10064;
              FStar_Syntax_Syntax.sigattrs = uu____10065;_},uu____10066),uu____10067)
          -> true
      | uu____10122 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10151 = lookup_qname env lid in
      match uu____10151 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10172,uu____10173,uu____10174,uu____10175,uu____10176,uu____10177);
              FStar_Syntax_Syntax.sigrng = uu____10178;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10180;
              FStar_Syntax_Syntax.sigattrs = uu____10181;_},uu____10182),uu____10183)
          ->
          FStar_Util.for_some
            (fun uu___115_10244  ->
               match uu___115_10244 with
               | FStar_Syntax_Syntax.RecordType uu____10245 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____10254 -> true
               | uu____10263 -> false) quals
      | uu____10264 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10293 = lookup_qname env lid in
      match uu____10293 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____10314,uu____10315);
              FStar_Syntax_Syntax.sigrng = uu____10316;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10318;
              FStar_Syntax_Syntax.sigattrs = uu____10319;_},uu____10320),uu____10321)
          ->
          FStar_Util.for_some
            (fun uu___116_10378  ->
               match uu___116_10378 with
               | FStar_Syntax_Syntax.Action uu____10379 -> true
               | uu____10380 -> false) quals
      | uu____10381 -> false
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
      let uu____10413 =
        let uu____10414 = FStar_Syntax_Util.un_uinst head1 in
        uu____10414.FStar_Syntax_Syntax.n in
      match uu____10413 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10418 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10485 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10501) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10518 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10525 ->
                 FStar_Pervasives_Native.Some true
             | uu____10542 -> FStar_Pervasives_Native.Some false) in
      let uu____10543 =
        let uu____10546 = lookup_qname env lid in
        FStar_Util.bind_opt uu____10546 mapper in
      match uu____10543 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____10594 = lookup_qname env lid in
      match uu____10594 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10615,uu____10616,tps,uu____10618,uu____10619,uu____10620);
              FStar_Syntax_Syntax.sigrng = uu____10621;
              FStar_Syntax_Syntax.sigquals = uu____10622;
              FStar_Syntax_Syntax.sigmeta = uu____10623;
              FStar_Syntax_Syntax.sigattrs = uu____10624;_},uu____10625),uu____10626)
          -> FStar_List.length tps
      | uu____10689 ->
          let uu____10710 =
            let uu____10711 =
              let uu____10716 = name_not_found lid in
              (uu____10716, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____10711 in
          FStar_Exn.raise uu____10710
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
           (fun uu____10758  ->
              match uu____10758 with
              | (d,uu____10766) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____10779 = effect_decl_opt env l in
      match uu____10779 with
      | FStar_Pervasives_Native.None  ->
          let uu____10794 =
            let uu____10795 =
              let uu____10800 = name_not_found l in
              (uu____10800, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____10795 in
          FStar_Exn.raise uu____10794
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
            (let uu____10866 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____10919  ->
                       match uu____10919 with
                       | (m1,m2,uu____10932,uu____10933,uu____10934) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____10866 with
             | FStar_Pervasives_Native.None  ->
                 let uu____10951 =
                   let uu____10952 =
                     let uu____10957 =
                       let uu____10958 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____10959 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____10958
                         uu____10959 in
                     (uu____10957, (env.range)) in
                   FStar_Errors.Error uu____10952 in
                 FStar_Exn.raise uu____10951
             | FStar_Pervasives_Native.Some
                 (uu____10966,uu____10967,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11010 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11010)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11037 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11063  ->
                match uu____11063 with
                | (d,uu____11069) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11037 with
      | FStar_Pervasives_Native.None  ->
          let uu____11080 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11080
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11093 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11093 with
           | (uu____11104,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11114)::(wp,uu____11116)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11152 -> failwith "Impossible"))
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
                 let uu____11201 = get_range env in
                 let uu____11202 =
                   let uu____11205 =
                     let uu____11206 =
                       let uu____11221 =
                         let uu____11224 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11224] in
                       (null_wp, uu____11221) in
                     FStar_Syntax_Syntax.Tm_app uu____11206 in
                   FStar_Syntax_Syntax.mk uu____11205 in
                 uu____11202 FStar_Pervasives_Native.None uu____11201 in
               let uu____11230 =
                 let uu____11231 =
                   let uu____11240 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11240] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11231;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11230)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___127_11251 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___127_11251.order);
              joins = (uu___127_11251.joins)
            } in
          let uu___128_11260 = env in
          {
            solver = (uu___128_11260.solver);
            range = (uu___128_11260.range);
            curmodule = (uu___128_11260.curmodule);
            gamma = (uu___128_11260.gamma);
            gamma_cache = (uu___128_11260.gamma_cache);
            modules = (uu___128_11260.modules);
            expected_typ = (uu___128_11260.expected_typ);
            sigtab = (uu___128_11260.sigtab);
            is_pattern = (uu___128_11260.is_pattern);
            instantiate_imp = (uu___128_11260.instantiate_imp);
            effects;
            generalize = (uu___128_11260.generalize);
            letrecs = (uu___128_11260.letrecs);
            top_level = (uu___128_11260.top_level);
            check_uvars = (uu___128_11260.check_uvars);
            use_eq = (uu___128_11260.use_eq);
            is_iface = (uu___128_11260.is_iface);
            admit = (uu___128_11260.admit);
            lax = (uu___128_11260.lax);
            lax_universes = (uu___128_11260.lax_universes);
            type_of = (uu___128_11260.type_of);
            universe_of = (uu___128_11260.universe_of);
            use_bv_sorts = (uu___128_11260.use_bv_sorts);
            qname_and_index = (uu___128_11260.qname_and_index);
            proof_ns = (uu___128_11260.proof_ns);
            synth = (uu___128_11260.synth);
            is_native_tactic = (uu___128_11260.is_native_tactic);
            identifier_info = (uu___128_11260.identifier_info)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____11277 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____11277 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____11367 = (e1.mlift).mlift_wp t wp in
                              let uu____11368 = l1 t wp e in
                              l2 t uu____11367 uu____11368))
                | uu____11369 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____11408 = inst_tscheme lift_t in
            match uu____11408 with
            | (uu____11415,lift_t1) ->
                let uu____11417 =
                  let uu____11420 =
                    let uu____11421 =
                      let uu____11436 =
                        let uu____11439 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11440 =
                          let uu____11443 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____11443] in
                        uu____11439 :: uu____11440 in
                      (lift_t1, uu____11436) in
                    FStar_Syntax_Syntax.Tm_app uu____11421 in
                  FStar_Syntax_Syntax.mk uu____11420 in
                uu____11417 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____11484 = inst_tscheme lift_t in
            match uu____11484 with
            | (uu____11491,lift_t1) ->
                let uu____11493 =
                  let uu____11496 =
                    let uu____11497 =
                      let uu____11512 =
                        let uu____11515 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11516 =
                          let uu____11519 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____11520 =
                            let uu____11523 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11523] in
                          uu____11519 :: uu____11520 in
                        uu____11515 :: uu____11516 in
                      (lift_t1, uu____11512) in
                    FStar_Syntax_Syntax.Tm_app uu____11497 in
                  FStar_Syntax_Syntax.mk uu____11496 in
                uu____11493 FStar_Pervasives_Native.None
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
              let uu____11561 =
                let uu____11562 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____11562
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____11561 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____11566 =
              let uu____11567 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____11567 in
            let uu____11568 =
              let uu____11569 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11587 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____11587) in
              FStar_Util.dflt "none" uu____11569 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11566
              uu____11568 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11613  ->
                    match uu____11613 with
                    | (e,uu____11621) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____11640 =
            match uu____11640 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____11678 =
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
                                    (let uu____11699 =
                                       let uu____11708 =
                                         find_edge order1 (i, k) in
                                       let uu____11711 =
                                         find_edge order1 (k, j) in
                                       (uu____11708, uu____11711) in
                                     match uu____11699 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____11726 =
                                           compose_edges e1 e2 in
                                         [uu____11726]
                                     | uu____11727 -> []))))) in
              FStar_List.append order1 uu____11678 in
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
                   let uu____11756 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____11758 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____11758
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____11756
                   then
                     let uu____11763 =
                       let uu____11764 =
                         let uu____11769 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____11770 = get_range env in
                         (uu____11769, uu____11770) in
                       FStar_Errors.Error uu____11764 in
                     FStar_Exn.raise uu____11763
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
                                            let uu____11895 =
                                              let uu____11904 =
                                                find_edge order2 (i, k) in
                                              let uu____11907 =
                                                find_edge order2 (j, k) in
                                              (uu____11904, uu____11907) in
                                            match uu____11895 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____11949,uu____11950)
                                                     ->
                                                     let uu____11957 =
                                                       let uu____11962 =
                                                         let uu____11963 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____11963 in
                                                       let uu____11966 =
                                                         let uu____11967 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____11967 in
                                                       (uu____11962,
                                                         uu____11966) in
                                                     (match uu____11957 with
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
                                            | uu____12002 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___129_12075 = env.effects in
              { decls = (uu___129_12075.decls); order = order2; joins } in
            let uu___130_12076 = env in
            {
              solver = (uu___130_12076.solver);
              range = (uu___130_12076.range);
              curmodule = (uu___130_12076.curmodule);
              gamma = (uu___130_12076.gamma);
              gamma_cache = (uu___130_12076.gamma_cache);
              modules = (uu___130_12076.modules);
              expected_typ = (uu___130_12076.expected_typ);
              sigtab = (uu___130_12076.sigtab);
              is_pattern = (uu___130_12076.is_pattern);
              instantiate_imp = (uu___130_12076.instantiate_imp);
              effects;
              generalize = (uu___130_12076.generalize);
              letrecs = (uu___130_12076.letrecs);
              top_level = (uu___130_12076.top_level);
              check_uvars = (uu___130_12076.check_uvars);
              use_eq = (uu___130_12076.use_eq);
              is_iface = (uu___130_12076.is_iface);
              admit = (uu___130_12076.admit);
              lax = (uu___130_12076.lax);
              lax_universes = (uu___130_12076.lax_universes);
              type_of = (uu___130_12076.type_of);
              universe_of = (uu___130_12076.universe_of);
              use_bv_sorts = (uu___130_12076.use_bv_sorts);
              qname_and_index = (uu___130_12076.qname_and_index);
              proof_ns = (uu___130_12076.proof_ns);
              synth = (uu___130_12076.synth);
              is_native_tactic = (uu___130_12076.is_native_tactic);
              identifier_info = (uu___130_12076.identifier_info)
            }))
      | uu____12077 -> env
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
        | uu____12103 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12113 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12113 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12130 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12130 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12148 =
                     let uu____12149 =
                       let uu____12154 =
                         let uu____12155 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12160 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12167 =
                           let uu____12168 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12168 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12155 uu____12160 uu____12167 in
                       (uu____12154, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12149 in
                   FStar_Exn.raise uu____12148)
                else ();
                (let inst1 =
                   let uu____12173 =
                     let uu____12182 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12182 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12199  ->
                        fun uu____12200  ->
                          match (uu____12199, uu____12200) with
                          | ((x,uu____12222),(t,uu____12224)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12173 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12243 =
                     let uu___131_12244 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___131_12244.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___131_12244.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___131_12244.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___131_12244.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12243
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
          let uu____12269 =
            let uu____12278 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____12278 in
          match uu____12269 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____12303 =
                only_reifiable &&
                  (let uu____12305 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____12305) in
              if uu____12303
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____12321 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____12323 =
                       let uu____12336 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____12336) in
                     (match uu____12323 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____12382 =
                            let uu____12385 = get_range env in
                            let uu____12386 =
                              let uu____12389 =
                                let uu____12390 =
                                  let uu____12405 =
                                    let uu____12408 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____12408; wp] in
                                  (repr, uu____12405) in
                                FStar_Syntax_Syntax.Tm_app uu____12390 in
                              FStar_Syntax_Syntax.mk uu____12389 in
                            uu____12386 FStar_Pervasives_Native.None
                              uu____12385 in
                          FStar_Pervasives_Native.Some uu____12382))
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
          let uu____12460 =
            let uu____12461 =
              let uu____12466 =
                let uu____12467 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____12467 in
              let uu____12468 = get_range env in (uu____12466, uu____12468) in
            FStar_Errors.Error uu____12461 in
          FStar_Exn.raise uu____12460 in
        let uu____12469 = effect_repr_aux true env c u_c in
        match uu____12469 with
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
      | uu____12509 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____12518 =
        let uu____12519 = FStar_Syntax_Subst.compress t in
        uu____12519.FStar_Syntax_Syntax.n in
      match uu____12518 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12522,c) ->
          is_reifiable_comp env c
      | uu____12540 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12564)::uu____12565 -> x :: rest
        | (Binding_sig_inst uu____12574)::uu____12575 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12590 = push1 x rest1 in local :: uu____12590 in
      let uu___132_12593 = env in
      let uu____12594 = push1 s env.gamma in
      {
        solver = (uu___132_12593.solver);
        range = (uu___132_12593.range);
        curmodule = (uu___132_12593.curmodule);
        gamma = uu____12594;
        gamma_cache = (uu___132_12593.gamma_cache);
        modules = (uu___132_12593.modules);
        expected_typ = (uu___132_12593.expected_typ);
        sigtab = (uu___132_12593.sigtab);
        is_pattern = (uu___132_12593.is_pattern);
        instantiate_imp = (uu___132_12593.instantiate_imp);
        effects = (uu___132_12593.effects);
        generalize = (uu___132_12593.generalize);
        letrecs = (uu___132_12593.letrecs);
        top_level = (uu___132_12593.top_level);
        check_uvars = (uu___132_12593.check_uvars);
        use_eq = (uu___132_12593.use_eq);
        is_iface = (uu___132_12593.is_iface);
        admit = (uu___132_12593.admit);
        lax = (uu___132_12593.lax);
        lax_universes = (uu___132_12593.lax_universes);
        type_of = (uu___132_12593.type_of);
        universe_of = (uu___132_12593.universe_of);
        use_bv_sorts = (uu___132_12593.use_bv_sorts);
        qname_and_index = (uu___132_12593.qname_and_index);
        proof_ns = (uu___132_12593.proof_ns);
        synth = (uu___132_12593.synth);
        is_native_tactic = (uu___132_12593.is_native_tactic);
        identifier_info = (uu___132_12593.identifier_info)
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
      let uu___133_12631 = env in
      {
        solver = (uu___133_12631.solver);
        range = (uu___133_12631.range);
        curmodule = (uu___133_12631.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___133_12631.gamma_cache);
        modules = (uu___133_12631.modules);
        expected_typ = (uu___133_12631.expected_typ);
        sigtab = (uu___133_12631.sigtab);
        is_pattern = (uu___133_12631.is_pattern);
        instantiate_imp = (uu___133_12631.instantiate_imp);
        effects = (uu___133_12631.effects);
        generalize = (uu___133_12631.generalize);
        letrecs = (uu___133_12631.letrecs);
        top_level = (uu___133_12631.top_level);
        check_uvars = (uu___133_12631.check_uvars);
        use_eq = (uu___133_12631.use_eq);
        is_iface = (uu___133_12631.is_iface);
        admit = (uu___133_12631.admit);
        lax = (uu___133_12631.lax);
        lax_universes = (uu___133_12631.lax_universes);
        type_of = (uu___133_12631.type_of);
        universe_of = (uu___133_12631.universe_of);
        use_bv_sorts = (uu___133_12631.use_bv_sorts);
        qname_and_index = (uu___133_12631.qname_and_index);
        proof_ns = (uu___133_12631.proof_ns);
        synth = (uu___133_12631.synth);
        is_native_tactic = (uu___133_12631.is_native_tactic);
        identifier_info = (uu___133_12631.identifier_info)
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
            (let uu___134_12665 = env in
             {
               solver = (uu___134_12665.solver);
               range = (uu___134_12665.range);
               curmodule = (uu___134_12665.curmodule);
               gamma = rest;
               gamma_cache = (uu___134_12665.gamma_cache);
               modules = (uu___134_12665.modules);
               expected_typ = (uu___134_12665.expected_typ);
               sigtab = (uu___134_12665.sigtab);
               is_pattern = (uu___134_12665.is_pattern);
               instantiate_imp = (uu___134_12665.instantiate_imp);
               effects = (uu___134_12665.effects);
               generalize = (uu___134_12665.generalize);
               letrecs = (uu___134_12665.letrecs);
               top_level = (uu___134_12665.top_level);
               check_uvars = (uu___134_12665.check_uvars);
               use_eq = (uu___134_12665.use_eq);
               is_iface = (uu___134_12665.is_iface);
               admit = (uu___134_12665.admit);
               lax = (uu___134_12665.lax);
               lax_universes = (uu___134_12665.lax_universes);
               type_of = (uu___134_12665.type_of);
               universe_of = (uu___134_12665.universe_of);
               use_bv_sorts = (uu___134_12665.use_bv_sorts);
               qname_and_index = (uu___134_12665.qname_and_index);
               proof_ns = (uu___134_12665.proof_ns);
               synth = (uu___134_12665.synth);
               is_native_tactic = (uu___134_12665.is_native_tactic);
               identifier_info = (uu___134_12665.identifier_info)
             }))
    | uu____12666 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12690  ->
             match uu____12690 with | (x,uu____12696) -> push_bv env1 x) env
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
            let uu___135_12726 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___135_12726.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___135_12726.FStar_Syntax_Syntax.index);
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
      (let uu___136_12761 = env in
       {
         solver = (uu___136_12761.solver);
         range = (uu___136_12761.range);
         curmodule = (uu___136_12761.curmodule);
         gamma = [];
         gamma_cache = (uu___136_12761.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___136_12761.sigtab);
         is_pattern = (uu___136_12761.is_pattern);
         instantiate_imp = (uu___136_12761.instantiate_imp);
         effects = (uu___136_12761.effects);
         generalize = (uu___136_12761.generalize);
         letrecs = (uu___136_12761.letrecs);
         top_level = (uu___136_12761.top_level);
         check_uvars = (uu___136_12761.check_uvars);
         use_eq = (uu___136_12761.use_eq);
         is_iface = (uu___136_12761.is_iface);
         admit = (uu___136_12761.admit);
         lax = (uu___136_12761.lax);
         lax_universes = (uu___136_12761.lax_universes);
         type_of = (uu___136_12761.type_of);
         universe_of = (uu___136_12761.universe_of);
         use_bv_sorts = (uu___136_12761.use_bv_sorts);
         qname_and_index = (uu___136_12761.qname_and_index);
         proof_ns = (uu___136_12761.proof_ns);
         synth = (uu___136_12761.synth);
         is_native_tactic = (uu___136_12761.is_native_tactic);
         identifier_info = (uu___136_12761.identifier_info)
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
        let uu____12798 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____12798 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____12826 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____12826)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___137_12841 = env in
      {
        solver = (uu___137_12841.solver);
        range = (uu___137_12841.range);
        curmodule = (uu___137_12841.curmodule);
        gamma = (uu___137_12841.gamma);
        gamma_cache = (uu___137_12841.gamma_cache);
        modules = (uu___137_12841.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___137_12841.sigtab);
        is_pattern = (uu___137_12841.is_pattern);
        instantiate_imp = (uu___137_12841.instantiate_imp);
        effects = (uu___137_12841.effects);
        generalize = (uu___137_12841.generalize);
        letrecs = (uu___137_12841.letrecs);
        top_level = (uu___137_12841.top_level);
        check_uvars = (uu___137_12841.check_uvars);
        use_eq = false;
        is_iface = (uu___137_12841.is_iface);
        admit = (uu___137_12841.admit);
        lax = (uu___137_12841.lax);
        lax_universes = (uu___137_12841.lax_universes);
        type_of = (uu___137_12841.type_of);
        universe_of = (uu___137_12841.universe_of);
        use_bv_sorts = (uu___137_12841.use_bv_sorts);
        qname_and_index = (uu___137_12841.qname_and_index);
        proof_ns = (uu___137_12841.proof_ns);
        synth = (uu___137_12841.synth);
        is_native_tactic = (uu___137_12841.is_native_tactic);
        identifier_info = (uu___137_12841.identifier_info)
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
    let uu____12867 = expected_typ env_ in
    ((let uu___138_12873 = env_ in
      {
        solver = (uu___138_12873.solver);
        range = (uu___138_12873.range);
        curmodule = (uu___138_12873.curmodule);
        gamma = (uu___138_12873.gamma);
        gamma_cache = (uu___138_12873.gamma_cache);
        modules = (uu___138_12873.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___138_12873.sigtab);
        is_pattern = (uu___138_12873.is_pattern);
        instantiate_imp = (uu___138_12873.instantiate_imp);
        effects = (uu___138_12873.effects);
        generalize = (uu___138_12873.generalize);
        letrecs = (uu___138_12873.letrecs);
        top_level = (uu___138_12873.top_level);
        check_uvars = (uu___138_12873.check_uvars);
        use_eq = false;
        is_iface = (uu___138_12873.is_iface);
        admit = (uu___138_12873.admit);
        lax = (uu___138_12873.lax);
        lax_universes = (uu___138_12873.lax_universes);
        type_of = (uu___138_12873.type_of);
        universe_of = (uu___138_12873.universe_of);
        use_bv_sorts = (uu___138_12873.use_bv_sorts);
        qname_and_index = (uu___138_12873.qname_and_index);
        proof_ns = (uu___138_12873.proof_ns);
        synth = (uu___138_12873.synth);
        is_native_tactic = (uu___138_12873.is_native_tactic);
        identifier_info = (uu___138_12873.identifier_info)
      }), uu____12867)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____12888 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___117_12898  ->
                    match uu___117_12898 with
                    | Binding_sig (uu____12901,se) -> [se]
                    | uu____12907 -> [])) in
          FStar_All.pipe_right uu____12888 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___139_12914 = env in
       {
         solver = (uu___139_12914.solver);
         range = (uu___139_12914.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___139_12914.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___139_12914.expected_typ);
         sigtab = (uu___139_12914.sigtab);
         is_pattern = (uu___139_12914.is_pattern);
         instantiate_imp = (uu___139_12914.instantiate_imp);
         effects = (uu___139_12914.effects);
         generalize = (uu___139_12914.generalize);
         letrecs = (uu___139_12914.letrecs);
         top_level = (uu___139_12914.top_level);
         check_uvars = (uu___139_12914.check_uvars);
         use_eq = (uu___139_12914.use_eq);
         is_iface = (uu___139_12914.is_iface);
         admit = (uu___139_12914.admit);
         lax = (uu___139_12914.lax);
         lax_universes = (uu___139_12914.lax_universes);
         type_of = (uu___139_12914.type_of);
         universe_of = (uu___139_12914.universe_of);
         use_bv_sorts = (uu___139_12914.use_bv_sorts);
         qname_and_index = (uu___139_12914.qname_and_index);
         proof_ns = (uu___139_12914.proof_ns);
         synth = (uu___139_12914.synth);
         is_native_tactic = (uu___139_12914.is_native_tactic);
         identifier_info = (uu___139_12914.identifier_info)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____12996)::tl1 -> aux out tl1
      | (Binding_lid (uu____13000,(uu____13001,t)))::tl1 ->
          let uu____13016 =
            let uu____13023 = FStar_Syntax_Free.uvars t in
            ext out uu____13023 in
          aux uu____13016 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13030;
            FStar_Syntax_Syntax.index = uu____13031;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13038 =
            let uu____13045 = FStar_Syntax_Free.uvars t in
            ext out uu____13045 in
          aux uu____13038 tl1
      | (Binding_sig uu____13052)::uu____13053 -> out
      | (Binding_sig_inst uu____13062)::uu____13063 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13119)::tl1 -> aux out tl1
      | (Binding_univ uu____13131)::tl1 -> aux out tl1
      | (Binding_lid (uu____13135,(uu____13136,t)))::tl1 ->
          let uu____13151 =
            let uu____13154 = FStar_Syntax_Free.univs t in
            ext out uu____13154 in
          aux uu____13151 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13157;
            FStar_Syntax_Syntax.index = uu____13158;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13165 =
            let uu____13168 = FStar_Syntax_Free.univs t in
            ext out uu____13168 in
          aux uu____13165 tl1
      | (Binding_sig uu____13171)::uu____13172 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13226)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13242 = FStar_Util.set_add uname out in
          aux uu____13242 tl1
      | (Binding_lid (uu____13245,(uu____13246,t)))::tl1 ->
          let uu____13261 =
            let uu____13264 = FStar_Syntax_Free.univnames t in
            ext out uu____13264 in
          aux uu____13261 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13267;
            FStar_Syntax_Syntax.index = uu____13268;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13275 =
            let uu____13278 = FStar_Syntax_Free.univnames t in
            ext out uu____13278 in
          aux uu____13275 tl1
      | (Binding_sig uu____13281)::uu____13282 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___118_13310  ->
            match uu___118_13310 with
            | Binding_var x -> [x]
            | Binding_lid uu____13314 -> []
            | Binding_sig uu____13319 -> []
            | Binding_univ uu____13326 -> []
            | Binding_sig_inst uu____13327 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____13344 =
      let uu____13347 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____13347
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____13344 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____13372 =
      let uu____13373 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___119_13383  ->
                match uu___119_13383 with
                | Binding_var x ->
                    let uu____13385 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____13385
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13388) ->
                    let uu____13389 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____13389
                | Binding_sig (ls,uu____13391) ->
                    let uu____13396 =
                      let uu____13397 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13397
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____13396
                | Binding_sig_inst (ls,uu____13407,uu____13408) ->
                    let uu____13413 =
                      let uu____13414 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13414
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____13413)) in
      FStar_All.pipe_right uu____13373 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____13372 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____13433 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____13433
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13461  ->
                 fun uu____13462  ->
                   match (uu____13461, uu____13462) with
                   | ((b1,uu____13480),(b2,uu____13482)) ->
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
           fun uu___120_13544  ->
             match uu___120_13544 with
             | Binding_sig (lids,uu____13550) -> FStar_List.append lids keys
             | uu____13555 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13561  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13597) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13616,uu____13617) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13654 = list_prefix p path1 in
            if uu____13654 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13668 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13668
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___140_13698 = e in
            {
              solver = (uu___140_13698.solver);
              range = (uu___140_13698.range);
              curmodule = (uu___140_13698.curmodule);
              gamma = (uu___140_13698.gamma);
              gamma_cache = (uu___140_13698.gamma_cache);
              modules = (uu___140_13698.modules);
              expected_typ = (uu___140_13698.expected_typ);
              sigtab = (uu___140_13698.sigtab);
              is_pattern = (uu___140_13698.is_pattern);
              instantiate_imp = (uu___140_13698.instantiate_imp);
              effects = (uu___140_13698.effects);
              generalize = (uu___140_13698.generalize);
              letrecs = (uu___140_13698.letrecs);
              top_level = (uu___140_13698.top_level);
              check_uvars = (uu___140_13698.check_uvars);
              use_eq = (uu___140_13698.use_eq);
              is_iface = (uu___140_13698.is_iface);
              admit = (uu___140_13698.admit);
              lax = (uu___140_13698.lax);
              lax_universes = (uu___140_13698.lax_universes);
              type_of = (uu___140_13698.type_of);
              universe_of = (uu___140_13698.universe_of);
              use_bv_sorts = (uu___140_13698.use_bv_sorts);
              qname_and_index = (uu___140_13698.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___140_13698.synth);
              is_native_tactic = (uu___140_13698.is_native_tactic);
              identifier_info = (uu___140_13698.identifier_info)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___141_13725 = e in
    {
      solver = (uu___141_13725.solver);
      range = (uu___141_13725.range);
      curmodule = (uu___141_13725.curmodule);
      gamma = (uu___141_13725.gamma);
      gamma_cache = (uu___141_13725.gamma_cache);
      modules = (uu___141_13725.modules);
      expected_typ = (uu___141_13725.expected_typ);
      sigtab = (uu___141_13725.sigtab);
      is_pattern = (uu___141_13725.is_pattern);
      instantiate_imp = (uu___141_13725.instantiate_imp);
      effects = (uu___141_13725.effects);
      generalize = (uu___141_13725.generalize);
      letrecs = (uu___141_13725.letrecs);
      top_level = (uu___141_13725.top_level);
      check_uvars = (uu___141_13725.check_uvars);
      use_eq = (uu___141_13725.use_eq);
      is_iface = (uu___141_13725.is_iface);
      admit = (uu___141_13725.admit);
      lax = (uu___141_13725.lax);
      lax_universes = (uu___141_13725.lax_universes);
      type_of = (uu___141_13725.type_of);
      universe_of = (uu___141_13725.universe_of);
      use_bv_sorts = (uu___141_13725.use_bv_sorts);
      qname_and_index = (uu___141_13725.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___141_13725.synth);
      is_native_tactic = (uu___141_13725.is_native_tactic);
      identifier_info = (uu___141_13725.identifier_info)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____13740::rest ->
        let uu___142_13744 = e in
        {
          solver = (uu___142_13744.solver);
          range = (uu___142_13744.range);
          curmodule = (uu___142_13744.curmodule);
          gamma = (uu___142_13744.gamma);
          gamma_cache = (uu___142_13744.gamma_cache);
          modules = (uu___142_13744.modules);
          expected_typ = (uu___142_13744.expected_typ);
          sigtab = (uu___142_13744.sigtab);
          is_pattern = (uu___142_13744.is_pattern);
          instantiate_imp = (uu___142_13744.instantiate_imp);
          effects = (uu___142_13744.effects);
          generalize = (uu___142_13744.generalize);
          letrecs = (uu___142_13744.letrecs);
          top_level = (uu___142_13744.top_level);
          check_uvars = (uu___142_13744.check_uvars);
          use_eq = (uu___142_13744.use_eq);
          is_iface = (uu___142_13744.is_iface);
          admit = (uu___142_13744.admit);
          lax = (uu___142_13744.lax);
          lax_universes = (uu___142_13744.lax_universes);
          type_of = (uu___142_13744.type_of);
          universe_of = (uu___142_13744.universe_of);
          use_bv_sorts = (uu___142_13744.use_bv_sorts);
          qname_and_index = (uu___142_13744.qname_and_index);
          proof_ns = rest;
          synth = (uu___142_13744.synth);
          is_native_tactic = (uu___142_13744.is_native_tactic);
          identifier_info = (uu___142_13744.identifier_info)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___143_13757 = e in
      {
        solver = (uu___143_13757.solver);
        range = (uu___143_13757.range);
        curmodule = (uu___143_13757.curmodule);
        gamma = (uu___143_13757.gamma);
        gamma_cache = (uu___143_13757.gamma_cache);
        modules = (uu___143_13757.modules);
        expected_typ = (uu___143_13757.expected_typ);
        sigtab = (uu___143_13757.sigtab);
        is_pattern = (uu___143_13757.is_pattern);
        instantiate_imp = (uu___143_13757.instantiate_imp);
        effects = (uu___143_13757.effects);
        generalize = (uu___143_13757.generalize);
        letrecs = (uu___143_13757.letrecs);
        top_level = (uu___143_13757.top_level);
        check_uvars = (uu___143_13757.check_uvars);
        use_eq = (uu___143_13757.use_eq);
        is_iface = (uu___143_13757.is_iface);
        admit = (uu___143_13757.admit);
        lax = (uu___143_13757.lax);
        lax_universes = (uu___143_13757.lax_universes);
        type_of = (uu___143_13757.type_of);
        universe_of = (uu___143_13757.universe_of);
        use_bv_sorts = (uu___143_13757.use_bv_sorts);
        qname_and_index = (uu___143_13757.qname_and_index);
        proof_ns = ns;
        synth = (uu___143_13757.synth);
        is_native_tactic = (uu___143_13757.is_native_tactic);
        identifier_info = (uu___143_13757.identifier_info)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____13786 =
        FStar_List.map
          (fun fpns  ->
             let uu____13808 =
               let uu____13809 =
                 let uu____13810 =
                   FStar_List.map
                     (fun uu____13822  ->
                        match uu____13822 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____13810 in
               Prims.strcat uu____13809 "]" in
             Prims.strcat "[" uu____13808) pns in
      FStar_String.concat ";" uu____13786 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____13838  -> ());
    push = (fun uu____13840  -> ());
    pop = (fun uu____13842  -> ());
    mark = (fun uu____13844  -> ());
    reset_mark = (fun uu____13846  -> ());
    commit_mark = (fun uu____13848  -> ());
    encode_modul = (fun uu____13851  -> fun uu____13852  -> ());
    encode_sig = (fun uu____13855  -> fun uu____13856  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____13862 =
             let uu____13869 = FStar_Options.peek () in (e, g, uu____13869) in
           [uu____13862]);
    solve = (fun uu____13885  -> fun uu____13886  -> fun uu____13887  -> ());
    is_trivial = (fun uu____13894  -> fun uu____13895  -> false);
    finish = (fun uu____13897  -> ());
    refresh = (fun uu____13899  -> ())
  }