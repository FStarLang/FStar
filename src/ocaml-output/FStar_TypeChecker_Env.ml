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
  is_native_tactic: FStar_Ident.lid -> Prims.bool;}
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__solver
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__range
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__curmodule
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__gamma
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__modules
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__sigtab
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__effects
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__letrecs
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__top_level
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__use_eq
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__is_iface
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__admit
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__lax
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__type_of
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        type_of = __fname__type_of; universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        is_native_tactic = __fname__is_native_tactic;_} ->
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__proof_ns
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
        is_native_tactic = __fname__is_native_tactic;_} -> __fname__synth
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
        is_native_tactic = __fname__is_native_tactic;_} ->
        __fname__is_native_tactic
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
      | (NoDelta ,uu____4204) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4205,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4206,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4207 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4216 . Prims.unit -> 'Auu____4216 FStar_Util.smap =
  fun uu____4222  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4227 . Prims.unit -> 'Auu____4227 FStar_Util.smap =
  fun uu____4233  -> FStar_Util.smap_create (Prims.parse_int "100")
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
          let uu____4282 = new_gamma_cache () in
          let uu____4285 = new_sigtab () in
          let uu____4288 =
            let uu____4289 = FStar_Options.using_facts_from () in
            match uu____4289 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____4299 =
                  let uu____4308 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____4308 [([], false)] in
                [uu____4299]
            | FStar_Pervasives_Native.None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____4282;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____4285;
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
            proof_ns = uu____4288;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____4412  -> false)
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
  fun uu____4469  ->
    let uu____4470 = FStar_ST.op_Bang query_indices in
    match uu____4470 with
    | [] -> failwith "Empty query indices!"
    | uu____4527 ->
        let uu____4536 =
          let uu____4545 =
            let uu____4552 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____4552 in
          let uu____4609 = FStar_ST.op_Bang query_indices in uu____4545 ::
            uu____4609 in
        FStar_ST.op_Colon_Equals query_indices uu____4536
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____4711  ->
    let uu____4712 = FStar_ST.op_Bang query_indices in
    match uu____4712 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____4840  ->
    match uu____4840 with
    | (l,n1) ->
        let uu____4847 = FStar_ST.op_Bang query_indices in
        (match uu____4847 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____4972 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____4990  ->
    let uu____4991 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____4991
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____5051  ->
    let uu____5052 = FStar_ST.op_Bang query_indices in
    match uu____5052 with
    | hd1::uu____5104::tl1 ->
        FStar_ST.op_Colon_Equals query_indices (hd1 :: tl1)
    | uu____5186 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5213 =
       let uu____5216 = FStar_ST.op_Bang stack in env :: uu____5216 in
     FStar_ST.op_Colon_Equals stack uu____5213);
    (let uu___117_5255 = env in
     let uu____5256 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5259 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___117_5255.solver);
       range = (uu___117_5255.range);
       curmodule = (uu___117_5255.curmodule);
       gamma = (uu___117_5255.gamma);
       gamma_cache = uu____5256;
       modules = (uu___117_5255.modules);
       expected_typ = (uu___117_5255.expected_typ);
       sigtab = uu____5259;
       is_pattern = (uu___117_5255.is_pattern);
       instantiate_imp = (uu___117_5255.instantiate_imp);
       effects = (uu___117_5255.effects);
       generalize = (uu___117_5255.generalize);
       letrecs = (uu___117_5255.letrecs);
       top_level = (uu___117_5255.top_level);
       check_uvars = (uu___117_5255.check_uvars);
       use_eq = (uu___117_5255.use_eq);
       is_iface = (uu___117_5255.is_iface);
       admit = (uu___117_5255.admit);
       lax = (uu___117_5255.lax);
       lax_universes = (uu___117_5255.lax_universes);
       type_of = (uu___117_5255.type_of);
       universe_of = (uu___117_5255.universe_of);
       use_bv_sorts = (uu___117_5255.use_bv_sorts);
       qname_and_index = (uu___117_5255.qname_and_index);
       proof_ns = (uu___117_5255.proof_ns);
       synth = (uu___117_5255.synth);
       is_native_tactic = (uu___117_5255.is_native_tactic)
     })
let pop_stack: Prims.unit -> env =
  fun uu____5265  ->
    let uu____5266 = FStar_ST.op_Bang stack in
    match uu____5266 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____5310 -> failwith "Impossible: Too many pops"
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
    (let uu____5350 = pop_stack () in ());
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
        let uu____5378 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____5404  ->
                  match uu____5404 with
                  | (m,uu____5410) -> FStar_Ident.lid_equals l m)) in
        (match uu____5378 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___118_5417 = env in
               {
                 solver = (uu___118_5417.solver);
                 range = (uu___118_5417.range);
                 curmodule = (uu___118_5417.curmodule);
                 gamma = (uu___118_5417.gamma);
                 gamma_cache = (uu___118_5417.gamma_cache);
                 modules = (uu___118_5417.modules);
                 expected_typ = (uu___118_5417.expected_typ);
                 sigtab = (uu___118_5417.sigtab);
                 is_pattern = (uu___118_5417.is_pattern);
                 instantiate_imp = (uu___118_5417.instantiate_imp);
                 effects = (uu___118_5417.effects);
                 generalize = (uu___118_5417.generalize);
                 letrecs = (uu___118_5417.letrecs);
                 top_level = (uu___118_5417.top_level);
                 check_uvars = (uu___118_5417.check_uvars);
                 use_eq = (uu___118_5417.use_eq);
                 is_iface = (uu___118_5417.is_iface);
                 admit = (uu___118_5417.admit);
                 lax = (uu___118_5417.lax);
                 lax_universes = (uu___118_5417.lax_universes);
                 type_of = (uu___118_5417.type_of);
                 universe_of = (uu___118_5417.universe_of);
                 use_bv_sorts = (uu___118_5417.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___118_5417.proof_ns);
                 synth = (uu___118_5417.synth);
                 is_native_tactic = (uu___118_5417.is_native_tactic)
               }))
         | FStar_Pervasives_Native.Some (uu____5422,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___119_5430 = env in
               {
                 solver = (uu___119_5430.solver);
                 range = (uu___119_5430.range);
                 curmodule = (uu___119_5430.curmodule);
                 gamma = (uu___119_5430.gamma);
                 gamma_cache = (uu___119_5430.gamma_cache);
                 modules = (uu___119_5430.modules);
                 expected_typ = (uu___119_5430.expected_typ);
                 sigtab = (uu___119_5430.sigtab);
                 is_pattern = (uu___119_5430.is_pattern);
                 instantiate_imp = (uu___119_5430.instantiate_imp);
                 effects = (uu___119_5430.effects);
                 generalize = (uu___119_5430.generalize);
                 letrecs = (uu___119_5430.letrecs);
                 top_level = (uu___119_5430.top_level);
                 check_uvars = (uu___119_5430.check_uvars);
                 use_eq = (uu___119_5430.use_eq);
                 is_iface = (uu___119_5430.is_iface);
                 admit = (uu___119_5430.admit);
                 lax = (uu___119_5430.lax);
                 lax_universes = (uu___119_5430.lax_universes);
                 type_of = (uu___119_5430.type_of);
                 universe_of = (uu___119_5430.universe_of);
                 use_bv_sorts = (uu___119_5430.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___119_5430.proof_ns);
                 synth = (uu___119_5430.synth);
                 is_native_tactic = (uu___119_5430.is_native_tactic)
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
        (let uu___120_5452 = e in
         {
           solver = (uu___120_5452.solver);
           range = r;
           curmodule = (uu___120_5452.curmodule);
           gamma = (uu___120_5452.gamma);
           gamma_cache = (uu___120_5452.gamma_cache);
           modules = (uu___120_5452.modules);
           expected_typ = (uu___120_5452.expected_typ);
           sigtab = (uu___120_5452.sigtab);
           is_pattern = (uu___120_5452.is_pattern);
           instantiate_imp = (uu___120_5452.instantiate_imp);
           effects = (uu___120_5452.effects);
           generalize = (uu___120_5452.generalize);
           letrecs = (uu___120_5452.letrecs);
           top_level = (uu___120_5452.top_level);
           check_uvars = (uu___120_5452.check_uvars);
           use_eq = (uu___120_5452.use_eq);
           is_iface = (uu___120_5452.is_iface);
           admit = (uu___120_5452.admit);
           lax = (uu___120_5452.lax);
           lax_universes = (uu___120_5452.lax_universes);
           type_of = (uu___120_5452.type_of);
           universe_of = (uu___120_5452.universe_of);
           use_bv_sorts = (uu___120_5452.use_bv_sorts);
           qname_and_index = (uu___120_5452.qname_and_index);
           proof_ns = (uu___120_5452.proof_ns);
           synth = (uu___120_5452.synth);
           is_native_tactic = (uu___120_5452.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___121_5475 = env in
      {
        solver = (uu___121_5475.solver);
        range = (uu___121_5475.range);
        curmodule = lid;
        gamma = (uu___121_5475.gamma);
        gamma_cache = (uu___121_5475.gamma_cache);
        modules = (uu___121_5475.modules);
        expected_typ = (uu___121_5475.expected_typ);
        sigtab = (uu___121_5475.sigtab);
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
        is_native_tactic = (uu___121_5475.is_native_tactic)
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
    let uu____5506 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____5506
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____5510  ->
    let uu____5511 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____5511
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
      | ((formals,t),uu____5551) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____5575 = FStar_Syntax_Subst.subst vs t in (us, uu____5575)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___105_5589  ->
    match uu___105_5589 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____5613  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____5628 = inst_tscheme t in
      match uu____5628 with
      | (us,t1) ->
          let uu____5639 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____5639)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____5655  ->
          match uu____5655 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____5670 =
                         let uu____5671 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____5672 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____5673 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____5674 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____5671 uu____5672 uu____5673 uu____5674 in
                       failwith uu____5670)
                    else ();
                    (let uu____5676 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____5676))
               | uu____5683 ->
                   let uu____5684 =
                     let uu____5685 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____5685 in
                   failwith uu____5684)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____5690 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____5695 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____5700 -> false
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
             | ([],uu____5736) -> Maybe
             | (uu____5743,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____5762 -> No in
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
          let uu____5869 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____5869 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___106_5914  ->
                   match uu___106_5914 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____5957 =
                           let uu____5976 =
                             let uu____5991 = inst_tscheme t in
                             FStar_Util.Inl uu____5991 in
                           (uu____5976, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____5957
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____6057,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____6059);
                                     FStar_Syntax_Syntax.sigrng = uu____6060;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____6061;
                                     FStar_Syntax_Syntax.sigmeta = uu____6062;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____6063;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____6083 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____6083
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____6129 ->
                             FStar_Pervasives_Native.Some t
                         | uu____6136 -> cache t in
                       let uu____6137 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6137 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____6212 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____6212 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____6298 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____6378 = find_in_sigtab env lid in
         match uu____6378 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6477) ->
          add_sigelts env ses
      | uu____6486 ->
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
            | uu____6500 -> ()))
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
        (fun uu___107_6529  ->
           match uu___107_6529 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____6547 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____6582,lb::[]),uu____6584) ->
          let uu____6597 =
            let uu____6606 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____6615 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____6606, uu____6615) in
          FStar_Pervasives_Native.Some uu____6597
      | FStar_Syntax_Syntax.Sig_let ((uu____6628,lbs),uu____6630) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____6666 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____6678 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____6678
                   then
                     let uu____6689 =
                       let uu____6698 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____6707 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____6698, uu____6707) in
                     FStar_Pervasives_Native.Some uu____6689
                   else FStar_Pervasives_Native.None)
      | uu____6729 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____6763 =
          let uu____6772 =
            let uu____6777 =
              let uu____6778 =
                let uu____6781 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____6781 in
              ((ne.FStar_Syntax_Syntax.univs), uu____6778) in
            inst_tscheme uu____6777 in
          (uu____6772, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____6763
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____6801,uu____6802) ->
        let uu____6807 =
          let uu____6816 =
            let uu____6821 =
              let uu____6822 =
                let uu____6825 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____6825 in
              (us, uu____6822) in
            inst_tscheme uu____6821 in
          (uu____6816, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____6807
    | uu____6842 -> FStar_Pervasives_Native.None
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
      let mapper uu____6902 =
        match uu____6902 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____6998,uvs,t,uu____7001,uu____7002,uu____7003);
                    FStar_Syntax_Syntax.sigrng = uu____7004;
                    FStar_Syntax_Syntax.sigquals = uu____7005;
                    FStar_Syntax_Syntax.sigmeta = uu____7006;
                    FStar_Syntax_Syntax.sigattrs = uu____7007;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7028 =
                   let uu____7037 = inst_tscheme (uvs, t) in
                   (uu____7037, rng) in
                 FStar_Pervasives_Native.Some uu____7028
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____7057;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____7059;
                    FStar_Syntax_Syntax.sigattrs = uu____7060;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____7077 =
                   let uu____7078 = in_cur_mod env l in uu____7078 = Yes in
                 if uu____7077
                 then
                   let uu____7089 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____7089
                    then
                      let uu____7102 =
                        let uu____7111 = inst_tscheme (uvs, t) in
                        (uu____7111, rng) in
                      FStar_Pervasives_Native.Some uu____7102
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____7138 =
                      let uu____7147 = inst_tscheme (uvs, t) in
                      (uu____7147, rng) in
                    FStar_Pervasives_Native.Some uu____7138)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7168,uu____7169);
                    FStar_Syntax_Syntax.sigrng = uu____7170;
                    FStar_Syntax_Syntax.sigquals = uu____7171;
                    FStar_Syntax_Syntax.sigmeta = uu____7172;
                    FStar_Syntax_Syntax.sigattrs = uu____7173;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____7212 =
                        let uu____7221 = inst_tscheme (uvs, k) in
                        (uu____7221, rng) in
                      FStar_Pervasives_Native.Some uu____7212
                  | uu____7238 ->
                      let uu____7239 =
                        let uu____7248 =
                          let uu____7253 =
                            let uu____7254 =
                              let uu____7257 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7257 in
                            (uvs, uu____7254) in
                          inst_tscheme uu____7253 in
                        (uu____7248, rng) in
                      FStar_Pervasives_Native.Some uu____7239)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____7278,uu____7279);
                    FStar_Syntax_Syntax.sigrng = uu____7280;
                    FStar_Syntax_Syntax.sigquals = uu____7281;
                    FStar_Syntax_Syntax.sigmeta = uu____7282;
                    FStar_Syntax_Syntax.sigattrs = uu____7283;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____7323 =
                        let uu____7332 = inst_tscheme_with (uvs, k) us in
                        (uu____7332, rng) in
                      FStar_Pervasives_Native.Some uu____7323
                  | uu____7349 ->
                      let uu____7350 =
                        let uu____7359 =
                          let uu____7364 =
                            let uu____7365 =
                              let uu____7368 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____7368 in
                            (uvs, uu____7365) in
                          inst_tscheme_with uu____7364 us in
                        (uu____7359, rng) in
                      FStar_Pervasives_Native.Some uu____7350)
             | FStar_Util.Inr se ->
                 let uu____7402 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____7423;
                        FStar_Syntax_Syntax.sigrng = uu____7424;
                        FStar_Syntax_Syntax.sigquals = uu____7425;
                        FStar_Syntax_Syntax.sigmeta = uu____7426;
                        FStar_Syntax_Syntax.sigattrs = uu____7427;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____7442 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____7402
                   (FStar_Util.map_option
                      (fun uu____7490  ->
                         match uu____7490 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____7521 =
        let uu____7532 = lookup_qname env lid in
        FStar_Util.bind_opt uu____7532 mapper in
      match uu____7521 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___122_7625 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___122_7625.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___122_7625.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____7652 = lookup_qname env l in
      match uu____7652 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____7691 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____7741 = try_lookup_bv env bv in
      match uu____7741 with
      | FStar_Pervasives_Native.None  ->
          let uu____7756 =
            let uu____7757 =
              let uu____7762 = variable_not_found bv in (uu____7762, bvr) in
            FStar_Errors.Error uu____7757 in
          FStar_Exn.raise uu____7756
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____7773 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____7774 = FStar_Range.set_use_range r bvr in
          (uu____7773, uu____7774)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____7793 = try_lookup_lid_aux env l in
      match uu____7793 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____7859 =
            let uu____7868 =
              let uu____7873 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____7873) in
            (uu____7868, r1) in
          FStar_Pervasives_Native.Some uu____7859
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____7902 = try_lookup_lid env l in
      match uu____7902 with
      | FStar_Pervasives_Native.None  ->
          let uu____7929 =
            let uu____7930 =
              let uu____7935 = name_not_found l in
              (uu____7935, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7930 in
          FStar_Exn.raise uu____7929
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___108_7973  ->
              match uu___108_7973 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____7975 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____7992 = lookup_qname env lid in
      match uu____7992 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8021,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8024;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8026;
              FStar_Syntax_Syntax.sigattrs = uu____8027;_},FStar_Pervasives_Native.None
            ),uu____8028)
          ->
          let uu____8077 =
            let uu____8088 =
              let uu____8093 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____8093) in
            (uu____8088, q) in
          FStar_Pervasives_Native.Some uu____8077
      | uu____8110 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8149 = lookup_qname env lid in
      match uu____8149 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____8174,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____8177;
              FStar_Syntax_Syntax.sigquals = uu____8178;
              FStar_Syntax_Syntax.sigmeta = uu____8179;
              FStar_Syntax_Syntax.sigattrs = uu____8180;_},FStar_Pervasives_Native.None
            ),uu____8181)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8230 ->
          let uu____8251 =
            let uu____8252 =
              let uu____8257 = name_not_found lid in
              (uu____8257, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8252 in
          FStar_Exn.raise uu____8251
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8274 = lookup_qname env lid in
      match uu____8274 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8299,uvs,t,uu____8302,uu____8303,uu____8304);
              FStar_Syntax_Syntax.sigrng = uu____8305;
              FStar_Syntax_Syntax.sigquals = uu____8306;
              FStar_Syntax_Syntax.sigmeta = uu____8307;
              FStar_Syntax_Syntax.sigattrs = uu____8308;_},FStar_Pervasives_Native.None
            ),uu____8309)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____8362 ->
          let uu____8383 =
            let uu____8384 =
              let uu____8389 = name_not_found lid in
              (uu____8389, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____8384 in
          FStar_Exn.raise uu____8383
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8408 = lookup_qname env lid in
      match uu____8408 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____8435,uu____8436,uu____8437,uu____8438,uu____8439,dcs);
              FStar_Syntax_Syntax.sigrng = uu____8441;
              FStar_Syntax_Syntax.sigquals = uu____8442;
              FStar_Syntax_Syntax.sigmeta = uu____8443;
              FStar_Syntax_Syntax.sigattrs = uu____8444;_},uu____8445),uu____8446)
          -> (true, dcs)
      | uu____8507 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____8538 = lookup_qname env lid in
      match uu____8538 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8559,uu____8560,uu____8561,l,uu____8563,uu____8564);
              FStar_Syntax_Syntax.sigrng = uu____8565;
              FStar_Syntax_Syntax.sigquals = uu____8566;
              FStar_Syntax_Syntax.sigmeta = uu____8567;
              FStar_Syntax_Syntax.sigattrs = uu____8568;_},uu____8569),uu____8570)
          -> l
      | uu____8625 ->
          let uu____8646 =
            let uu____8647 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____8647 in
          failwith uu____8646
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
        let uu____8684 = lookup_qname env lid in
        match uu____8684 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8712) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____8763,lbs),uu____8765) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____8793 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____8793
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____8825 -> FStar_Pervasives_Native.None)
        | uu____8830 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____8867 = lookup_qname env ftv in
      match uu____8867 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8891) ->
          let uu____8936 = effect_signature se in
          (match uu____8936 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____8957,t),r) ->
               let uu____8972 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____8972)
      | uu____8973 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____9002 = try_lookup_effect_lid env ftv in
      match uu____9002 with
      | FStar_Pervasives_Native.None  ->
          let uu____9005 =
            let uu____9006 =
              let uu____9011 = name_not_found ftv in
              (uu____9011, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____9006 in
          FStar_Exn.raise uu____9005
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
        let uu____9031 = lookup_qname env lid0 in
        match uu____9031 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____9062);
                FStar_Syntax_Syntax.sigrng = uu____9063;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____9065;
                FStar_Syntax_Syntax.sigattrs = uu____9066;_},FStar_Pervasives_Native.None
              ),uu____9067)
            ->
            let lid1 =
              let uu____9121 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____9121 in
            let uu____9122 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___109_9126  ->
                      match uu___109_9126 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____9127 -> false)) in
            if uu____9122
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____9141 =
                      let uu____9142 =
                        let uu____9143 = get_range env in
                        FStar_Range.string_of_range uu____9143 in
                      let uu____9144 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____9145 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____9142 uu____9144 uu____9145 in
                    failwith uu____9141) in
               match (binders, univs1) with
               | ([],uu____9152) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____9169,uu____9170::uu____9171::uu____9172) ->
                   let uu____9177 =
                     let uu____9178 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____9179 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____9178 uu____9179 in
                   failwith uu____9177
               | uu____9186 ->
                   let uu____9191 =
                     let uu____9196 =
                       let uu____9197 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____9197) in
                     inst_tscheme_with uu____9196 insts in
                   (match uu____9191 with
                    | (uu____9208,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____9211 =
                          let uu____9212 = FStar_Syntax_Subst.compress t1 in
                          uu____9212.FStar_Syntax_Syntax.n in
                        (match uu____9211 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____9259 -> failwith "Impossible")))
        | uu____9266 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____9308 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____9308 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____9321,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____9328 = find1 l2 in
            (match uu____9328 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____9335 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____9335 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____9339 = find1 l in
            (match uu____9339 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____9355 = lookup_qname env l1 in
      match uu____9355 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____9378;
              FStar_Syntax_Syntax.sigrng = uu____9379;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9381;
              FStar_Syntax_Syntax.sigattrs = uu____9382;_},uu____9383),uu____9384)
          -> q
      | uu____9435 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____9471 =
          let uu____9472 =
            let uu____9473 = FStar_Util.string_of_int i in
            let uu____9474 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____9473 uu____9474 in
          failwith uu____9472 in
        let uu____9475 = lookup_datacon env lid in
        match uu____9475 with
        | (uu____9480,t) ->
            let uu____9482 =
              let uu____9483 = FStar_Syntax_Subst.compress t in
              uu____9483.FStar_Syntax_Syntax.n in
            (match uu____9482 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9487) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____9518 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____9518
                      FStar_Pervasives_Native.fst)
             | uu____9527 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9536 = lookup_qname env l in
      match uu____9536 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9557,uu____9558,uu____9559);
              FStar_Syntax_Syntax.sigrng = uu____9560;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9562;
              FStar_Syntax_Syntax.sigattrs = uu____9563;_},uu____9564),uu____9565)
          ->
          FStar_Util.for_some
            (fun uu___110_9618  ->
               match uu___110_9618 with
               | FStar_Syntax_Syntax.Projector uu____9619 -> true
               | uu____9624 -> false) quals
      | uu____9625 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9654 = lookup_qname env lid in
      match uu____9654 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9675,uu____9676,uu____9677,uu____9678,uu____9679,uu____9680);
              FStar_Syntax_Syntax.sigrng = uu____9681;
              FStar_Syntax_Syntax.sigquals = uu____9682;
              FStar_Syntax_Syntax.sigmeta = uu____9683;
              FStar_Syntax_Syntax.sigattrs = uu____9684;_},uu____9685),uu____9686)
          -> true
      | uu____9741 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9770 = lookup_qname env lid in
      match uu____9770 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9791,uu____9792,uu____9793,uu____9794,uu____9795,uu____9796);
              FStar_Syntax_Syntax.sigrng = uu____9797;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9799;
              FStar_Syntax_Syntax.sigattrs = uu____9800;_},uu____9801),uu____9802)
          ->
          FStar_Util.for_some
            (fun uu___111_9863  ->
               match uu___111_9863 with
               | FStar_Syntax_Syntax.RecordType uu____9864 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____9873 -> true
               | uu____9882 -> false) quals
      | uu____9883 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9912 = lookup_qname env lid in
      match uu____9912 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____9933,uu____9934);
              FStar_Syntax_Syntax.sigrng = uu____9935;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9937;
              FStar_Syntax_Syntax.sigattrs = uu____9938;_},uu____9939),uu____9940)
          ->
          FStar_Util.for_some
            (fun uu___112_9997  ->
               match uu___112_9997 with
               | FStar_Syntax_Syntax.Action uu____9998 -> true
               | uu____9999 -> false) quals
      | uu____10000 -> false
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
      let uu____10032 =
        let uu____10033 = FStar_Syntax_Util.un_uinst head1 in
        uu____10033.FStar_Syntax_Syntax.n in
      match uu____10032 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____10037 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____10104 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____10120) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____10137 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____10144 ->
                 FStar_Pervasives_Native.Some true
             | uu____10161 -> FStar_Pervasives_Native.Some false) in
      let uu____10162 =
        let uu____10165 = lookup_qname env lid in
        FStar_Util.bind_opt uu____10165 mapper in
      match uu____10162 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____10213 = lookup_qname env lid in
      match uu____10213 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10234,uu____10235,tps,uu____10237,uu____10238,uu____10239);
              FStar_Syntax_Syntax.sigrng = uu____10240;
              FStar_Syntax_Syntax.sigquals = uu____10241;
              FStar_Syntax_Syntax.sigmeta = uu____10242;
              FStar_Syntax_Syntax.sigattrs = uu____10243;_},uu____10244),uu____10245)
          -> FStar_List.length tps
      | uu____10308 ->
          let uu____10329 =
            let uu____10330 =
              let uu____10335 = name_not_found lid in
              (uu____10335, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____10330 in
          FStar_Exn.raise uu____10329
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
           (fun uu____10377  ->
              match uu____10377 with
              | (d,uu____10385) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____10398 = effect_decl_opt env l in
      match uu____10398 with
      | FStar_Pervasives_Native.None  ->
          let uu____10413 =
            let uu____10414 =
              let uu____10419 = name_not_found l in
              (uu____10419, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____10414 in
          FStar_Exn.raise uu____10413
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
            (let uu____10485 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____10538  ->
                       match uu____10538 with
                       | (m1,m2,uu____10551,uu____10552,uu____10553) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____10485 with
             | FStar_Pervasives_Native.None  ->
                 let uu____10570 =
                   let uu____10571 =
                     let uu____10576 =
                       let uu____10577 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____10578 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____10577
                         uu____10578 in
                     (uu____10576, (env.range)) in
                   FStar_Errors.Error uu____10571 in
                 FStar_Exn.raise uu____10570
             | FStar_Pervasives_Native.Some
                 (uu____10585,uu____10586,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____10629 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____10629)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____10656 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____10682  ->
                match uu____10682 with
                | (d,uu____10688) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____10656 with
      | FStar_Pervasives_Native.None  ->
          let uu____10699 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____10699
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____10712 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____10712 with
           | (uu____10723,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____10733)::(wp,uu____10735)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____10771 -> failwith "Impossible"))
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
                 let uu____10820 = get_range env in
                 let uu____10821 =
                   let uu____10824 =
                     let uu____10825 =
                       let uu____10840 =
                         let uu____10843 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____10843] in
                       (null_wp, uu____10840) in
                     FStar_Syntax_Syntax.Tm_app uu____10825 in
                   FStar_Syntax_Syntax.mk uu____10824 in
                 uu____10821 FStar_Pervasives_Native.None uu____10820 in
               let uu____10849 =
                 let uu____10850 =
                   let uu____10859 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____10859] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____10850;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____10849)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___123_10870 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___123_10870.order);
              joins = (uu___123_10870.joins)
            } in
          let uu___124_10879 = env in
          {
            solver = (uu___124_10879.solver);
            range = (uu___124_10879.range);
            curmodule = (uu___124_10879.curmodule);
            gamma = (uu___124_10879.gamma);
            gamma_cache = (uu___124_10879.gamma_cache);
            modules = (uu___124_10879.modules);
            expected_typ = (uu___124_10879.expected_typ);
            sigtab = (uu___124_10879.sigtab);
            is_pattern = (uu___124_10879.is_pattern);
            instantiate_imp = (uu___124_10879.instantiate_imp);
            effects;
            generalize = (uu___124_10879.generalize);
            letrecs = (uu___124_10879.letrecs);
            top_level = (uu___124_10879.top_level);
            check_uvars = (uu___124_10879.check_uvars);
            use_eq = (uu___124_10879.use_eq);
            is_iface = (uu___124_10879.is_iface);
            admit = (uu___124_10879.admit);
            lax = (uu___124_10879.lax);
            lax_universes = (uu___124_10879.lax_universes);
            type_of = (uu___124_10879.type_of);
            universe_of = (uu___124_10879.universe_of);
            use_bv_sorts = (uu___124_10879.use_bv_sorts);
            qname_and_index = (uu___124_10879.qname_and_index);
            proof_ns = (uu___124_10879.proof_ns);
            synth = (uu___124_10879.synth);
            is_native_tactic = (uu___124_10879.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____10896 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____10896 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____10986 = (e1.mlift).mlift_wp t wp in
                              let uu____10987 = l1 t wp e in
                              l2 t uu____10986 uu____10987))
                | uu____10988 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____11027 = inst_tscheme lift_t in
            match uu____11027 with
            | (uu____11034,lift_t1) ->
                let uu____11036 =
                  let uu____11039 =
                    let uu____11040 =
                      let uu____11055 =
                        let uu____11058 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11059 =
                          let uu____11062 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____11062] in
                        uu____11058 :: uu____11059 in
                      (lift_t1, uu____11055) in
                    FStar_Syntax_Syntax.Tm_app uu____11040 in
                  FStar_Syntax_Syntax.mk uu____11039 in
                uu____11036 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____11103 = inst_tscheme lift_t in
            match uu____11103 with
            | (uu____11110,lift_t1) ->
                let uu____11112 =
                  let uu____11115 =
                    let uu____11116 =
                      let uu____11131 =
                        let uu____11134 = FStar_Syntax_Syntax.as_arg r in
                        let uu____11135 =
                          let uu____11138 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____11139 =
                            let uu____11142 = FStar_Syntax_Syntax.as_arg e in
                            [uu____11142] in
                          uu____11138 :: uu____11139 in
                        uu____11134 :: uu____11135 in
                      (lift_t1, uu____11131) in
                    FStar_Syntax_Syntax.Tm_app uu____11116 in
                  FStar_Syntax_Syntax.mk uu____11115 in
                uu____11112 FStar_Pervasives_Native.None
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
              let uu____11180 =
                let uu____11181 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____11181
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____11180 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____11185 =
              let uu____11186 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____11186 in
            let uu____11187 =
              let uu____11188 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____11206 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____11206) in
              FStar_Util.dflt "none" uu____11188 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____11185
              uu____11187 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____11232  ->
                    match uu____11232 with
                    | (e,uu____11240) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____11259 =
            match uu____11259 with
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
              let uu____11297 =
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
                                    (let uu____11318 =
                                       let uu____11327 =
                                         find_edge order1 (i, k) in
                                       let uu____11330 =
                                         find_edge order1 (k, j) in
                                       (uu____11327, uu____11330) in
                                     match uu____11318 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____11345 =
                                           compose_edges e1 e2 in
                                         [uu____11345]
                                     | uu____11346 -> []))))) in
              FStar_List.append order1 uu____11297 in
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
                   let uu____11375 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____11377 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____11377
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____11375
                   then
                     let uu____11382 =
                       let uu____11383 =
                         let uu____11388 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____11389 = get_range env in
                         (uu____11388, uu____11389) in
                       FStar_Errors.Error uu____11383 in
                     FStar_Exn.raise uu____11382
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
                                            let uu____11514 =
                                              let uu____11523 =
                                                find_edge order2 (i, k) in
                                              let uu____11526 =
                                                find_edge order2 (j, k) in
                                              (uu____11523, uu____11526) in
                                            match uu____11514 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____11568,uu____11569)
                                                     ->
                                                     let uu____11576 =
                                                       let uu____11581 =
                                                         let uu____11582 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____11582 in
                                                       let uu____11585 =
                                                         let uu____11586 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____11586 in
                                                       (uu____11581,
                                                         uu____11585) in
                                                     (match uu____11576 with
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
                                            | uu____11621 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___125_11694 = env.effects in
              { decls = (uu___125_11694.decls); order = order2; joins } in
            let uu___126_11695 = env in
            {
              solver = (uu___126_11695.solver);
              range = (uu___126_11695.range);
              curmodule = (uu___126_11695.curmodule);
              gamma = (uu___126_11695.gamma);
              gamma_cache = (uu___126_11695.gamma_cache);
              modules = (uu___126_11695.modules);
              expected_typ = (uu___126_11695.expected_typ);
              sigtab = (uu___126_11695.sigtab);
              is_pattern = (uu___126_11695.is_pattern);
              instantiate_imp = (uu___126_11695.instantiate_imp);
              effects;
              generalize = (uu___126_11695.generalize);
              letrecs = (uu___126_11695.letrecs);
              top_level = (uu___126_11695.top_level);
              check_uvars = (uu___126_11695.check_uvars);
              use_eq = (uu___126_11695.use_eq);
              is_iface = (uu___126_11695.is_iface);
              admit = (uu___126_11695.admit);
              lax = (uu___126_11695.lax);
              lax_universes = (uu___126_11695.lax_universes);
              type_of = (uu___126_11695.type_of);
              universe_of = (uu___126_11695.universe_of);
              use_bv_sorts = (uu___126_11695.use_bv_sorts);
              qname_and_index = (uu___126_11695.qname_and_index);
              proof_ns = (uu___126_11695.proof_ns);
              synth = (uu___126_11695.synth);
              is_native_tactic = (uu___126_11695.is_native_tactic)
            }))
      | uu____11696 -> env
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
        | uu____11722 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____11732 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____11732 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____11749 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____11749 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____11767 =
                     let uu____11768 =
                       let uu____11773 =
                         let uu____11774 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____11779 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____11786 =
                           let uu____11787 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____11787 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____11774 uu____11779 uu____11786 in
                       (uu____11773, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____11768 in
                   FStar_Exn.raise uu____11767)
                else ();
                (let inst1 =
                   let uu____11792 =
                     let uu____11801 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____11801 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____11818  ->
                        fun uu____11819  ->
                          match (uu____11818, uu____11819) with
                          | ((x,uu____11841),(t,uu____11843)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____11792 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____11862 =
                     let uu___127_11863 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___127_11863.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___127_11863.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___127_11863.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___127_11863.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____11862
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
          let uu____11888 =
            let uu____11897 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____11897 in
          match uu____11888 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____11922 =
                only_reifiable &&
                  (let uu____11924 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____11924) in
              if uu____11922
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____11940 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____11942 =
                       let uu____11955 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____11955) in
                     (match uu____11942 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____12001 =
                            let uu____12004 = get_range env in
                            let uu____12005 =
                              let uu____12008 =
                                let uu____12009 =
                                  let uu____12024 =
                                    let uu____12027 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____12027; wp] in
                                  (repr, uu____12024) in
                                FStar_Syntax_Syntax.Tm_app uu____12009 in
                              FStar_Syntax_Syntax.mk uu____12008 in
                            uu____12005 FStar_Pervasives_Native.None
                              uu____12004 in
                          FStar_Pervasives_Native.Some uu____12001))
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
          let uu____12079 =
            let uu____12080 =
              let uu____12085 =
                let uu____12086 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____12086 in
              let uu____12087 = get_range env in (uu____12085, uu____12087) in
            FStar_Errors.Error uu____12080 in
          FStar_Exn.raise uu____12079 in
        let uu____12088 = effect_repr_aux true env c u_c in
        match uu____12088 with
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
      | uu____12128 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____12137 =
        let uu____12138 = FStar_Syntax_Subst.compress t in
        uu____12138.FStar_Syntax_Syntax.n in
      match uu____12137 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____12141,c) ->
          is_reifiable_comp env c
      | uu____12159 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____12183)::uu____12184 -> x :: rest
        | (Binding_sig_inst uu____12193)::uu____12194 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12209 = push1 x rest1 in local :: uu____12209 in
      let uu___128_12212 = env in
      let uu____12213 = push1 s env.gamma in
      {
        solver = (uu___128_12212.solver);
        range = (uu___128_12212.range);
        curmodule = (uu___128_12212.curmodule);
        gamma = uu____12213;
        gamma_cache = (uu___128_12212.gamma_cache);
        modules = (uu___128_12212.modules);
        expected_typ = (uu___128_12212.expected_typ);
        sigtab = (uu___128_12212.sigtab);
        is_pattern = (uu___128_12212.is_pattern);
        instantiate_imp = (uu___128_12212.instantiate_imp);
        effects = (uu___128_12212.effects);
        generalize = (uu___128_12212.generalize);
        letrecs = (uu___128_12212.letrecs);
        top_level = (uu___128_12212.top_level);
        check_uvars = (uu___128_12212.check_uvars);
        use_eq = (uu___128_12212.use_eq);
        is_iface = (uu___128_12212.is_iface);
        admit = (uu___128_12212.admit);
        lax = (uu___128_12212.lax);
        lax_universes = (uu___128_12212.lax_universes);
        type_of = (uu___128_12212.type_of);
        universe_of = (uu___128_12212.universe_of);
        use_bv_sorts = (uu___128_12212.use_bv_sorts);
        qname_and_index = (uu___128_12212.qname_and_index);
        proof_ns = (uu___128_12212.proof_ns);
        synth = (uu___128_12212.synth);
        is_native_tactic = (uu___128_12212.is_native_tactic)
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
      let uu___129_12250 = env in
      {
        solver = (uu___129_12250.solver);
        range = (uu___129_12250.range);
        curmodule = (uu___129_12250.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___129_12250.gamma_cache);
        modules = (uu___129_12250.modules);
        expected_typ = (uu___129_12250.expected_typ);
        sigtab = (uu___129_12250.sigtab);
        is_pattern = (uu___129_12250.is_pattern);
        instantiate_imp = (uu___129_12250.instantiate_imp);
        effects = (uu___129_12250.effects);
        generalize = (uu___129_12250.generalize);
        letrecs = (uu___129_12250.letrecs);
        top_level = (uu___129_12250.top_level);
        check_uvars = (uu___129_12250.check_uvars);
        use_eq = (uu___129_12250.use_eq);
        is_iface = (uu___129_12250.is_iface);
        admit = (uu___129_12250.admit);
        lax = (uu___129_12250.lax);
        lax_universes = (uu___129_12250.lax_universes);
        type_of = (uu___129_12250.type_of);
        universe_of = (uu___129_12250.universe_of);
        use_bv_sorts = (uu___129_12250.use_bv_sorts);
        qname_and_index = (uu___129_12250.qname_and_index);
        proof_ns = (uu___129_12250.proof_ns);
        synth = (uu___129_12250.synth);
        is_native_tactic = (uu___129_12250.is_native_tactic)
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
            (let uu___130_12284 = env in
             {
               solver = (uu___130_12284.solver);
               range = (uu___130_12284.range);
               curmodule = (uu___130_12284.curmodule);
               gamma = rest;
               gamma_cache = (uu___130_12284.gamma_cache);
               modules = (uu___130_12284.modules);
               expected_typ = (uu___130_12284.expected_typ);
               sigtab = (uu___130_12284.sigtab);
               is_pattern = (uu___130_12284.is_pattern);
               instantiate_imp = (uu___130_12284.instantiate_imp);
               effects = (uu___130_12284.effects);
               generalize = (uu___130_12284.generalize);
               letrecs = (uu___130_12284.letrecs);
               top_level = (uu___130_12284.top_level);
               check_uvars = (uu___130_12284.check_uvars);
               use_eq = (uu___130_12284.use_eq);
               is_iface = (uu___130_12284.is_iface);
               admit = (uu___130_12284.admit);
               lax = (uu___130_12284.lax);
               lax_universes = (uu___130_12284.lax_universes);
               type_of = (uu___130_12284.type_of);
               universe_of = (uu___130_12284.universe_of);
               use_bv_sorts = (uu___130_12284.use_bv_sorts);
               qname_and_index = (uu___130_12284.qname_and_index);
               proof_ns = (uu___130_12284.proof_ns);
               synth = (uu___130_12284.synth);
               is_native_tactic = (uu___130_12284.is_native_tactic)
             }))
    | uu____12285 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12309  ->
             match uu____12309 with | (x,uu____12315) -> push_bv env1 x) env
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
            let uu___131_12345 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___131_12345.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___131_12345.FStar_Syntax_Syntax.index);
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
      (let uu___132_12380 = env in
       {
         solver = (uu___132_12380.solver);
         range = (uu___132_12380.range);
         curmodule = (uu___132_12380.curmodule);
         gamma = [];
         gamma_cache = (uu___132_12380.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___132_12380.sigtab);
         is_pattern = (uu___132_12380.is_pattern);
         instantiate_imp = (uu___132_12380.instantiate_imp);
         effects = (uu___132_12380.effects);
         generalize = (uu___132_12380.generalize);
         letrecs = (uu___132_12380.letrecs);
         top_level = (uu___132_12380.top_level);
         check_uvars = (uu___132_12380.check_uvars);
         use_eq = (uu___132_12380.use_eq);
         is_iface = (uu___132_12380.is_iface);
         admit = (uu___132_12380.admit);
         lax = (uu___132_12380.lax);
         lax_universes = (uu___132_12380.lax_universes);
         type_of = (uu___132_12380.type_of);
         universe_of = (uu___132_12380.universe_of);
         use_bv_sorts = (uu___132_12380.use_bv_sorts);
         qname_and_index = (uu___132_12380.qname_and_index);
         proof_ns = (uu___132_12380.proof_ns);
         synth = (uu___132_12380.synth);
         is_native_tactic = (uu___132_12380.is_native_tactic)
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
        let uu____12417 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____12417 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____12445 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____12445)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___133_12460 = env in
      {
        solver = (uu___133_12460.solver);
        range = (uu___133_12460.range);
        curmodule = (uu___133_12460.curmodule);
        gamma = (uu___133_12460.gamma);
        gamma_cache = (uu___133_12460.gamma_cache);
        modules = (uu___133_12460.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___133_12460.sigtab);
        is_pattern = (uu___133_12460.is_pattern);
        instantiate_imp = (uu___133_12460.instantiate_imp);
        effects = (uu___133_12460.effects);
        generalize = (uu___133_12460.generalize);
        letrecs = (uu___133_12460.letrecs);
        top_level = (uu___133_12460.top_level);
        check_uvars = (uu___133_12460.check_uvars);
        use_eq = false;
        is_iface = (uu___133_12460.is_iface);
        admit = (uu___133_12460.admit);
        lax = (uu___133_12460.lax);
        lax_universes = (uu___133_12460.lax_universes);
        type_of = (uu___133_12460.type_of);
        universe_of = (uu___133_12460.universe_of);
        use_bv_sorts = (uu___133_12460.use_bv_sorts);
        qname_and_index = (uu___133_12460.qname_and_index);
        proof_ns = (uu___133_12460.proof_ns);
        synth = (uu___133_12460.synth);
        is_native_tactic = (uu___133_12460.is_native_tactic)
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
    let uu____12486 = expected_typ env_ in
    ((let uu___134_12492 = env_ in
      {
        solver = (uu___134_12492.solver);
        range = (uu___134_12492.range);
        curmodule = (uu___134_12492.curmodule);
        gamma = (uu___134_12492.gamma);
        gamma_cache = (uu___134_12492.gamma_cache);
        modules = (uu___134_12492.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___134_12492.sigtab);
        is_pattern = (uu___134_12492.is_pattern);
        instantiate_imp = (uu___134_12492.instantiate_imp);
        effects = (uu___134_12492.effects);
        generalize = (uu___134_12492.generalize);
        letrecs = (uu___134_12492.letrecs);
        top_level = (uu___134_12492.top_level);
        check_uvars = (uu___134_12492.check_uvars);
        use_eq = false;
        is_iface = (uu___134_12492.is_iface);
        admit = (uu___134_12492.admit);
        lax = (uu___134_12492.lax);
        lax_universes = (uu___134_12492.lax_universes);
        type_of = (uu___134_12492.type_of);
        universe_of = (uu___134_12492.universe_of);
        use_bv_sorts = (uu___134_12492.use_bv_sorts);
        qname_and_index = (uu___134_12492.qname_and_index);
        proof_ns = (uu___134_12492.proof_ns);
        synth = (uu___134_12492.synth);
        is_native_tactic = (uu___134_12492.is_native_tactic)
      }), uu____12486)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____12507 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___113_12517  ->
                    match uu___113_12517 with
                    | Binding_sig (uu____12520,se) -> [se]
                    | uu____12526 -> [])) in
          FStar_All.pipe_right uu____12507 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___135_12533 = env in
       {
         solver = (uu___135_12533.solver);
         range = (uu___135_12533.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___135_12533.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___135_12533.expected_typ);
         sigtab = (uu___135_12533.sigtab);
         is_pattern = (uu___135_12533.is_pattern);
         instantiate_imp = (uu___135_12533.instantiate_imp);
         effects = (uu___135_12533.effects);
         generalize = (uu___135_12533.generalize);
         letrecs = (uu___135_12533.letrecs);
         top_level = (uu___135_12533.top_level);
         check_uvars = (uu___135_12533.check_uvars);
         use_eq = (uu___135_12533.use_eq);
         is_iface = (uu___135_12533.is_iface);
         admit = (uu___135_12533.admit);
         lax = (uu___135_12533.lax);
         lax_universes = (uu___135_12533.lax_universes);
         type_of = (uu___135_12533.type_of);
         universe_of = (uu___135_12533.universe_of);
         use_bv_sorts = (uu___135_12533.use_bv_sorts);
         qname_and_index = (uu___135_12533.qname_and_index);
         proof_ns = (uu___135_12533.proof_ns);
         synth = (uu___135_12533.synth);
         is_native_tactic = (uu___135_12533.is_native_tactic)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____12615)::tl1 -> aux out tl1
      | (Binding_lid (uu____12619,(uu____12620,t)))::tl1 ->
          let uu____12635 =
            let uu____12642 = FStar_Syntax_Free.uvars t in
            ext out uu____12642 in
          aux uu____12635 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12649;
            FStar_Syntax_Syntax.index = uu____12650;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12657 =
            let uu____12664 = FStar_Syntax_Free.uvars t in
            ext out uu____12664 in
          aux uu____12657 tl1
      | (Binding_sig uu____12671)::uu____12672 -> out
      | (Binding_sig_inst uu____12681)::uu____12682 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____12738)::tl1 -> aux out tl1
      | (Binding_univ uu____12750)::tl1 -> aux out tl1
      | (Binding_lid (uu____12754,(uu____12755,t)))::tl1 ->
          let uu____12770 =
            let uu____12773 = FStar_Syntax_Free.univs t in
            ext out uu____12773 in
          aux uu____12770 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12776;
            FStar_Syntax_Syntax.index = uu____12777;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12784 =
            let uu____12787 = FStar_Syntax_Free.univs t in
            ext out uu____12787 in
          aux uu____12784 tl1
      | (Binding_sig uu____12790)::uu____12791 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____12845)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____12861 = FStar_Util.set_add uname out in
          aux uu____12861 tl1
      | (Binding_lid (uu____12864,(uu____12865,t)))::tl1 ->
          let uu____12880 =
            let uu____12883 = FStar_Syntax_Free.univnames t in
            ext out uu____12883 in
          aux uu____12880 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12886;
            FStar_Syntax_Syntax.index = uu____12887;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12894 =
            let uu____12897 = FStar_Syntax_Free.univnames t in
            ext out uu____12897 in
          aux uu____12894 tl1
      | (Binding_sig uu____12900)::uu____12901 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___114_12929  ->
            match uu___114_12929 with
            | Binding_var x -> [x]
            | Binding_lid uu____12933 -> []
            | Binding_sig uu____12938 -> []
            | Binding_univ uu____12945 -> []
            | Binding_sig_inst uu____12946 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____12963 =
      let uu____12966 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____12966
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____12963 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____12991 =
      let uu____12992 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___115_13002  ->
                match uu___115_13002 with
                | Binding_var x ->
                    let uu____13004 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____13004
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____13007) ->
                    let uu____13008 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____13008
                | Binding_sig (ls,uu____13010) ->
                    let uu____13015 =
                      let uu____13016 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13016
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____13015
                | Binding_sig_inst (ls,uu____13026,uu____13027) ->
                    let uu____13032 =
                      let uu____13033 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____13033
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____13032)) in
      FStar_All.pipe_right uu____12992 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____12991 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____13052 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____13052
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____13080  ->
                 fun uu____13081  ->
                   match (uu____13080, uu____13081) with
                   | ((b1,uu____13099),(b2,uu____13101)) ->
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
           fun uu___116_13163  ->
             match uu___116_13163 with
             | Binding_sig (lids,uu____13169) -> FStar_List.append lids keys
             | uu____13174 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13180  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13216) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13235,uu____13236) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13273 = list_prefix p path1 in
            if uu____13273 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13287 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13287
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___136_13317 = e in
            {
              solver = (uu___136_13317.solver);
              range = (uu___136_13317.range);
              curmodule = (uu___136_13317.curmodule);
              gamma = (uu___136_13317.gamma);
              gamma_cache = (uu___136_13317.gamma_cache);
              modules = (uu___136_13317.modules);
              expected_typ = (uu___136_13317.expected_typ);
              sigtab = (uu___136_13317.sigtab);
              is_pattern = (uu___136_13317.is_pattern);
              instantiate_imp = (uu___136_13317.instantiate_imp);
              effects = (uu___136_13317.effects);
              generalize = (uu___136_13317.generalize);
              letrecs = (uu___136_13317.letrecs);
              top_level = (uu___136_13317.top_level);
              check_uvars = (uu___136_13317.check_uvars);
              use_eq = (uu___136_13317.use_eq);
              is_iface = (uu___136_13317.is_iface);
              admit = (uu___136_13317.admit);
              lax = (uu___136_13317.lax);
              lax_universes = (uu___136_13317.lax_universes);
              type_of = (uu___136_13317.type_of);
              universe_of = (uu___136_13317.universe_of);
              use_bv_sorts = (uu___136_13317.use_bv_sorts);
              qname_and_index = (uu___136_13317.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___136_13317.synth);
              is_native_tactic = (uu___136_13317.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___137_13344 = e in
    {
      solver = (uu___137_13344.solver);
      range = (uu___137_13344.range);
      curmodule = (uu___137_13344.curmodule);
      gamma = (uu___137_13344.gamma);
      gamma_cache = (uu___137_13344.gamma_cache);
      modules = (uu___137_13344.modules);
      expected_typ = (uu___137_13344.expected_typ);
      sigtab = (uu___137_13344.sigtab);
      is_pattern = (uu___137_13344.is_pattern);
      instantiate_imp = (uu___137_13344.instantiate_imp);
      effects = (uu___137_13344.effects);
      generalize = (uu___137_13344.generalize);
      letrecs = (uu___137_13344.letrecs);
      top_level = (uu___137_13344.top_level);
      check_uvars = (uu___137_13344.check_uvars);
      use_eq = (uu___137_13344.use_eq);
      is_iface = (uu___137_13344.is_iface);
      admit = (uu___137_13344.admit);
      lax = (uu___137_13344.lax);
      lax_universes = (uu___137_13344.lax_universes);
      type_of = (uu___137_13344.type_of);
      universe_of = (uu___137_13344.universe_of);
      use_bv_sorts = (uu___137_13344.use_bv_sorts);
      qname_and_index = (uu___137_13344.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___137_13344.synth);
      is_native_tactic = (uu___137_13344.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____13359::rest ->
        let uu___138_13363 = e in
        {
          solver = (uu___138_13363.solver);
          range = (uu___138_13363.range);
          curmodule = (uu___138_13363.curmodule);
          gamma = (uu___138_13363.gamma);
          gamma_cache = (uu___138_13363.gamma_cache);
          modules = (uu___138_13363.modules);
          expected_typ = (uu___138_13363.expected_typ);
          sigtab = (uu___138_13363.sigtab);
          is_pattern = (uu___138_13363.is_pattern);
          instantiate_imp = (uu___138_13363.instantiate_imp);
          effects = (uu___138_13363.effects);
          generalize = (uu___138_13363.generalize);
          letrecs = (uu___138_13363.letrecs);
          top_level = (uu___138_13363.top_level);
          check_uvars = (uu___138_13363.check_uvars);
          use_eq = (uu___138_13363.use_eq);
          is_iface = (uu___138_13363.is_iface);
          admit = (uu___138_13363.admit);
          lax = (uu___138_13363.lax);
          lax_universes = (uu___138_13363.lax_universes);
          type_of = (uu___138_13363.type_of);
          universe_of = (uu___138_13363.universe_of);
          use_bv_sorts = (uu___138_13363.use_bv_sorts);
          qname_and_index = (uu___138_13363.qname_and_index);
          proof_ns = rest;
          synth = (uu___138_13363.synth);
          is_native_tactic = (uu___138_13363.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___139_13376 = e in
      {
        solver = (uu___139_13376.solver);
        range = (uu___139_13376.range);
        curmodule = (uu___139_13376.curmodule);
        gamma = (uu___139_13376.gamma);
        gamma_cache = (uu___139_13376.gamma_cache);
        modules = (uu___139_13376.modules);
        expected_typ = (uu___139_13376.expected_typ);
        sigtab = (uu___139_13376.sigtab);
        is_pattern = (uu___139_13376.is_pattern);
        instantiate_imp = (uu___139_13376.instantiate_imp);
        effects = (uu___139_13376.effects);
        generalize = (uu___139_13376.generalize);
        letrecs = (uu___139_13376.letrecs);
        top_level = (uu___139_13376.top_level);
        check_uvars = (uu___139_13376.check_uvars);
        use_eq = (uu___139_13376.use_eq);
        is_iface = (uu___139_13376.is_iface);
        admit = (uu___139_13376.admit);
        lax = (uu___139_13376.lax);
        lax_universes = (uu___139_13376.lax_universes);
        type_of = (uu___139_13376.type_of);
        universe_of = (uu___139_13376.universe_of);
        use_bv_sorts = (uu___139_13376.use_bv_sorts);
        qname_and_index = (uu___139_13376.qname_and_index);
        proof_ns = ns;
        synth = (uu___139_13376.synth);
        is_native_tactic = (uu___139_13376.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____13405 =
        FStar_List.map
          (fun fpns  ->
             let uu____13427 =
               let uu____13428 =
                 let uu____13429 =
                   FStar_List.map
                     (fun uu____13441  ->
                        match uu____13441 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____13429 in
               Prims.strcat uu____13428 "]" in
             Prims.strcat "[" uu____13427) pns in
      FStar_String.concat ";" uu____13405 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____13457  -> ());
    push = (fun uu____13459  -> ());
    pop = (fun uu____13461  -> ());
    mark = (fun uu____13463  -> ());
    reset_mark = (fun uu____13465  -> ());
    commit_mark = (fun uu____13467  -> ());
    encode_modul = (fun uu____13470  -> fun uu____13471  -> ());
    encode_sig = (fun uu____13474  -> fun uu____13475  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____13481 =
             let uu____13488 = FStar_Options.peek () in (e, g, uu____13488) in
           [uu____13481]);
    solve = (fun uu____13504  -> fun uu____13505  -> fun uu____13506  -> ());
    is_trivial = (fun uu____13513  -> fun uu____13514  -> false);
    finish = (fun uu____13516  -> ());
    refresh = (fun uu____13518  -> ())
  }