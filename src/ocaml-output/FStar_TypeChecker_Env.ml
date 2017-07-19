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
let new_sigtab uu____4222 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____4233 =
  FStar_Util.smap_create (Prims.parse_int "100")
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
  fun uu____4463  ->
    let uu____4464 = FStar_ST.read query_indices in
    match uu____4464 with
    | [] -> failwith "Empty query indices!"
    | uu____4487 ->
        let uu____4496 =
          let uu____4505 =
            let uu____4512 = FStar_ST.read query_indices in
            FStar_List.hd uu____4512 in
          let uu____4535 = FStar_ST.read query_indices in uu____4505 ::
            uu____4535 in
        FStar_ST.write query_indices uu____4496
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____4569  ->
    let uu____4570 = FStar_ST.read query_indices in
    match uu____4570 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____4630  ->
    match uu____4630 with
    | (l,n1) ->
        let uu____4637 = FStar_ST.read query_indices in
        (match uu____4637 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____4694 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____4712  ->
    let uu____4713 = FStar_ST.read query_indices in FStar_List.hd uu____4713
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____4739  ->
    let uu____4740 = FStar_ST.read query_indices in
    match uu____4740 with
    | hd1::uu____4758::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____4806 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____4827 =
       let uu____4830 = FStar_ST.read stack in env :: uu____4830 in
     FStar_ST.write stack uu____4827);
    (let uu___115_4837 = env in
     let uu____4838 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____4841 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___115_4837.solver);
       range = (uu___115_4837.range);
       curmodule = (uu___115_4837.curmodule);
       gamma = (uu___115_4837.gamma);
       gamma_cache = uu____4838;
       modules = (uu___115_4837.modules);
       expected_typ = (uu___115_4837.expected_typ);
       sigtab = uu____4841;
       is_pattern = (uu___115_4837.is_pattern);
       instantiate_imp = (uu___115_4837.instantiate_imp);
       effects = (uu___115_4837.effects);
       generalize = (uu___115_4837.generalize);
       letrecs = (uu___115_4837.letrecs);
       top_level = (uu___115_4837.top_level);
       check_uvars = (uu___115_4837.check_uvars);
       use_eq = (uu___115_4837.use_eq);
       is_iface = (uu___115_4837.is_iface);
       admit = (uu___115_4837.admit);
       lax = (uu___115_4837.lax);
       lax_universes = (uu___115_4837.lax_universes);
       type_of = (uu___115_4837.type_of);
       universe_of = (uu___115_4837.universe_of);
       use_bv_sorts = (uu___115_4837.use_bv_sorts);
       qname_and_index = (uu___115_4837.qname_and_index);
       proof_ns = (uu___115_4837.proof_ns);
       synth = (uu___115_4837.synth);
       is_native_tactic = (uu___115_4837.is_native_tactic)
     })
let pop_stack: Prims.unit -> env =
  fun uu____4847  ->
    let uu____4848 = FStar_ST.read stack in
    match uu____4848 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____4860 -> failwith "Impossible: Too many pops"
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
    (let uu____4900 = pop_stack () in ());
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
        let uu____4928 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____4954  ->
                  match uu____4954 with
                  | (m,uu____4960) -> FStar_Ident.lid_equals l m)) in
        (match uu____4928 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___116_4967 = env in
               {
                 solver = (uu___116_4967.solver);
                 range = (uu___116_4967.range);
                 curmodule = (uu___116_4967.curmodule);
                 gamma = (uu___116_4967.gamma);
                 gamma_cache = (uu___116_4967.gamma_cache);
                 modules = (uu___116_4967.modules);
                 expected_typ = (uu___116_4967.expected_typ);
                 sigtab = (uu___116_4967.sigtab);
                 is_pattern = (uu___116_4967.is_pattern);
                 instantiate_imp = (uu___116_4967.instantiate_imp);
                 effects = (uu___116_4967.effects);
                 generalize = (uu___116_4967.generalize);
                 letrecs = (uu___116_4967.letrecs);
                 top_level = (uu___116_4967.top_level);
                 check_uvars = (uu___116_4967.check_uvars);
                 use_eq = (uu___116_4967.use_eq);
                 is_iface = (uu___116_4967.is_iface);
                 admit = (uu___116_4967.admit);
                 lax = (uu___116_4967.lax);
                 lax_universes = (uu___116_4967.lax_universes);
                 type_of = (uu___116_4967.type_of);
                 universe_of = (uu___116_4967.universe_of);
                 use_bv_sorts = (uu___116_4967.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___116_4967.proof_ns);
                 synth = (uu___116_4967.synth);
                 is_native_tactic = (uu___116_4967.is_native_tactic)
               }))
         | FStar_Pervasives_Native.Some (uu____4972,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___117_4980 = env in
               {
                 solver = (uu___117_4980.solver);
                 range = (uu___117_4980.range);
                 curmodule = (uu___117_4980.curmodule);
                 gamma = (uu___117_4980.gamma);
                 gamma_cache = (uu___117_4980.gamma_cache);
                 modules = (uu___117_4980.modules);
                 expected_typ = (uu___117_4980.expected_typ);
                 sigtab = (uu___117_4980.sigtab);
                 is_pattern = (uu___117_4980.is_pattern);
                 instantiate_imp = (uu___117_4980.instantiate_imp);
                 effects = (uu___117_4980.effects);
                 generalize = (uu___117_4980.generalize);
                 letrecs = (uu___117_4980.letrecs);
                 top_level = (uu___117_4980.top_level);
                 check_uvars = (uu___117_4980.check_uvars);
                 use_eq = (uu___117_4980.use_eq);
                 is_iface = (uu___117_4980.is_iface);
                 admit = (uu___117_4980.admit);
                 lax = (uu___117_4980.lax);
                 lax_universes = (uu___117_4980.lax_universes);
                 type_of = (uu___117_4980.type_of);
                 universe_of = (uu___117_4980.universe_of);
                 use_bv_sorts = (uu___117_4980.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___117_4980.proof_ns);
                 synth = (uu___117_4980.synth);
                 is_native_tactic = (uu___117_4980.is_native_tactic)
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
        (let uu___118_5002 = e in
         {
           solver = (uu___118_5002.solver);
           range = r;
           curmodule = (uu___118_5002.curmodule);
           gamma = (uu___118_5002.gamma);
           gamma_cache = (uu___118_5002.gamma_cache);
           modules = (uu___118_5002.modules);
           expected_typ = (uu___118_5002.expected_typ);
           sigtab = (uu___118_5002.sigtab);
           is_pattern = (uu___118_5002.is_pattern);
           instantiate_imp = (uu___118_5002.instantiate_imp);
           effects = (uu___118_5002.effects);
           generalize = (uu___118_5002.generalize);
           letrecs = (uu___118_5002.letrecs);
           top_level = (uu___118_5002.top_level);
           check_uvars = (uu___118_5002.check_uvars);
           use_eq = (uu___118_5002.use_eq);
           is_iface = (uu___118_5002.is_iface);
           admit = (uu___118_5002.admit);
           lax = (uu___118_5002.lax);
           lax_universes = (uu___118_5002.lax_universes);
           type_of = (uu___118_5002.type_of);
           universe_of = (uu___118_5002.universe_of);
           use_bv_sorts = (uu___118_5002.use_bv_sorts);
           qname_and_index = (uu___118_5002.qname_and_index);
           proof_ns = (uu___118_5002.proof_ns);
           synth = (uu___118_5002.synth);
           is_native_tactic = (uu___118_5002.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___119_5025 = env in
      {
        solver = (uu___119_5025.solver);
        range = (uu___119_5025.range);
        curmodule = lid;
        gamma = (uu___119_5025.gamma);
        gamma_cache = (uu___119_5025.gamma_cache);
        modules = (uu___119_5025.modules);
        expected_typ = (uu___119_5025.expected_typ);
        sigtab = (uu___119_5025.sigtab);
        is_pattern = (uu___119_5025.is_pattern);
        instantiate_imp = (uu___119_5025.instantiate_imp);
        effects = (uu___119_5025.effects);
        generalize = (uu___119_5025.generalize);
        letrecs = (uu___119_5025.letrecs);
        top_level = (uu___119_5025.top_level);
        check_uvars = (uu___119_5025.check_uvars);
        use_eq = (uu___119_5025.use_eq);
        is_iface = (uu___119_5025.is_iface);
        admit = (uu___119_5025.admit);
        lax = (uu___119_5025.lax);
        lax_universes = (uu___119_5025.lax_universes);
        type_of = (uu___119_5025.type_of);
        universe_of = (uu___119_5025.universe_of);
        use_bv_sorts = (uu___119_5025.use_bv_sorts);
        qname_and_index = (uu___119_5025.qname_and_index);
        proof_ns = (uu___119_5025.proof_ns);
        synth = (uu___119_5025.synth);
        is_native_tactic = (uu___119_5025.is_native_tactic)
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
    let uu____5056 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____5056
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____5060  ->
    let uu____5061 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____5061
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
      | ((formals,t),uu____5101) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____5125 = FStar_Syntax_Subst.subst vs t in (us, uu____5125)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___103_5133  ->
    match uu___103_5133 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____5157  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____5172 = inst_tscheme t in
      match uu____5172 with
      | (us,t1) ->
          let uu____5183 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____5183)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____5199  ->
          match uu____5199 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____5214 =
                         let uu____5215 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____5216 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____5217 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____5218 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____5215 uu____5216 uu____5217 uu____5218 in
                       failwith uu____5214)
                    else ();
                    (let uu____5220 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____5220))
               | uu____5227 ->
                   let uu____5228 =
                     let uu____5229 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____5229 in
                   failwith uu____5228)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____5234 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____5239 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____5244 -> false
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
             | ([],uu____5280) -> Maybe
             | (uu____5287,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____5306 -> No in
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
          let uu____5413 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____5413 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___104_5458  ->
                   match uu___104_5458 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____5501 =
                           let uu____5520 =
                             let uu____5535 = inst_tscheme t in
                             FStar_Util.Inl uu____5535 in
                           (uu____5520, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____5501
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____5601,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____5603);
                                     FStar_Syntax_Syntax.sigrng = uu____5604;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____5605;
                                     FStar_Syntax_Syntax.sigmeta = uu____5606;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____5607;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____5627 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____5627
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____5673 ->
                             FStar_Pervasives_Native.Some t
                         | uu____5680 -> cache t in
                       let uu____5681 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____5681 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____5756 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____5756 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____5842 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____5922 = find_in_sigtab env lid in
         match uu____5922 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6021) ->
          add_sigelts env ses
      | uu____6030 ->
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
            | uu____6044 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___105_6073  ->
           match uu___105_6073 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____6091 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____6126,lb::[]),uu____6128) ->
          let uu____6141 =
            let uu____6150 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____6159 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____6150, uu____6159) in
          FStar_Pervasives_Native.Some uu____6141
      | FStar_Syntax_Syntax.Sig_let ((uu____6172,lbs),uu____6174) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____6210 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____6222 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____6222
                   then
                     let uu____6233 =
                       let uu____6242 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____6251 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____6242, uu____6251) in
                     FStar_Pervasives_Native.Some uu____6233
                   else FStar_Pervasives_Native.None)
      | uu____6273 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____6307 =
          let uu____6316 =
            let uu____6321 =
              let uu____6322 =
                let uu____6325 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____6325 in
              ((ne.FStar_Syntax_Syntax.univs), uu____6322) in
            inst_tscheme uu____6321 in
          (uu____6316, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____6307
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____6345,uu____6346) ->
        let uu____6351 =
          let uu____6360 =
            let uu____6365 =
              let uu____6366 =
                let uu____6369 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____6369 in
              (us, uu____6366) in
            inst_tscheme uu____6365 in
          (uu____6360, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____6351
    | uu____6386 -> FStar_Pervasives_Native.None
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
      let mapper uu____6446 =
        match uu____6446 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____6542,uvs,t,uu____6545,uu____6546,uu____6547);
                    FStar_Syntax_Syntax.sigrng = uu____6548;
                    FStar_Syntax_Syntax.sigquals = uu____6549;
                    FStar_Syntax_Syntax.sigmeta = uu____6550;
                    FStar_Syntax_Syntax.sigattrs = uu____6551;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____6572 =
                   let uu____6581 = inst_tscheme (uvs, t) in
                   (uu____6581, rng) in
                 FStar_Pervasives_Native.Some uu____6572
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____6601;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____6603;
                    FStar_Syntax_Syntax.sigattrs = uu____6604;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____6621 =
                   let uu____6622 = in_cur_mod env l in uu____6622 = Yes in
                 if uu____6621
                 then
                   let uu____6633 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____6633
                    then
                      let uu____6646 =
                        let uu____6655 = inst_tscheme (uvs, t) in
                        (uu____6655, rng) in
                      FStar_Pervasives_Native.Some uu____6646
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____6682 =
                      let uu____6691 = inst_tscheme (uvs, t) in
                      (uu____6691, rng) in
                    FStar_Pervasives_Native.Some uu____6682)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____6712,uu____6713);
                    FStar_Syntax_Syntax.sigrng = uu____6714;
                    FStar_Syntax_Syntax.sigquals = uu____6715;
                    FStar_Syntax_Syntax.sigmeta = uu____6716;
                    FStar_Syntax_Syntax.sigattrs = uu____6717;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____6756 =
                        let uu____6765 = inst_tscheme (uvs, k) in
                        (uu____6765, rng) in
                      FStar_Pervasives_Native.Some uu____6756
                  | uu____6782 ->
                      let uu____6783 =
                        let uu____6792 =
                          let uu____6797 =
                            let uu____6798 =
                              let uu____6801 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____6801 in
                            (uvs, uu____6798) in
                          inst_tscheme uu____6797 in
                        (uu____6792, rng) in
                      FStar_Pervasives_Native.Some uu____6783)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____6822,uu____6823);
                    FStar_Syntax_Syntax.sigrng = uu____6824;
                    FStar_Syntax_Syntax.sigquals = uu____6825;
                    FStar_Syntax_Syntax.sigmeta = uu____6826;
                    FStar_Syntax_Syntax.sigattrs = uu____6827;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____6867 =
                        let uu____6876 = inst_tscheme_with (uvs, k) us in
                        (uu____6876, rng) in
                      FStar_Pervasives_Native.Some uu____6867
                  | uu____6893 ->
                      let uu____6894 =
                        let uu____6903 =
                          let uu____6908 =
                            let uu____6909 =
                              let uu____6912 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____6912 in
                            (uvs, uu____6909) in
                          inst_tscheme_with uu____6908 us in
                        (uu____6903, rng) in
                      FStar_Pervasives_Native.Some uu____6894)
             | FStar_Util.Inr se ->
                 let uu____6946 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____6967;
                        FStar_Syntax_Syntax.sigrng = uu____6968;
                        FStar_Syntax_Syntax.sigquals = uu____6969;
                        FStar_Syntax_Syntax.sigmeta = uu____6970;
                        FStar_Syntax_Syntax.sigattrs = uu____6971;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____6986 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____6946
                   (FStar_Util.map_option
                      (fun uu____7034  ->
                         match uu____7034 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____7065 =
        let uu____7076 = lookup_qname env lid in
        FStar_Util.bind_opt uu____7076 mapper in
      match uu____7065 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___120_7169 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___120_7169.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_7169.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____7196 = lookup_qname env l in
      match uu____7196 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____7235 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____7285 = try_lookup_bv env bv in
      match uu____7285 with
      | FStar_Pervasives_Native.None  ->
          let uu____7300 =
            let uu____7301 =
              let uu____7306 = variable_not_found bv in (uu____7306, bvr) in
            FStar_Errors.Error uu____7301 in
          raise uu____7300
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____7317 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____7318 = FStar_Range.set_use_range r bvr in
          (uu____7317, uu____7318)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____7337 = try_lookup_lid_aux env l in
      match uu____7337 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____7403 =
            let uu____7412 =
              let uu____7417 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____7417) in
            (uu____7412, r1) in
          FStar_Pervasives_Native.Some uu____7403
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____7446 = try_lookup_lid env l in
      match uu____7446 with
      | FStar_Pervasives_Native.None  ->
          let uu____7473 =
            let uu____7474 =
              let uu____7479 = name_not_found l in
              (uu____7479, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7474 in
          raise uu____7473
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___106_7517  ->
              match uu___106_7517 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____7519 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____7536 = lookup_qname env lid in
      match uu____7536 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____7565,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____7568;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____7570;
              FStar_Syntax_Syntax.sigattrs = uu____7571;_},FStar_Pervasives_Native.None
            ),uu____7572)
          ->
          let uu____7621 =
            let uu____7632 =
              let uu____7637 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____7637) in
            (uu____7632, q) in
          FStar_Pervasives_Native.Some uu____7621
      | uu____7654 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____7693 = lookup_qname env lid in
      match uu____7693 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____7718,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____7721;
              FStar_Syntax_Syntax.sigquals = uu____7722;
              FStar_Syntax_Syntax.sigmeta = uu____7723;
              FStar_Syntax_Syntax.sigattrs = uu____7724;_},FStar_Pervasives_Native.None
            ),uu____7725)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____7774 ->
          let uu____7795 =
            let uu____7796 =
              let uu____7801 = name_not_found lid in
              (uu____7801, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7796 in
          raise uu____7795
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____7818 = lookup_qname env lid in
      match uu____7818 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____7843,uvs,t,uu____7846,uu____7847,uu____7848);
              FStar_Syntax_Syntax.sigrng = uu____7849;
              FStar_Syntax_Syntax.sigquals = uu____7850;
              FStar_Syntax_Syntax.sigmeta = uu____7851;
              FStar_Syntax_Syntax.sigattrs = uu____7852;_},FStar_Pervasives_Native.None
            ),uu____7853)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____7906 ->
          let uu____7927 =
            let uu____7928 =
              let uu____7933 = name_not_found lid in
              (uu____7933, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7928 in
          raise uu____7927
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____7952 = lookup_qname env lid in
      match uu____7952 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____7979,uu____7980,uu____7981,uu____7982,uu____7983,dcs);
              FStar_Syntax_Syntax.sigrng = uu____7985;
              FStar_Syntax_Syntax.sigquals = uu____7986;
              FStar_Syntax_Syntax.sigmeta = uu____7987;
              FStar_Syntax_Syntax.sigattrs = uu____7988;_},uu____7989),uu____7990)
          -> (true, dcs)
      | uu____8051 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____8082 = lookup_qname env lid in
      match uu____8082 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8103,uu____8104,uu____8105,l,uu____8107,uu____8108);
              FStar_Syntax_Syntax.sigrng = uu____8109;
              FStar_Syntax_Syntax.sigquals = uu____8110;
              FStar_Syntax_Syntax.sigmeta = uu____8111;
              FStar_Syntax_Syntax.sigattrs = uu____8112;_},uu____8113),uu____8114)
          -> l
      | uu____8169 ->
          let uu____8190 =
            let uu____8191 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____8191 in
          failwith uu____8190
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
        let uu____8228 = lookup_qname env lid in
        match uu____8228 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8256) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____8307,lbs),uu____8309) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____8337 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____8337
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____8369 -> FStar_Pervasives_Native.None)
        | uu____8374 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____8411 = lookup_qname env ftv in
      match uu____8411 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8435) ->
          let uu____8480 = effect_signature se in
          (match uu____8480 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____8501,t),r) ->
               let uu____8516 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____8516)
      | uu____8517 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____8546 = try_lookup_effect_lid env ftv in
      match uu____8546 with
      | FStar_Pervasives_Native.None  ->
          let uu____8549 =
            let uu____8550 =
              let uu____8555 = name_not_found ftv in
              (uu____8555, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____8550 in
          raise uu____8549
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
        let uu____8575 = lookup_qname env lid0 in
        match uu____8575 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____8606);
                FStar_Syntax_Syntax.sigrng = uu____8607;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____8609;
                FStar_Syntax_Syntax.sigattrs = uu____8610;_},FStar_Pervasives_Native.None
              ),uu____8611)
            ->
            let lid1 =
              let uu____8665 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____8665 in
            let uu____8666 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___107_8670  ->
                      match uu___107_8670 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____8671 -> false)) in
            if uu____8666
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____8685 =
                      let uu____8686 =
                        let uu____8687 = get_range env in
                        FStar_Range.string_of_range uu____8687 in
                      let uu____8688 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____8689 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____8686 uu____8688 uu____8689 in
                    failwith uu____8685) in
               match (binders, univs1) with
               | ([],uu____8696) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____8713,uu____8714::uu____8715::uu____8716) ->
                   let uu____8721 =
                     let uu____8722 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____8723 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____8722 uu____8723 in
                   failwith uu____8721
               | uu____8730 ->
                   let uu____8735 =
                     let uu____8740 =
                       let uu____8741 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____8741) in
                     inst_tscheme_with uu____8740 insts in
                   (match uu____8735 with
                    | (uu____8752,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____8755 =
                          let uu____8756 = FStar_Syntax_Subst.compress t1 in
                          uu____8756.FStar_Syntax_Syntax.n in
                        (match uu____8755 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____8803 -> failwith "Impossible")))
        | uu____8810 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____8852 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____8852 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____8865,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____8872 = find1 l2 in
            (match uu____8872 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____8879 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____8879 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____8883 = find1 l in
            (match uu____8883 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____8899 = lookup_qname env l1 in
      match uu____8899 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____8922;
              FStar_Syntax_Syntax.sigrng = uu____8923;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____8925;
              FStar_Syntax_Syntax.sigattrs = uu____8926;_},uu____8927),uu____8928)
          -> q
      | uu____8979 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____9015 =
          let uu____9016 =
            let uu____9017 = FStar_Util.string_of_int i in
            let uu____9018 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____9017 uu____9018 in
          failwith uu____9016 in
        let uu____9019 = lookup_datacon env lid in
        match uu____9019 with
        | (uu____9024,t) ->
            let uu____9026 =
              let uu____9027 = FStar_Syntax_Subst.compress t in
              uu____9027.FStar_Syntax_Syntax.n in
            (match uu____9026 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9031) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____9062 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____9062
                      FStar_Pervasives_Native.fst)
             | uu____9071 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9080 = lookup_qname env l in
      match uu____9080 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9101,uu____9102,uu____9103);
              FStar_Syntax_Syntax.sigrng = uu____9104;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9106;
              FStar_Syntax_Syntax.sigattrs = uu____9107;_},uu____9108),uu____9109)
          ->
          FStar_Util.for_some
            (fun uu___108_9162  ->
               match uu___108_9162 with
               | FStar_Syntax_Syntax.Projector uu____9163 -> true
               | uu____9168 -> false) quals
      | uu____9169 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9198 = lookup_qname env lid in
      match uu____9198 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9219,uu____9220,uu____9221,uu____9222,uu____9223,uu____9224);
              FStar_Syntax_Syntax.sigrng = uu____9225;
              FStar_Syntax_Syntax.sigquals = uu____9226;
              FStar_Syntax_Syntax.sigmeta = uu____9227;
              FStar_Syntax_Syntax.sigattrs = uu____9228;_},uu____9229),uu____9230)
          -> true
      | uu____9285 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9314 = lookup_qname env lid in
      match uu____9314 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9335,uu____9336,uu____9337,uu____9338,uu____9339,uu____9340);
              FStar_Syntax_Syntax.sigrng = uu____9341;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9343;
              FStar_Syntax_Syntax.sigattrs = uu____9344;_},uu____9345),uu____9346)
          ->
          FStar_Util.for_some
            (fun uu___109_9407  ->
               match uu___109_9407 with
               | FStar_Syntax_Syntax.RecordType uu____9408 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____9417 -> true
               | uu____9426 -> false) quals
      | uu____9427 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9456 = lookup_qname env lid in
      match uu____9456 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____9477,uu____9478);
              FStar_Syntax_Syntax.sigrng = uu____9479;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9481;
              FStar_Syntax_Syntax.sigattrs = uu____9482;_},uu____9483),uu____9484)
          ->
          FStar_Util.for_some
            (fun uu___110_9541  ->
               match uu___110_9541 with
               | FStar_Syntax_Syntax.Action uu____9542 -> true
               | uu____9543 -> false) quals
      | uu____9544 -> false
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
      let uu____9576 =
        let uu____9577 = FStar_Syntax_Util.un_uinst head1 in
        uu____9577.FStar_Syntax_Syntax.n in
      match uu____9576 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____9581 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____9648 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____9664) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____9681 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____9688 ->
                 FStar_Pervasives_Native.Some true
             | uu____9705 -> FStar_Pervasives_Native.Some false) in
      let uu____9706 =
        let uu____9709 = lookup_qname env lid in
        FStar_Util.bind_opt uu____9709 mapper in
      match uu____9706 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____9757 = lookup_qname env lid in
      match uu____9757 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9778,uu____9779,tps,uu____9781,uu____9782,uu____9783);
              FStar_Syntax_Syntax.sigrng = uu____9784;
              FStar_Syntax_Syntax.sigquals = uu____9785;
              FStar_Syntax_Syntax.sigmeta = uu____9786;
              FStar_Syntax_Syntax.sigattrs = uu____9787;_},uu____9788),uu____9789)
          -> FStar_List.length tps
      | uu____9852 ->
          let uu____9873 =
            let uu____9874 =
              let uu____9879 = name_not_found lid in
              (uu____9879, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9874 in
          raise uu____9873
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
           (fun uu____9921  ->
              match uu____9921 with
              | (d,uu____9929) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____9942 = effect_decl_opt env l in
      match uu____9942 with
      | FStar_Pervasives_Native.None  ->
          let uu____9957 =
            let uu____9958 =
              let uu____9963 = name_not_found l in
              (uu____9963, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9958 in
          raise uu____9957
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some (fun t  -> fun wp  -> fun e  -> e))
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
            (let uu____10029 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____10082  ->
                       match uu____10082 with
                       | (m1,m2,uu____10095,uu____10096,uu____10097) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____10029 with
             | FStar_Pervasives_Native.None  ->
                 let uu____10114 =
                   let uu____10115 =
                     let uu____10120 =
                       let uu____10121 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____10122 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____10121
                         uu____10122 in
                     (uu____10120, (env.range)) in
                   FStar_Errors.Error uu____10115 in
                 raise uu____10114
             | FStar_Pervasives_Native.Some
                 (uu____10129,uu____10130,m3,j1,j2) -> (m3, j1, j2))
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
let wp_sig_aux decls m =
  let uu____10200 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____10226  ->
            match uu____10226 with
            | (d,uu____10232) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____10200 with
  | FStar_Pervasives_Native.None  ->
      let uu____10243 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____10243
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____10256 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____10256 with
       | (uu____10267,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____10277)::(wp,uu____10279)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____10315 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                FStar_Syntax_Syntax.syntax)
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
                 let uu____10364 = get_range env in
                 let uu____10365 =
                   let uu____10368 =
                     let uu____10369 =
                       let uu____10384 =
                         let uu____10387 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____10387] in
                       (null_wp, uu____10384) in
                     FStar_Syntax_Syntax.Tm_app uu____10369 in
                   FStar_Syntax_Syntax.mk uu____10368 in
                 uu____10365 FStar_Pervasives_Native.None uu____10364 in
               let uu____10393 =
                 let uu____10394 =
                   let uu____10403 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____10403] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____10394;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____10393)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_10414 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_10414.order);
              joins = (uu___121_10414.joins)
            } in
          let uu___122_10423 = env in
          {
            solver = (uu___122_10423.solver);
            range = (uu___122_10423.range);
            curmodule = (uu___122_10423.curmodule);
            gamma = (uu___122_10423.gamma);
            gamma_cache = (uu___122_10423.gamma_cache);
            modules = (uu___122_10423.modules);
            expected_typ = (uu___122_10423.expected_typ);
            sigtab = (uu___122_10423.sigtab);
            is_pattern = (uu___122_10423.is_pattern);
            instantiate_imp = (uu___122_10423.instantiate_imp);
            effects;
            generalize = (uu___122_10423.generalize);
            letrecs = (uu___122_10423.letrecs);
            top_level = (uu___122_10423.top_level);
            check_uvars = (uu___122_10423.check_uvars);
            use_eq = (uu___122_10423.use_eq);
            is_iface = (uu___122_10423.is_iface);
            admit = (uu___122_10423.admit);
            lax = (uu___122_10423.lax);
            lax_universes = (uu___122_10423.lax_universes);
            type_of = (uu___122_10423.type_of);
            universe_of = (uu___122_10423.universe_of);
            use_bv_sorts = (uu___122_10423.use_bv_sorts);
            qname_and_index = (uu___122_10423.qname_and_index);
            proof_ns = (uu___122_10423.proof_ns);
            synth = (uu___122_10423.synth);
            is_native_tactic = (uu___122_10423.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____10440 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____10440 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____10530 = (e1.mlift).mlift_wp t wp in
                              let uu____10531 = l1 t wp e in
                              l2 t uu____10530 uu____10531))
                | uu____10532 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____10571 = inst_tscheme lift_t in
            match uu____10571 with
            | (uu____10578,lift_t1) ->
                let uu____10580 =
                  let uu____10583 =
                    let uu____10584 =
                      let uu____10599 =
                        let uu____10602 = FStar_Syntax_Syntax.as_arg r in
                        let uu____10603 =
                          let uu____10606 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____10606] in
                        uu____10602 :: uu____10603 in
                      (lift_t1, uu____10599) in
                    FStar_Syntax_Syntax.Tm_app uu____10584 in
                  FStar_Syntax_Syntax.mk uu____10583 in
                uu____10580 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____10647 = inst_tscheme lift_t in
            match uu____10647 with
            | (uu____10654,lift_t1) ->
                let uu____10656 =
                  let uu____10659 =
                    let uu____10660 =
                      let uu____10675 =
                        let uu____10678 = FStar_Syntax_Syntax.as_arg r in
                        let uu____10679 =
                          let uu____10682 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____10683 =
                            let uu____10686 = FStar_Syntax_Syntax.as_arg e in
                            [uu____10686] in
                          uu____10682 :: uu____10683 in
                        uu____10678 :: uu____10679 in
                      (lift_t1, uu____10675) in
                    FStar_Syntax_Syntax.Tm_app uu____10660 in
                  FStar_Syntax_Syntax.mk uu____10659 in
                uu____10656 FStar_Pervasives_Native.None
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
              let uu____10724 =
                let uu____10725 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____10725
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____10724 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____10729 =
              let uu____10730 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____10730 in
            let uu____10731 =
              let uu____10732 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____10750 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____10750) in
              FStar_Util.dflt "none" uu____10732 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____10729
              uu____10731 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____10776  ->
                    match uu____10776 with
                    | (e,uu____10784) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____10803 =
            match uu____10803 with
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
              let uu____10841 =
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
                                    (let uu____10862 =
                                       let uu____10871 =
                                         find_edge order1 (i, k) in
                                       let uu____10874 =
                                         find_edge order1 (k, j) in
                                       (uu____10871, uu____10874) in
                                     match uu____10862 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____10889 =
                                           compose_edges e1 e2 in
                                         [uu____10889]
                                     | uu____10890 -> []))))) in
              FStar_List.append order1 uu____10841 in
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
                   let uu____10919 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____10921 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____10921
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____10919
                   then
                     let uu____10926 =
                       let uu____10927 =
                         let uu____10932 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____10933 = get_range env in
                         (uu____10932, uu____10933) in
                       FStar_Errors.Error uu____10927 in
                     raise uu____10926
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
                                            let uu____11058 =
                                              let uu____11067 =
                                                find_edge order2 (i, k) in
                                              let uu____11070 =
                                                find_edge order2 (j, k) in
                                              (uu____11067, uu____11070) in
                                            match uu____11058 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____11112,uu____11113)
                                                     ->
                                                     let uu____11120 =
                                                       let uu____11125 =
                                                         let uu____11126 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____11126 in
                                                       let uu____11129 =
                                                         let uu____11130 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____11130 in
                                                       (uu____11125,
                                                         uu____11129) in
                                                     (match uu____11120 with
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
                                            | uu____11165 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___123_11238 = env.effects in
              { decls = (uu___123_11238.decls); order = order2; joins } in
            let uu___124_11239 = env in
            {
              solver = (uu___124_11239.solver);
              range = (uu___124_11239.range);
              curmodule = (uu___124_11239.curmodule);
              gamma = (uu___124_11239.gamma);
              gamma_cache = (uu___124_11239.gamma_cache);
              modules = (uu___124_11239.modules);
              expected_typ = (uu___124_11239.expected_typ);
              sigtab = (uu___124_11239.sigtab);
              is_pattern = (uu___124_11239.is_pattern);
              instantiate_imp = (uu___124_11239.instantiate_imp);
              effects;
              generalize = (uu___124_11239.generalize);
              letrecs = (uu___124_11239.letrecs);
              top_level = (uu___124_11239.top_level);
              check_uvars = (uu___124_11239.check_uvars);
              use_eq = (uu___124_11239.use_eq);
              is_iface = (uu___124_11239.is_iface);
              admit = (uu___124_11239.admit);
              lax = (uu___124_11239.lax);
              lax_universes = (uu___124_11239.lax_universes);
              type_of = (uu___124_11239.type_of);
              universe_of = (uu___124_11239.universe_of);
              use_bv_sorts = (uu___124_11239.use_bv_sorts);
              qname_and_index = (uu___124_11239.qname_and_index);
              proof_ns = (uu___124_11239.proof_ns);
              synth = (uu___124_11239.synth);
              is_native_tactic = (uu___124_11239.is_native_tactic)
            }))
      | uu____11240 -> env
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
        | uu____11266 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____11276 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____11276 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____11293 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____11293 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____11311 =
                     let uu____11312 =
                       let uu____11317 =
                         let uu____11318 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____11323 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____11330 =
                           let uu____11331 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____11331 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____11318 uu____11323 uu____11330 in
                       (uu____11317, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____11312 in
                   raise uu____11311)
                else ();
                (let inst1 =
                   let uu____11336 =
                     let uu____11345 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____11345 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____11362  ->
                        fun uu____11363  ->
                          match (uu____11362, uu____11363) with
                          | ((x,uu____11385),(t,uu____11387)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____11336 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____11406 =
                     let uu___125_11407 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_11407.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_11407.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_11407.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_11407.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____11406
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
          let uu____11432 =
            let uu____11441 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____11441 in
          match uu____11432 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____11466 =
                only_reifiable &&
                  (let uu____11468 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____11468) in
              if uu____11466
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____11484 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____11486 =
                       let uu____11499 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____11499) in
                     (match uu____11486 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____11545 =
                            let uu____11548 = get_range env in
                            let uu____11549 =
                              let uu____11552 =
                                let uu____11553 =
                                  let uu____11568 =
                                    let uu____11571 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____11571; wp] in
                                  (repr, uu____11568) in
                                FStar_Syntax_Syntax.Tm_app uu____11553 in
                              FStar_Syntax_Syntax.mk uu____11552 in
                            uu____11549 FStar_Pervasives_Native.None
                              uu____11548 in
                          FStar_Pervasives_Native.Some uu____11545))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
          FStar_Pervasives_Native.option
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
          let uu____11623 =
            let uu____11624 =
              let uu____11629 =
                let uu____11630 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____11630 in
              let uu____11631 = get_range env in (uu____11629, uu____11631) in
            FStar_Errors.Error uu____11624 in
          raise uu____11623 in
        let uu____11632 = effect_repr_aux true env c u_c in
        match uu____11632 with
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
      | uu____11672 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____11681 =
        let uu____11682 = FStar_Syntax_Subst.compress t in
        uu____11682.FStar_Syntax_Syntax.n in
      match uu____11681 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____11685,c) ->
          is_reifiable_comp env c
      | uu____11703 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____11727)::uu____11728 -> x :: rest
        | (Binding_sig_inst uu____11737)::uu____11738 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____11753 = push1 x rest1 in local :: uu____11753 in
      let uu___126_11756 = env in
      let uu____11757 = push1 s env.gamma in
      {
        solver = (uu___126_11756.solver);
        range = (uu___126_11756.range);
        curmodule = (uu___126_11756.curmodule);
        gamma = uu____11757;
        gamma_cache = (uu___126_11756.gamma_cache);
        modules = (uu___126_11756.modules);
        expected_typ = (uu___126_11756.expected_typ);
        sigtab = (uu___126_11756.sigtab);
        is_pattern = (uu___126_11756.is_pattern);
        instantiate_imp = (uu___126_11756.instantiate_imp);
        effects = (uu___126_11756.effects);
        generalize = (uu___126_11756.generalize);
        letrecs = (uu___126_11756.letrecs);
        top_level = (uu___126_11756.top_level);
        check_uvars = (uu___126_11756.check_uvars);
        use_eq = (uu___126_11756.use_eq);
        is_iface = (uu___126_11756.is_iface);
        admit = (uu___126_11756.admit);
        lax = (uu___126_11756.lax);
        lax_universes = (uu___126_11756.lax_universes);
        type_of = (uu___126_11756.type_of);
        universe_of = (uu___126_11756.universe_of);
        use_bv_sorts = (uu___126_11756.use_bv_sorts);
        qname_and_index = (uu___126_11756.qname_and_index);
        proof_ns = (uu___126_11756.proof_ns);
        synth = (uu___126_11756.synth);
        is_native_tactic = (uu___126_11756.is_native_tactic)
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
      let uu___127_11794 = env in
      {
        solver = (uu___127_11794.solver);
        range = (uu___127_11794.range);
        curmodule = (uu___127_11794.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___127_11794.gamma_cache);
        modules = (uu___127_11794.modules);
        expected_typ = (uu___127_11794.expected_typ);
        sigtab = (uu___127_11794.sigtab);
        is_pattern = (uu___127_11794.is_pattern);
        instantiate_imp = (uu___127_11794.instantiate_imp);
        effects = (uu___127_11794.effects);
        generalize = (uu___127_11794.generalize);
        letrecs = (uu___127_11794.letrecs);
        top_level = (uu___127_11794.top_level);
        check_uvars = (uu___127_11794.check_uvars);
        use_eq = (uu___127_11794.use_eq);
        is_iface = (uu___127_11794.is_iface);
        admit = (uu___127_11794.admit);
        lax = (uu___127_11794.lax);
        lax_universes = (uu___127_11794.lax_universes);
        type_of = (uu___127_11794.type_of);
        universe_of = (uu___127_11794.universe_of);
        use_bv_sorts = (uu___127_11794.use_bv_sorts);
        qname_and_index = (uu___127_11794.qname_and_index);
        proof_ns = (uu___127_11794.proof_ns);
        synth = (uu___127_11794.synth);
        is_native_tactic = (uu___127_11794.is_native_tactic)
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
            (let uu___128_11828 = env in
             {
               solver = (uu___128_11828.solver);
               range = (uu___128_11828.range);
               curmodule = (uu___128_11828.curmodule);
               gamma = rest;
               gamma_cache = (uu___128_11828.gamma_cache);
               modules = (uu___128_11828.modules);
               expected_typ = (uu___128_11828.expected_typ);
               sigtab = (uu___128_11828.sigtab);
               is_pattern = (uu___128_11828.is_pattern);
               instantiate_imp = (uu___128_11828.instantiate_imp);
               effects = (uu___128_11828.effects);
               generalize = (uu___128_11828.generalize);
               letrecs = (uu___128_11828.letrecs);
               top_level = (uu___128_11828.top_level);
               check_uvars = (uu___128_11828.check_uvars);
               use_eq = (uu___128_11828.use_eq);
               is_iface = (uu___128_11828.is_iface);
               admit = (uu___128_11828.admit);
               lax = (uu___128_11828.lax);
               lax_universes = (uu___128_11828.lax_universes);
               type_of = (uu___128_11828.type_of);
               universe_of = (uu___128_11828.universe_of);
               use_bv_sorts = (uu___128_11828.use_bv_sorts);
               qname_and_index = (uu___128_11828.qname_and_index);
               proof_ns = (uu___128_11828.proof_ns);
               synth = (uu___128_11828.synth);
               is_native_tactic = (uu___128_11828.is_native_tactic)
             }))
    | uu____11829 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____11853  ->
             match uu____11853 with | (x,uu____11859) -> push_bv env1 x) env
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
            let uu___129_11889 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_11889.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_11889.FStar_Syntax_Syntax.index);
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
      (let uu___130_11924 = env in
       {
         solver = (uu___130_11924.solver);
         range = (uu___130_11924.range);
         curmodule = (uu___130_11924.curmodule);
         gamma = [];
         gamma_cache = (uu___130_11924.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_11924.sigtab);
         is_pattern = (uu___130_11924.is_pattern);
         instantiate_imp = (uu___130_11924.instantiate_imp);
         effects = (uu___130_11924.effects);
         generalize = (uu___130_11924.generalize);
         letrecs = (uu___130_11924.letrecs);
         top_level = (uu___130_11924.top_level);
         check_uvars = (uu___130_11924.check_uvars);
         use_eq = (uu___130_11924.use_eq);
         is_iface = (uu___130_11924.is_iface);
         admit = (uu___130_11924.admit);
         lax = (uu___130_11924.lax);
         lax_universes = (uu___130_11924.lax_universes);
         type_of = (uu___130_11924.type_of);
         universe_of = (uu___130_11924.universe_of);
         use_bv_sorts = (uu___130_11924.use_bv_sorts);
         qname_and_index = (uu___130_11924.qname_and_index);
         proof_ns = (uu___130_11924.proof_ns);
         synth = (uu___130_11924.synth);
         is_native_tactic = (uu___130_11924.is_native_tactic)
       })
let push_univ_vars: env_t -> FStar_Syntax_Syntax.univ_names -> env =
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
        let uu____11961 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____11961 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____11989 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____11989)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___131_12004 = env in
      {
        solver = (uu___131_12004.solver);
        range = (uu___131_12004.range);
        curmodule = (uu___131_12004.curmodule);
        gamma = (uu___131_12004.gamma);
        gamma_cache = (uu___131_12004.gamma_cache);
        modules = (uu___131_12004.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_12004.sigtab);
        is_pattern = (uu___131_12004.is_pattern);
        instantiate_imp = (uu___131_12004.instantiate_imp);
        effects = (uu___131_12004.effects);
        generalize = (uu___131_12004.generalize);
        letrecs = (uu___131_12004.letrecs);
        top_level = (uu___131_12004.top_level);
        check_uvars = (uu___131_12004.check_uvars);
        use_eq = false;
        is_iface = (uu___131_12004.is_iface);
        admit = (uu___131_12004.admit);
        lax = (uu___131_12004.lax);
        lax_universes = (uu___131_12004.lax_universes);
        type_of = (uu___131_12004.type_of);
        universe_of = (uu___131_12004.universe_of);
        use_bv_sorts = (uu___131_12004.use_bv_sorts);
        qname_and_index = (uu___131_12004.qname_and_index);
        proof_ns = (uu___131_12004.proof_ns);
        synth = (uu___131_12004.synth);
        is_native_tactic = (uu___131_12004.is_native_tactic)
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
    let uu____12030 = expected_typ env_ in
    ((let uu___132_12036 = env_ in
      {
        solver = (uu___132_12036.solver);
        range = (uu___132_12036.range);
        curmodule = (uu___132_12036.curmodule);
        gamma = (uu___132_12036.gamma);
        gamma_cache = (uu___132_12036.gamma_cache);
        modules = (uu___132_12036.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_12036.sigtab);
        is_pattern = (uu___132_12036.is_pattern);
        instantiate_imp = (uu___132_12036.instantiate_imp);
        effects = (uu___132_12036.effects);
        generalize = (uu___132_12036.generalize);
        letrecs = (uu___132_12036.letrecs);
        top_level = (uu___132_12036.top_level);
        check_uvars = (uu___132_12036.check_uvars);
        use_eq = false;
        is_iface = (uu___132_12036.is_iface);
        admit = (uu___132_12036.admit);
        lax = (uu___132_12036.lax);
        lax_universes = (uu___132_12036.lax_universes);
        type_of = (uu___132_12036.type_of);
        universe_of = (uu___132_12036.universe_of);
        use_bv_sorts = (uu___132_12036.use_bv_sorts);
        qname_and_index = (uu___132_12036.qname_and_index);
        proof_ns = (uu___132_12036.proof_ns);
        synth = (uu___132_12036.synth);
        is_native_tactic = (uu___132_12036.is_native_tactic)
      }), uu____12030)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____12051 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___111_12061  ->
                    match uu___111_12061 with
                    | Binding_sig (uu____12064,se) -> [se]
                    | uu____12070 -> [])) in
          FStar_All.pipe_right uu____12051 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___133_12077 = env in
       {
         solver = (uu___133_12077.solver);
         range = (uu___133_12077.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___133_12077.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_12077.expected_typ);
         sigtab = (uu___133_12077.sigtab);
         is_pattern = (uu___133_12077.is_pattern);
         instantiate_imp = (uu___133_12077.instantiate_imp);
         effects = (uu___133_12077.effects);
         generalize = (uu___133_12077.generalize);
         letrecs = (uu___133_12077.letrecs);
         top_level = (uu___133_12077.top_level);
         check_uvars = (uu___133_12077.check_uvars);
         use_eq = (uu___133_12077.use_eq);
         is_iface = (uu___133_12077.is_iface);
         admit = (uu___133_12077.admit);
         lax = (uu___133_12077.lax);
         lax_universes = (uu___133_12077.lax_universes);
         type_of = (uu___133_12077.type_of);
         universe_of = (uu___133_12077.universe_of);
         use_bv_sorts = (uu___133_12077.use_bv_sorts);
         qname_and_index = (uu___133_12077.qname_and_index);
         proof_ns = (uu___133_12077.proof_ns);
         synth = (uu___133_12077.synth);
         is_native_tactic = (uu___133_12077.is_native_tactic)
       })
let uvars_in_env:
  env ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____12159)::tl1 -> aux out tl1
      | (Binding_lid (uu____12163,(uu____12164,t)))::tl1 ->
          let uu____12179 =
            let uu____12186 = FStar_Syntax_Free.uvars t in
            ext out uu____12186 in
          aux uu____12179 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12193;
            FStar_Syntax_Syntax.index = uu____12194;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12201 =
            let uu____12208 = FStar_Syntax_Free.uvars t in
            ext out uu____12208 in
          aux uu____12201 tl1
      | (Binding_sig uu____12215)::uu____12216 -> out
      | (Binding_sig_inst uu____12225)::uu____12226 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____12282)::tl1 -> aux out tl1
      | (Binding_univ uu____12294)::tl1 -> aux out tl1
      | (Binding_lid (uu____12298,(uu____12299,t)))::tl1 ->
          let uu____12314 =
            let uu____12317 = FStar_Syntax_Free.univs t in
            ext out uu____12317 in
          aux uu____12314 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12320;
            FStar_Syntax_Syntax.index = uu____12321;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12328 =
            let uu____12331 = FStar_Syntax_Free.univs t in
            ext out uu____12331 in
          aux uu____12328 tl1
      | (Binding_sig uu____12334)::uu____12335 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____12389)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____12405 = FStar_Util.set_add uname out in
          aux uu____12405 tl1
      | (Binding_lid (uu____12408,(uu____12409,t)))::tl1 ->
          let uu____12424 =
            let uu____12427 = FStar_Syntax_Free.univnames t in
            ext out uu____12427 in
          aux uu____12424 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12430;
            FStar_Syntax_Syntax.index = uu____12431;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12438 =
            let uu____12441 = FStar_Syntax_Free.univnames t in
            ext out uu____12441 in
          aux uu____12438 tl1
      | (Binding_sig uu____12444)::uu____12445 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___112_12473  ->
            match uu___112_12473 with
            | Binding_var x -> [x]
            | Binding_lid uu____12477 -> []
            | Binding_sig uu____12482 -> []
            | Binding_univ uu____12489 -> []
            | Binding_sig_inst uu____12490 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____12507 =
      let uu____12510 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____12510
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____12507 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____12535 =
      let uu____12536 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___113_12546  ->
                match uu___113_12546 with
                | Binding_var x ->
                    let uu____12548 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____12548
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____12551) ->
                    let uu____12552 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____12552
                | Binding_sig (ls,uu____12554) ->
                    let uu____12559 =
                      let uu____12560 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____12560
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____12559
                | Binding_sig_inst (ls,uu____12570,uu____12571) ->
                    let uu____12576 =
                      let uu____12577 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____12577
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____12576)) in
      FStar_All.pipe_right uu____12536 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____12535 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____12596 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____12596
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____12624  ->
                 fun uu____12625  ->
                   match (uu____12624, uu____12625) with
                   | ((b1,uu____12643),(b2,uu____12645)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___114_12707  ->
             match uu___114_12707 with
             | Binding_sig (lids,uu____12713) -> FStar_List.append lids keys
             | uu____12718 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____12724  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____12760) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____12779,uu____12780) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____12817 = list_prefix p path1 in
            if uu____12817 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____12831 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____12831
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___134_12861 = e in
            {
              solver = (uu___134_12861.solver);
              range = (uu___134_12861.range);
              curmodule = (uu___134_12861.curmodule);
              gamma = (uu___134_12861.gamma);
              gamma_cache = (uu___134_12861.gamma_cache);
              modules = (uu___134_12861.modules);
              expected_typ = (uu___134_12861.expected_typ);
              sigtab = (uu___134_12861.sigtab);
              is_pattern = (uu___134_12861.is_pattern);
              instantiate_imp = (uu___134_12861.instantiate_imp);
              effects = (uu___134_12861.effects);
              generalize = (uu___134_12861.generalize);
              letrecs = (uu___134_12861.letrecs);
              top_level = (uu___134_12861.top_level);
              check_uvars = (uu___134_12861.check_uvars);
              use_eq = (uu___134_12861.use_eq);
              is_iface = (uu___134_12861.is_iface);
              admit = (uu___134_12861.admit);
              lax = (uu___134_12861.lax);
              lax_universes = (uu___134_12861.lax_universes);
              type_of = (uu___134_12861.type_of);
              universe_of = (uu___134_12861.universe_of);
              use_bv_sorts = (uu___134_12861.use_bv_sorts);
              qname_and_index = (uu___134_12861.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___134_12861.synth);
              is_native_tactic = (uu___134_12861.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___135_12888 = e in
    {
      solver = (uu___135_12888.solver);
      range = (uu___135_12888.range);
      curmodule = (uu___135_12888.curmodule);
      gamma = (uu___135_12888.gamma);
      gamma_cache = (uu___135_12888.gamma_cache);
      modules = (uu___135_12888.modules);
      expected_typ = (uu___135_12888.expected_typ);
      sigtab = (uu___135_12888.sigtab);
      is_pattern = (uu___135_12888.is_pattern);
      instantiate_imp = (uu___135_12888.instantiate_imp);
      effects = (uu___135_12888.effects);
      generalize = (uu___135_12888.generalize);
      letrecs = (uu___135_12888.letrecs);
      top_level = (uu___135_12888.top_level);
      check_uvars = (uu___135_12888.check_uvars);
      use_eq = (uu___135_12888.use_eq);
      is_iface = (uu___135_12888.is_iface);
      admit = (uu___135_12888.admit);
      lax = (uu___135_12888.lax);
      lax_universes = (uu___135_12888.lax_universes);
      type_of = (uu___135_12888.type_of);
      universe_of = (uu___135_12888.universe_of);
      use_bv_sorts = (uu___135_12888.use_bv_sorts);
      qname_and_index = (uu___135_12888.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___135_12888.synth);
      is_native_tactic = (uu___135_12888.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____12903::rest ->
        let uu___136_12907 = e in
        {
          solver = (uu___136_12907.solver);
          range = (uu___136_12907.range);
          curmodule = (uu___136_12907.curmodule);
          gamma = (uu___136_12907.gamma);
          gamma_cache = (uu___136_12907.gamma_cache);
          modules = (uu___136_12907.modules);
          expected_typ = (uu___136_12907.expected_typ);
          sigtab = (uu___136_12907.sigtab);
          is_pattern = (uu___136_12907.is_pattern);
          instantiate_imp = (uu___136_12907.instantiate_imp);
          effects = (uu___136_12907.effects);
          generalize = (uu___136_12907.generalize);
          letrecs = (uu___136_12907.letrecs);
          top_level = (uu___136_12907.top_level);
          check_uvars = (uu___136_12907.check_uvars);
          use_eq = (uu___136_12907.use_eq);
          is_iface = (uu___136_12907.is_iface);
          admit = (uu___136_12907.admit);
          lax = (uu___136_12907.lax);
          lax_universes = (uu___136_12907.lax_universes);
          type_of = (uu___136_12907.type_of);
          universe_of = (uu___136_12907.universe_of);
          use_bv_sorts = (uu___136_12907.use_bv_sorts);
          qname_and_index = (uu___136_12907.qname_and_index);
          proof_ns = rest;
          synth = (uu___136_12907.synth);
          is_native_tactic = (uu___136_12907.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___137_12920 = e in
      {
        solver = (uu___137_12920.solver);
        range = (uu___137_12920.range);
        curmodule = (uu___137_12920.curmodule);
        gamma = (uu___137_12920.gamma);
        gamma_cache = (uu___137_12920.gamma_cache);
        modules = (uu___137_12920.modules);
        expected_typ = (uu___137_12920.expected_typ);
        sigtab = (uu___137_12920.sigtab);
        is_pattern = (uu___137_12920.is_pattern);
        instantiate_imp = (uu___137_12920.instantiate_imp);
        effects = (uu___137_12920.effects);
        generalize = (uu___137_12920.generalize);
        letrecs = (uu___137_12920.letrecs);
        top_level = (uu___137_12920.top_level);
        check_uvars = (uu___137_12920.check_uvars);
        use_eq = (uu___137_12920.use_eq);
        is_iface = (uu___137_12920.is_iface);
        admit = (uu___137_12920.admit);
        lax = (uu___137_12920.lax);
        lax_universes = (uu___137_12920.lax_universes);
        type_of = (uu___137_12920.type_of);
        universe_of = (uu___137_12920.universe_of);
        use_bv_sorts = (uu___137_12920.use_bv_sorts);
        qname_and_index = (uu___137_12920.qname_and_index);
        proof_ns = ns;
        synth = (uu___137_12920.synth);
        is_native_tactic = (uu___137_12920.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____12949 =
        FStar_List.map
          (fun fpns  ->
             let uu____12971 =
               let uu____12972 =
                 let uu____12973 =
                   FStar_List.map
                     (fun uu____12985  ->
                        match uu____12985 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____12973 in
               Prims.strcat uu____12972 "]" in
             Prims.strcat "[" uu____12971) pns in
      FStar_String.concat ";" uu____12949 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____13001  -> ());
    push = (fun uu____13003  -> ());
    pop = (fun uu____13005  -> ());
    mark = (fun uu____13007  -> ());
    reset_mark = (fun uu____13009  -> ());
    commit_mark = (fun uu____13011  -> ());
    encode_modul = (fun uu____13014  -> fun uu____13015  -> ());
    encode_sig = (fun uu____13018  -> fun uu____13019  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____13025 =
             let uu____13032 = FStar_Options.peek () in (e, g, uu____13032) in
           [uu____13025]);
    solve = (fun uu____13048  -> fun uu____13049  -> fun uu____13050  -> ());
    is_trivial = (fun uu____13057  -> fun uu____13058  -> false);
    finish = (fun uu____13060  -> ());
    refresh = (fun uu____13062  -> ())
  }