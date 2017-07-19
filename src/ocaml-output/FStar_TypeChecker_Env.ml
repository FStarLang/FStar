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
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___105_6075  ->
           match uu___105_6075 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____6099 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____6136,lb::[]),uu____6138) ->
          let uu____6151 =
            let uu____6160 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____6171 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____6160, uu____6171) in
          FStar_Pervasives_Native.Some uu____6151
      | FStar_Syntax_Syntax.Sig_let ((uu____6184,lbs),uu____6186) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____6222 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____6234 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____6234
                   then
                     let uu____6245 =
                       let uu____6254 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____6265 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____6254, uu____6265) in
                     FStar_Pervasives_Native.Some uu____6245
                   else FStar_Pervasives_Native.None)
      | uu____6287 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____6321 =
          let uu____6330 =
            let uu____6335 =
              let uu____6336 =
                let uu____6341 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____6341 in
              ((ne.FStar_Syntax_Syntax.univs), uu____6336) in
            inst_tscheme uu____6335 in
          (uu____6330, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____6321
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____6365,uu____6366) ->
        let uu____6371 =
          let uu____6380 =
            let uu____6385 =
              let uu____6386 =
                let uu____6391 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____6391 in
              (us, uu____6386) in
            inst_tscheme uu____6385 in
          (uu____6380, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____6371
    | uu____6412 -> FStar_Pervasives_Native.None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____6474 =
        match uu____6474 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____6570,uvs,t,uu____6573,uu____6574,uu____6575);
                    FStar_Syntax_Syntax.sigrng = uu____6576;
                    FStar_Syntax_Syntax.sigquals = uu____6577;
                    FStar_Syntax_Syntax.sigmeta = uu____6578;
                    FStar_Syntax_Syntax.sigattrs = uu____6579;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____6600 =
                   let uu____6609 = inst_tscheme (uvs, t) in
                   (uu____6609, rng) in
                 FStar_Pervasives_Native.Some uu____6600
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____6629;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____6631;
                    FStar_Syntax_Syntax.sigattrs = uu____6632;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____6649 =
                   let uu____6650 = in_cur_mod env l in uu____6650 = Yes in
                 if uu____6649
                 then
                   let uu____6661 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____6661
                    then
                      let uu____6674 =
                        let uu____6683 = inst_tscheme (uvs, t) in
                        (uu____6683, rng) in
                      FStar_Pervasives_Native.Some uu____6674
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____6710 =
                      let uu____6719 = inst_tscheme (uvs, t) in
                      (uu____6719, rng) in
                    FStar_Pervasives_Native.Some uu____6710)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____6740,uu____6741);
                    FStar_Syntax_Syntax.sigrng = uu____6742;
                    FStar_Syntax_Syntax.sigquals = uu____6743;
                    FStar_Syntax_Syntax.sigmeta = uu____6744;
                    FStar_Syntax_Syntax.sigattrs = uu____6745;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____6784 =
                        let uu____6793 = inst_tscheme (uvs, k) in
                        (uu____6793, rng) in
                      FStar_Pervasives_Native.Some uu____6784
                  | uu____6810 ->
                      let uu____6811 =
                        let uu____6820 =
                          let uu____6825 =
                            let uu____6826 =
                              let uu____6831 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____6831 in
                            (uvs, uu____6826) in
                          inst_tscheme uu____6825 in
                        (uu____6820, rng) in
                      FStar_Pervasives_Native.Some uu____6811)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____6856,uu____6857);
                    FStar_Syntax_Syntax.sigrng = uu____6858;
                    FStar_Syntax_Syntax.sigquals = uu____6859;
                    FStar_Syntax_Syntax.sigmeta = uu____6860;
                    FStar_Syntax_Syntax.sigattrs = uu____6861;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____6901 =
                        let uu____6910 = inst_tscheme_with (uvs, k) us in
                        (uu____6910, rng) in
                      FStar_Pervasives_Native.Some uu____6901
                  | uu____6927 ->
                      let uu____6928 =
                        let uu____6937 =
                          let uu____6942 =
                            let uu____6943 =
                              let uu____6948 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____6948 in
                            (uvs, uu____6943) in
                          inst_tscheme_with uu____6942 us in
                        (uu____6937, rng) in
                      FStar_Pervasives_Native.Some uu____6928)
             | FStar_Util.Inr se ->
                 let uu____6986 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____7007;
                        FStar_Syntax_Syntax.sigrng = uu____7008;
                        FStar_Syntax_Syntax.sigquals = uu____7009;
                        FStar_Syntax_Syntax.sigmeta = uu____7010;
                        FStar_Syntax_Syntax.sigattrs = uu____7011;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____7026 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____6986
                   (FStar_Util.map_option
                      (fun uu____7074  ->
                         match uu____7074 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____7105 =
        let uu____7116 = lookup_qname env lid in
        FStar_Util.bind_opt uu____7116 mapper in
      match uu____7105 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___120_7217 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___120_7217.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___120_7217.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_7217.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____7246 = lookup_qname env l in
      match uu____7246 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____7285 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____7335 = try_lookup_bv env bv in
      match uu____7335 with
      | FStar_Pervasives_Native.None  ->
          let uu____7350 =
            let uu____7351 =
              let uu____7356 = variable_not_found bv in (uu____7356, bvr) in
            FStar_Errors.Error uu____7351 in
          raise uu____7350
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____7367 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____7368 = FStar_Range.set_use_range r bvr in
          (uu____7367, uu____7368)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____7387 = try_lookup_lid_aux env l in
      match uu____7387 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____7465 =
            let uu____7474 =
              let uu____7479 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____7479) in
            (uu____7474, r1) in
          FStar_Pervasives_Native.Some uu____7465
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____7508 = try_lookup_lid env l in
      match uu____7508 with
      | FStar_Pervasives_Native.None  ->
          let uu____7535 =
            let uu____7536 =
              let uu____7541 = name_not_found l in
              (uu____7541, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7536 in
          raise uu____7535
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___106_7579  ->
              match uu___106_7579 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____7581 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____7598 = lookup_qname env lid in
      match uu____7598 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____7627,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____7630;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____7632;
              FStar_Syntax_Syntax.sigattrs = uu____7633;_},FStar_Pervasives_Native.None
            ),uu____7634)
          ->
          let uu____7683 =
            let uu____7694 =
              let uu____7699 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____7699) in
            (uu____7694, q) in
          FStar_Pervasives_Native.Some uu____7683
      | uu____7716 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____7755 = lookup_qname env lid in
      match uu____7755 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____7780,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____7783;
              FStar_Syntax_Syntax.sigquals = uu____7784;
              FStar_Syntax_Syntax.sigmeta = uu____7785;
              FStar_Syntax_Syntax.sigattrs = uu____7786;_},FStar_Pervasives_Native.None
            ),uu____7787)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____7836 ->
          let uu____7857 =
            let uu____7858 =
              let uu____7863 = name_not_found lid in
              (uu____7863, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7858 in
          raise uu____7857
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____7880 = lookup_qname env lid in
      match uu____7880 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____7905,uvs,t,uu____7908,uu____7909,uu____7910);
              FStar_Syntax_Syntax.sigrng = uu____7911;
              FStar_Syntax_Syntax.sigquals = uu____7912;
              FStar_Syntax_Syntax.sigmeta = uu____7913;
              FStar_Syntax_Syntax.sigattrs = uu____7914;_},FStar_Pervasives_Native.None
            ),uu____7915)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____7968 ->
          let uu____7989 =
            let uu____7990 =
              let uu____7995 = name_not_found lid in
              (uu____7995, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7990 in
          raise uu____7989
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____8014 = lookup_qname env lid in
      match uu____8014 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____8041,uu____8042,uu____8043,uu____8044,uu____8045,dcs);
              FStar_Syntax_Syntax.sigrng = uu____8047;
              FStar_Syntax_Syntax.sigquals = uu____8048;
              FStar_Syntax_Syntax.sigmeta = uu____8049;
              FStar_Syntax_Syntax.sigattrs = uu____8050;_},uu____8051),uu____8052)
          -> (true, dcs)
      | uu____8113 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____8144 = lookup_qname env lid in
      match uu____8144 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____8165,uu____8166,uu____8167,l,uu____8169,uu____8170);
              FStar_Syntax_Syntax.sigrng = uu____8171;
              FStar_Syntax_Syntax.sigquals = uu____8172;
              FStar_Syntax_Syntax.sigmeta = uu____8173;
              FStar_Syntax_Syntax.sigattrs = uu____8174;_},uu____8175),uu____8176)
          -> l
      | uu____8231 ->
          let uu____8252 =
            let uu____8253 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____8253 in
          failwith uu____8252
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
        let uu____8290 = lookup_qname env lid in
        match uu____8290 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8318) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____8369,lbs),uu____8371) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____8401 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____8401
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____8441 -> FStar_Pervasives_Native.None)
        | uu____8446 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____8483 = lookup_qname env ftv in
      match uu____8483 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____8507) ->
          let uu____8552 = effect_signature se in
          (match uu____8552 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____8573,t),r) ->
               let uu____8588 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____8588)
      | uu____8589 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____8618 = try_lookup_effect_lid env ftv in
      match uu____8618 with
      | FStar_Pervasives_Native.None  ->
          let uu____8621 =
            let uu____8622 =
              let uu____8627 = name_not_found ftv in
              (uu____8627, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____8622 in
          raise uu____8621
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
        let uu____8647 = lookup_qname env lid0 in
        match uu____8647 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____8678);
                FStar_Syntax_Syntax.sigrng = uu____8679;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____8681;
                FStar_Syntax_Syntax.sigattrs = uu____8682;_},FStar_Pervasives_Native.None
              ),uu____8683)
            ->
            let lid1 =
              let uu____8737 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____8737 in
            let uu____8738 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___107_8742  ->
                      match uu___107_8742 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____8743 -> false)) in
            if uu____8738
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____8757 =
                      let uu____8758 =
                        let uu____8759 = get_range env in
                        FStar_Range.string_of_range uu____8759 in
                      let uu____8760 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____8761 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____8758 uu____8760 uu____8761 in
                    failwith uu____8757) in
               match (binders, univs1) with
               | ([],uu____8768) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____8785,uu____8786::uu____8787::uu____8788) ->
                   let uu____8793 =
                     let uu____8794 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____8795 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____8794 uu____8795 in
                   failwith uu____8793
               | uu____8802 ->
                   let uu____8807 =
                     let uu____8812 =
                       let uu____8813 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____8813) in
                     inst_tscheme_with uu____8812 insts in
                   (match uu____8807 with
                    | (uu____8828,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____8831 =
                          let uu____8832 = FStar_Syntax_Subst.compress t1 in
                          uu____8832.FStar_Syntax_Syntax.n in
                        (match uu____8831 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____8889 -> failwith "Impossible")))
        | uu____8896 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____8938 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____8938 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____8951,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____8958 = find1 l2 in
            (match uu____8958 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____8965 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____8965 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____8969 = find1 l in
            (match uu____8969 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____8985 = lookup_qname env l1 in
      match uu____8985 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____9008;
              FStar_Syntax_Syntax.sigrng = uu____9009;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9011;
              FStar_Syntax_Syntax.sigattrs = uu____9012;_},uu____9013),uu____9014)
          -> q
      | uu____9065 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____9101 =
          let uu____9102 =
            let uu____9103 = FStar_Util.string_of_int i in
            let uu____9104 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____9103 uu____9104 in
          failwith uu____9102 in
        let uu____9105 = lookup_datacon env lid in
        match uu____9105 with
        | (uu____9110,t) ->
            let uu____9112 =
              let uu____9113 = FStar_Syntax_Subst.compress t in
              uu____9113.FStar_Syntax_Syntax.n in
            (match uu____9112 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9119) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____9154 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____9154
                      FStar_Pervasives_Native.fst)
             | uu____9163 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9172 = lookup_qname env l in
      match uu____9172 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9193,uu____9194,uu____9195);
              FStar_Syntax_Syntax.sigrng = uu____9196;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9198;
              FStar_Syntax_Syntax.sigattrs = uu____9199;_},uu____9200),uu____9201)
          ->
          FStar_Util.for_some
            (fun uu___108_9254  ->
               match uu___108_9254 with
               | FStar_Syntax_Syntax.Projector uu____9255 -> true
               | uu____9260 -> false) quals
      | uu____9261 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9290 = lookup_qname env lid in
      match uu____9290 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9311,uu____9312,uu____9313,uu____9314,uu____9315,uu____9316);
              FStar_Syntax_Syntax.sigrng = uu____9317;
              FStar_Syntax_Syntax.sigquals = uu____9318;
              FStar_Syntax_Syntax.sigmeta = uu____9319;
              FStar_Syntax_Syntax.sigattrs = uu____9320;_},uu____9321),uu____9322)
          -> true
      | uu____9377 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9406 = lookup_qname env lid in
      match uu____9406 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9427,uu____9428,uu____9429,uu____9430,uu____9431,uu____9432);
              FStar_Syntax_Syntax.sigrng = uu____9433;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9435;
              FStar_Syntax_Syntax.sigattrs = uu____9436;_},uu____9437),uu____9438)
          ->
          FStar_Util.for_some
            (fun uu___109_9499  ->
               match uu___109_9499 with
               | FStar_Syntax_Syntax.RecordType uu____9500 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____9509 -> true
               | uu____9518 -> false) quals
      | uu____9519 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9548 = lookup_qname env lid in
      match uu____9548 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____9569,uu____9570);
              FStar_Syntax_Syntax.sigrng = uu____9571;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____9573;
              FStar_Syntax_Syntax.sigattrs = uu____9574;_},uu____9575),uu____9576)
          ->
          FStar_Util.for_some
            (fun uu___110_9633  ->
               match uu___110_9633 with
               | FStar_Syntax_Syntax.Action uu____9634 -> true
               | uu____9635 -> false) quals
      | uu____9636 -> false
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
      let uu____9668 =
        let uu____9669 = FStar_Syntax_Util.un_uinst head1 in
        uu____9669.FStar_Syntax_Syntax.n in
      match uu____9668 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____9675 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____9742 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____9758) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____9775 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____9782 ->
                 FStar_Pervasives_Native.Some true
             | uu____9799 -> FStar_Pervasives_Native.Some false) in
      let uu____9800 =
        let uu____9803 = lookup_qname env lid in
        FStar_Util.bind_opt uu____9803 mapper in
      match uu____9800 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____9851 = lookup_qname env lid in
      match uu____9851 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9872,uu____9873,tps,uu____9875,uu____9876,uu____9877);
              FStar_Syntax_Syntax.sigrng = uu____9878;
              FStar_Syntax_Syntax.sigquals = uu____9879;
              FStar_Syntax_Syntax.sigmeta = uu____9880;
              FStar_Syntax_Syntax.sigattrs = uu____9881;_},uu____9882),uu____9883)
          -> FStar_List.length tps
      | uu____9946 ->
          let uu____9967 =
            let uu____9968 =
              let uu____9973 = name_not_found lid in
              (uu____9973, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9968 in
          raise uu____9967
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
           (fun uu____10015  ->
              match uu____10015 with
              | (d,uu____10023) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____10036 = effect_decl_opt env l in
      match uu____10036 with
      | FStar_Pervasives_Native.None  ->
          let uu____10051 =
            let uu____10052 =
              let uu____10057 = name_not_found l in
              (uu____10057, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____10052 in
          raise uu____10051
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
            (let uu____10123 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____10176  ->
                       match uu____10176 with
                       | (m1,m2,uu____10189,uu____10190,uu____10191) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____10123 with
             | FStar_Pervasives_Native.None  ->
                 let uu____10208 =
                   let uu____10209 =
                     let uu____10214 =
                       let uu____10215 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____10216 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____10215
                         uu____10216 in
                     (uu____10214, (env.range)) in
                   FStar_Errors.Error uu____10209 in
                 raise uu____10208
             | FStar_Pervasives_Native.Some
                 (uu____10223,uu____10224,m3,j1,j2) -> (m3, j1, j2))
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
  let uu____10296 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____10322  ->
            match uu____10322 with
            | (d,uu____10328) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____10296 with
  | FStar_Pervasives_Native.None  ->
      let uu____10341 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____10341
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____10356 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____10356 with
       | (uu____10369,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____10381)::(wp,uu____10383)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____10425 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
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
                 let uu____10478 = get_range env in
                 let uu____10479 =
                   let uu____10484 =
                     let uu____10485 =
                       let uu____10504 =
                         let uu____10507 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____10507] in
                       (null_wp, uu____10504) in
                     FStar_Syntax_Syntax.Tm_app uu____10485 in
                   FStar_Syntax_Syntax.mk uu____10484 in
                 uu____10479 FStar_Pervasives_Native.None uu____10478 in
               let uu____10514 =
                 let uu____10515 =
                   let uu____10526 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____10526] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____10515;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____10514)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_10537 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_10537.order);
              joins = (uu___121_10537.joins)
            } in
          let uu___122_10546 = env in
          {
            solver = (uu___122_10546.solver);
            range = (uu___122_10546.range);
            curmodule = (uu___122_10546.curmodule);
            gamma = (uu___122_10546.gamma);
            gamma_cache = (uu___122_10546.gamma_cache);
            modules = (uu___122_10546.modules);
            expected_typ = (uu___122_10546.expected_typ);
            sigtab = (uu___122_10546.sigtab);
            is_pattern = (uu___122_10546.is_pattern);
            instantiate_imp = (uu___122_10546.instantiate_imp);
            effects;
            generalize = (uu___122_10546.generalize);
            letrecs = (uu___122_10546.letrecs);
            top_level = (uu___122_10546.top_level);
            check_uvars = (uu___122_10546.check_uvars);
            use_eq = (uu___122_10546.use_eq);
            is_iface = (uu___122_10546.is_iface);
            admit = (uu___122_10546.admit);
            lax = (uu___122_10546.lax);
            lax_universes = (uu___122_10546.lax_universes);
            type_of = (uu___122_10546.type_of);
            universe_of = (uu___122_10546.universe_of);
            use_bv_sorts = (uu___122_10546.use_bv_sorts);
            qname_and_index = (uu___122_10546.qname_and_index);
            proof_ns = (uu___122_10546.proof_ns);
            synth = (uu___122_10546.synth);
            is_native_tactic = (uu___122_10546.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____10563 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____10563 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____10653 = (e1.mlift).mlift_wp t wp in
                              let uu____10654 = l1 t wp e in
                              l2 t uu____10653 uu____10654))
                | uu____10655 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____10696 = inst_tscheme lift_t in
            match uu____10696 with
            | (uu____10705,lift_t1) ->
                let uu____10707 =
                  let uu____10712 =
                    let uu____10713 =
                      let uu____10732 =
                        let uu____10735 = FStar_Syntax_Syntax.as_arg r in
                        let uu____10736 =
                          let uu____10739 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____10739] in
                        uu____10735 :: uu____10736 in
                      (lift_t1, uu____10732) in
                    FStar_Syntax_Syntax.Tm_app uu____10713 in
                  FStar_Syntax_Syntax.mk uu____10712 in
                uu____10707 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____10789 = inst_tscheme lift_t in
            match uu____10789 with
            | (uu____10798,lift_t1) ->
                let uu____10800 =
                  let uu____10805 =
                    let uu____10806 =
                      let uu____10825 =
                        let uu____10828 = FStar_Syntax_Syntax.as_arg r in
                        let uu____10829 =
                          let uu____10832 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____10833 =
                            let uu____10836 = FStar_Syntax_Syntax.as_arg e in
                            [uu____10836] in
                          uu____10832 :: uu____10833 in
                        uu____10828 :: uu____10829 in
                      (lift_t1, uu____10825) in
                    FStar_Syntax_Syntax.Tm_app uu____10806 in
                  FStar_Syntax_Syntax.mk uu____10805 in
                uu____10800 FStar_Pervasives_Native.None
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
              let uu____10879 =
                let uu____10880 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____10880
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____10879 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____10884 =
              let uu____10885 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____10885 in
            let uu____10886 =
              let uu____10887 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____10905 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____10905) in
              FStar_Util.dflt "none" uu____10887 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____10884
              uu____10886 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____10931  ->
                    match uu____10931 with
                    | (e,uu____10939) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____10958 =
            match uu____10958 with
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
              let uu____10996 =
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
                                    (let uu____11017 =
                                       let uu____11026 =
                                         find_edge order1 (i, k) in
                                       let uu____11029 =
                                         find_edge order1 (k, j) in
                                       (uu____11026, uu____11029) in
                                     match uu____11017 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____11044 =
                                           compose_edges e1 e2 in
                                         [uu____11044]
                                     | uu____11045 -> []))))) in
              FStar_List.append order1 uu____10996 in
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
                   let uu____11074 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____11076 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____11076
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____11074
                   then
                     let uu____11081 =
                       let uu____11082 =
                         let uu____11087 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____11088 = get_range env in
                         (uu____11087, uu____11088) in
                       FStar_Errors.Error uu____11082 in
                     raise uu____11081
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
                                            let uu____11213 =
                                              let uu____11222 =
                                                find_edge order2 (i, k) in
                                              let uu____11225 =
                                                find_edge order2 (j, k) in
                                              (uu____11222, uu____11225) in
                                            match uu____11213 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____11267,uu____11268)
                                                     ->
                                                     let uu____11275 =
                                                       let uu____11280 =
                                                         let uu____11281 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____11281 in
                                                       let uu____11284 =
                                                         let uu____11285 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____11285 in
                                                       (uu____11280,
                                                         uu____11284) in
                                                     (match uu____11275 with
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
                                            | uu____11320 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___123_11393 = env.effects in
              { decls = (uu___123_11393.decls); order = order2; joins } in
            let uu___124_11394 = env in
            {
              solver = (uu___124_11394.solver);
              range = (uu___124_11394.range);
              curmodule = (uu___124_11394.curmodule);
              gamma = (uu___124_11394.gamma);
              gamma_cache = (uu___124_11394.gamma_cache);
              modules = (uu___124_11394.modules);
              expected_typ = (uu___124_11394.expected_typ);
              sigtab = (uu___124_11394.sigtab);
              is_pattern = (uu___124_11394.is_pattern);
              instantiate_imp = (uu___124_11394.instantiate_imp);
              effects;
              generalize = (uu___124_11394.generalize);
              letrecs = (uu___124_11394.letrecs);
              top_level = (uu___124_11394.top_level);
              check_uvars = (uu___124_11394.check_uvars);
              use_eq = (uu___124_11394.use_eq);
              is_iface = (uu___124_11394.is_iface);
              admit = (uu___124_11394.admit);
              lax = (uu___124_11394.lax);
              lax_universes = (uu___124_11394.lax_universes);
              type_of = (uu___124_11394.type_of);
              universe_of = (uu___124_11394.universe_of);
              use_bv_sorts = (uu___124_11394.use_bv_sorts);
              qname_and_index = (uu___124_11394.qname_and_index);
              proof_ns = (uu___124_11394.proof_ns);
              synth = (uu___124_11394.synth);
              is_native_tactic = (uu___124_11394.is_native_tactic)
            }))
      | uu____11395 -> env
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
        | uu____11429 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____11439 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____11439 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____11456 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____11456 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____11476 =
                     let uu____11477 =
                       let uu____11482 =
                         let uu____11483 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____11488 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____11497 =
                           let uu____11498 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____11498 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____11483 uu____11488 uu____11497 in
                       (uu____11482, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____11477 in
                   raise uu____11476)
                else ();
                (let inst1 =
                   let uu____11503 =
                     let uu____11514 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____11514 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____11533  ->
                        fun uu____11534  ->
                          match (uu____11533, uu____11534) with
                          | ((x,uu____11560),(t,uu____11562)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____11503 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____11589 =
                     let uu___125_11590 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_11590.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_11590.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_11590.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_11590.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____11589
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____11632 =
    let uu____11641 =
      norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____11641 in
  match uu____11632 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
      let uu____11670 =
        only_reifiable &&
          (let uu____11672 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____11672) in
      if uu____11670
      then FStar_Pervasives_Native.None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
         | uu____11696 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____11698 =
               let uu____11715 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____11715) in
             (match uu____11698 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____11779 =
                    let uu____11784 = get_range env in
                    let uu____11785 =
                      let uu____11790 =
                        let uu____11791 =
                          let uu____11810 =
                            let uu____11813 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____11813; wp] in
                          (repr, uu____11810) in
                        FStar_Syntax_Syntax.Tm_app uu____11791 in
                      FStar_Syntax_Syntax.mk uu____11790 in
                    uu____11785 FStar_Pervasives_Native.None uu____11784 in
                  FStar_Pervasives_Native.Some uu____11779))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
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
          let uu____11872 =
            let uu____11873 =
              let uu____11878 =
                let uu____11879 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____11879 in
              let uu____11880 = get_range env in (uu____11878, uu____11880) in
            FStar_Errors.Error uu____11873 in
          raise uu____11872 in
        let uu____11881 = effect_repr_aux true env c u_c in
        match uu____11881 with
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
      | uu____11929 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____11938 =
        let uu____11939 = FStar_Syntax_Subst.compress t in
        uu____11939.FStar_Syntax_Syntax.n in
      match uu____11938 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____11944,c) ->
          is_reifiable_comp env c
      | uu____11966 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____11990)::uu____11991 -> x :: rest
        | (Binding_sig_inst uu____12000)::uu____12001 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____12016 = push1 x rest1 in local :: uu____12016 in
      let uu___126_12019 = env in
      let uu____12020 = push1 s env.gamma in
      {
        solver = (uu___126_12019.solver);
        range = (uu___126_12019.range);
        curmodule = (uu___126_12019.curmodule);
        gamma = uu____12020;
        gamma_cache = (uu___126_12019.gamma_cache);
        modules = (uu___126_12019.modules);
        expected_typ = (uu___126_12019.expected_typ);
        sigtab = (uu___126_12019.sigtab);
        is_pattern = (uu___126_12019.is_pattern);
        instantiate_imp = (uu___126_12019.instantiate_imp);
        effects = (uu___126_12019.effects);
        generalize = (uu___126_12019.generalize);
        letrecs = (uu___126_12019.letrecs);
        top_level = (uu___126_12019.top_level);
        check_uvars = (uu___126_12019.check_uvars);
        use_eq = (uu___126_12019.use_eq);
        is_iface = (uu___126_12019.is_iface);
        admit = (uu___126_12019.admit);
        lax = (uu___126_12019.lax);
        lax_universes = (uu___126_12019.lax_universes);
        type_of = (uu___126_12019.type_of);
        universe_of = (uu___126_12019.universe_of);
        use_bv_sorts = (uu___126_12019.use_bv_sorts);
        qname_and_index = (uu___126_12019.qname_and_index);
        proof_ns = (uu___126_12019.proof_ns);
        synth = (uu___126_12019.synth);
        is_native_tactic = (uu___126_12019.is_native_tactic)
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
      let uu___127_12057 = env in
      {
        solver = (uu___127_12057.solver);
        range = (uu___127_12057.range);
        curmodule = (uu___127_12057.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___127_12057.gamma_cache);
        modules = (uu___127_12057.modules);
        expected_typ = (uu___127_12057.expected_typ);
        sigtab = (uu___127_12057.sigtab);
        is_pattern = (uu___127_12057.is_pattern);
        instantiate_imp = (uu___127_12057.instantiate_imp);
        effects = (uu___127_12057.effects);
        generalize = (uu___127_12057.generalize);
        letrecs = (uu___127_12057.letrecs);
        top_level = (uu___127_12057.top_level);
        check_uvars = (uu___127_12057.check_uvars);
        use_eq = (uu___127_12057.use_eq);
        is_iface = (uu___127_12057.is_iface);
        admit = (uu___127_12057.admit);
        lax = (uu___127_12057.lax);
        lax_universes = (uu___127_12057.lax_universes);
        type_of = (uu___127_12057.type_of);
        universe_of = (uu___127_12057.universe_of);
        use_bv_sorts = (uu___127_12057.use_bv_sorts);
        qname_and_index = (uu___127_12057.qname_and_index);
        proof_ns = (uu___127_12057.proof_ns);
        synth = (uu___127_12057.synth);
        is_native_tactic = (uu___127_12057.is_native_tactic)
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
            (let uu___128_12091 = env in
             {
               solver = (uu___128_12091.solver);
               range = (uu___128_12091.range);
               curmodule = (uu___128_12091.curmodule);
               gamma = rest;
               gamma_cache = (uu___128_12091.gamma_cache);
               modules = (uu___128_12091.modules);
               expected_typ = (uu___128_12091.expected_typ);
               sigtab = (uu___128_12091.sigtab);
               is_pattern = (uu___128_12091.is_pattern);
               instantiate_imp = (uu___128_12091.instantiate_imp);
               effects = (uu___128_12091.effects);
               generalize = (uu___128_12091.generalize);
               letrecs = (uu___128_12091.letrecs);
               top_level = (uu___128_12091.top_level);
               check_uvars = (uu___128_12091.check_uvars);
               use_eq = (uu___128_12091.use_eq);
               is_iface = (uu___128_12091.is_iface);
               admit = (uu___128_12091.admit);
               lax = (uu___128_12091.lax);
               lax_universes = (uu___128_12091.lax_universes);
               type_of = (uu___128_12091.type_of);
               universe_of = (uu___128_12091.universe_of);
               use_bv_sorts = (uu___128_12091.use_bv_sorts);
               qname_and_index = (uu___128_12091.qname_and_index);
               proof_ns = (uu___128_12091.proof_ns);
               synth = (uu___128_12091.synth);
               is_native_tactic = (uu___128_12091.is_native_tactic)
             }))
    | uu____12092 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____12116  ->
             match uu____12116 with | (x,uu____12122) -> push_bv env1 x) env
        bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,(FStar_Syntax_Syntax.term',
                                                FStar_Syntax_Syntax.term')
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___129_12156 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_12156.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_12156.FStar_Syntax_Syntax.index);
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
      (let uu___130_12195 = env in
       {
         solver = (uu___130_12195.solver);
         range = (uu___130_12195.range);
         curmodule = (uu___130_12195.curmodule);
         gamma = [];
         gamma_cache = (uu___130_12195.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_12195.sigtab);
         is_pattern = (uu___130_12195.is_pattern);
         instantiate_imp = (uu___130_12195.instantiate_imp);
         effects = (uu___130_12195.effects);
         generalize = (uu___130_12195.generalize);
         letrecs = (uu___130_12195.letrecs);
         top_level = (uu___130_12195.top_level);
         check_uvars = (uu___130_12195.check_uvars);
         use_eq = (uu___130_12195.use_eq);
         is_iface = (uu___130_12195.is_iface);
         admit = (uu___130_12195.admit);
         lax = (uu___130_12195.lax);
         lax_universes = (uu___130_12195.lax_universes);
         type_of = (uu___130_12195.type_of);
         universe_of = (uu___130_12195.universe_of);
         use_bv_sorts = (uu___130_12195.use_bv_sorts);
         qname_and_index = (uu___130_12195.qname_and_index);
         proof_ns = (uu___130_12195.proof_ns);
         synth = (uu___130_12195.synth);
         is_native_tactic = (uu___130_12195.is_native_tactic)
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
        let uu____12232 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____12232 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____12260 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____12260)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___131_12275 = env in
      {
        solver = (uu___131_12275.solver);
        range = (uu___131_12275.range);
        curmodule = (uu___131_12275.curmodule);
        gamma = (uu___131_12275.gamma);
        gamma_cache = (uu___131_12275.gamma_cache);
        modules = (uu___131_12275.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_12275.sigtab);
        is_pattern = (uu___131_12275.is_pattern);
        instantiate_imp = (uu___131_12275.instantiate_imp);
        effects = (uu___131_12275.effects);
        generalize = (uu___131_12275.generalize);
        letrecs = (uu___131_12275.letrecs);
        top_level = (uu___131_12275.top_level);
        check_uvars = (uu___131_12275.check_uvars);
        use_eq = false;
        is_iface = (uu___131_12275.is_iface);
        admit = (uu___131_12275.admit);
        lax = (uu___131_12275.lax);
        lax_universes = (uu___131_12275.lax_universes);
        type_of = (uu___131_12275.type_of);
        universe_of = (uu___131_12275.universe_of);
        use_bv_sorts = (uu___131_12275.use_bv_sorts);
        qname_and_index = (uu___131_12275.qname_and_index);
        proof_ns = (uu___131_12275.proof_ns);
        synth = (uu___131_12275.synth);
        is_native_tactic = (uu___131_12275.is_native_tactic)
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
    let uu____12301 = expected_typ env_ in
    ((let uu___132_12307 = env_ in
      {
        solver = (uu___132_12307.solver);
        range = (uu___132_12307.range);
        curmodule = (uu___132_12307.curmodule);
        gamma = (uu___132_12307.gamma);
        gamma_cache = (uu___132_12307.gamma_cache);
        modules = (uu___132_12307.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_12307.sigtab);
        is_pattern = (uu___132_12307.is_pattern);
        instantiate_imp = (uu___132_12307.instantiate_imp);
        effects = (uu___132_12307.effects);
        generalize = (uu___132_12307.generalize);
        letrecs = (uu___132_12307.letrecs);
        top_level = (uu___132_12307.top_level);
        check_uvars = (uu___132_12307.check_uvars);
        use_eq = false;
        is_iface = (uu___132_12307.is_iface);
        admit = (uu___132_12307.admit);
        lax = (uu___132_12307.lax);
        lax_universes = (uu___132_12307.lax_universes);
        type_of = (uu___132_12307.type_of);
        universe_of = (uu___132_12307.universe_of);
        use_bv_sorts = (uu___132_12307.use_bv_sorts);
        qname_and_index = (uu___132_12307.qname_and_index);
        proof_ns = (uu___132_12307.proof_ns);
        synth = (uu___132_12307.synth);
        is_native_tactic = (uu___132_12307.is_native_tactic)
      }), uu____12301)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____12322 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___111_12332  ->
                    match uu___111_12332 with
                    | Binding_sig (uu____12335,se) -> [se]
                    | uu____12341 -> [])) in
          FStar_All.pipe_right uu____12322 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___133_12348 = env in
       {
         solver = (uu___133_12348.solver);
         range = (uu___133_12348.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___133_12348.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_12348.expected_typ);
         sigtab = (uu___133_12348.sigtab);
         is_pattern = (uu___133_12348.is_pattern);
         instantiate_imp = (uu___133_12348.instantiate_imp);
         effects = (uu___133_12348.effects);
         generalize = (uu___133_12348.generalize);
         letrecs = (uu___133_12348.letrecs);
         top_level = (uu___133_12348.top_level);
         check_uvars = (uu___133_12348.check_uvars);
         use_eq = (uu___133_12348.use_eq);
         is_iface = (uu___133_12348.is_iface);
         admit = (uu___133_12348.admit);
         lax = (uu___133_12348.lax);
         lax_universes = (uu___133_12348.lax_universes);
         type_of = (uu___133_12348.type_of);
         universe_of = (uu___133_12348.universe_of);
         use_bv_sorts = (uu___133_12348.use_bv_sorts);
         qname_and_index = (uu___133_12348.qname_and_index);
         proof_ns = (uu___133_12348.proof_ns);
         synth = (uu___133_12348.synth);
         is_native_tactic = (uu___133_12348.is_native_tactic)
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
      | (Binding_univ uu____12430)::tl1 -> aux out tl1
      | (Binding_lid (uu____12434,(uu____12435,t)))::tl1 ->
          let uu____12450 =
            let uu____12457 = FStar_Syntax_Free.uvars t in
            ext out uu____12457 in
          aux uu____12450 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12464;
            FStar_Syntax_Syntax.index = uu____12465;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12474 =
            let uu____12481 = FStar_Syntax_Free.uvars t in
            ext out uu____12481 in
          aux uu____12474 tl1
      | (Binding_sig uu____12488)::uu____12489 -> out
      | (Binding_sig_inst uu____12498)::uu____12499 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____12555)::tl1 -> aux out tl1
      | (Binding_univ uu____12567)::tl1 -> aux out tl1
      | (Binding_lid (uu____12571,(uu____12572,t)))::tl1 ->
          let uu____12587 =
            let uu____12590 = FStar_Syntax_Free.univs t in
            ext out uu____12590 in
          aux uu____12587 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12593;
            FStar_Syntax_Syntax.index = uu____12594;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12603 =
            let uu____12606 = FStar_Syntax_Free.univs t in
            ext out uu____12606 in
          aux uu____12603 tl1
      | (Binding_sig uu____12609)::uu____12610 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____12664)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____12680 = FStar_Util.set_add uname out in
          aux uu____12680 tl1
      | (Binding_lid (uu____12683,(uu____12684,t)))::tl1 ->
          let uu____12699 =
            let uu____12702 = FStar_Syntax_Free.univnames t in
            ext out uu____12702 in
          aux uu____12699 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____12705;
            FStar_Syntax_Syntax.index = uu____12706;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____12715 =
            let uu____12718 = FStar_Syntax_Free.univnames t in
            ext out uu____12718 in
          aux uu____12715 tl1
      | (Binding_sig uu____12721)::uu____12722 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___112_12750  ->
            match uu___112_12750 with
            | Binding_var x -> [x]
            | Binding_lid uu____12754 -> []
            | Binding_sig uu____12759 -> []
            | Binding_univ uu____12766 -> []
            | Binding_sig_inst uu____12767 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____12784 =
      let uu____12787 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____12787
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____12784 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____12812 =
      let uu____12813 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___113_12823  ->
                match uu___113_12823 with
                | Binding_var x ->
                    let uu____12825 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____12825
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____12828) ->
                    let uu____12829 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____12829
                | Binding_sig (ls,uu____12831) ->
                    let uu____12836 =
                      let uu____12837 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____12837
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____12836
                | Binding_sig_inst (ls,uu____12847,uu____12848) ->
                    let uu____12853 =
                      let uu____12854 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____12854
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____12853)) in
      FStar_All.pipe_right uu____12813 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____12812 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____12873 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____12873
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____12901  ->
                 fun uu____12902  ->
                   match (uu____12901, uu____12902) with
                   | ((b1,uu____12920),(b2,uu____12922)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___114_12984  ->
             match uu___114_12984 with
             | Binding_sig (lids,uu____12990) -> FStar_List.append lids keys
             | uu____12995 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____13001  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____13037) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____13056,uu____13057) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____13094 = list_prefix p path1 in
            if uu____13094 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____13108 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____13108
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___134_13138 = e in
            {
              solver = (uu___134_13138.solver);
              range = (uu___134_13138.range);
              curmodule = (uu___134_13138.curmodule);
              gamma = (uu___134_13138.gamma);
              gamma_cache = (uu___134_13138.gamma_cache);
              modules = (uu___134_13138.modules);
              expected_typ = (uu___134_13138.expected_typ);
              sigtab = (uu___134_13138.sigtab);
              is_pattern = (uu___134_13138.is_pattern);
              instantiate_imp = (uu___134_13138.instantiate_imp);
              effects = (uu___134_13138.effects);
              generalize = (uu___134_13138.generalize);
              letrecs = (uu___134_13138.letrecs);
              top_level = (uu___134_13138.top_level);
              check_uvars = (uu___134_13138.check_uvars);
              use_eq = (uu___134_13138.use_eq);
              is_iface = (uu___134_13138.is_iface);
              admit = (uu___134_13138.admit);
              lax = (uu___134_13138.lax);
              lax_universes = (uu___134_13138.lax_universes);
              type_of = (uu___134_13138.type_of);
              universe_of = (uu___134_13138.universe_of);
              use_bv_sorts = (uu___134_13138.use_bv_sorts);
              qname_and_index = (uu___134_13138.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___134_13138.synth);
              is_native_tactic = (uu___134_13138.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___135_13165 = e in
    {
      solver = (uu___135_13165.solver);
      range = (uu___135_13165.range);
      curmodule = (uu___135_13165.curmodule);
      gamma = (uu___135_13165.gamma);
      gamma_cache = (uu___135_13165.gamma_cache);
      modules = (uu___135_13165.modules);
      expected_typ = (uu___135_13165.expected_typ);
      sigtab = (uu___135_13165.sigtab);
      is_pattern = (uu___135_13165.is_pattern);
      instantiate_imp = (uu___135_13165.instantiate_imp);
      effects = (uu___135_13165.effects);
      generalize = (uu___135_13165.generalize);
      letrecs = (uu___135_13165.letrecs);
      top_level = (uu___135_13165.top_level);
      check_uvars = (uu___135_13165.check_uvars);
      use_eq = (uu___135_13165.use_eq);
      is_iface = (uu___135_13165.is_iface);
      admit = (uu___135_13165.admit);
      lax = (uu___135_13165.lax);
      lax_universes = (uu___135_13165.lax_universes);
      type_of = (uu___135_13165.type_of);
      universe_of = (uu___135_13165.universe_of);
      use_bv_sorts = (uu___135_13165.use_bv_sorts);
      qname_and_index = (uu___135_13165.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___135_13165.synth);
      is_native_tactic = (uu___135_13165.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____13180::rest ->
        let uu___136_13184 = e in
        {
          solver = (uu___136_13184.solver);
          range = (uu___136_13184.range);
          curmodule = (uu___136_13184.curmodule);
          gamma = (uu___136_13184.gamma);
          gamma_cache = (uu___136_13184.gamma_cache);
          modules = (uu___136_13184.modules);
          expected_typ = (uu___136_13184.expected_typ);
          sigtab = (uu___136_13184.sigtab);
          is_pattern = (uu___136_13184.is_pattern);
          instantiate_imp = (uu___136_13184.instantiate_imp);
          effects = (uu___136_13184.effects);
          generalize = (uu___136_13184.generalize);
          letrecs = (uu___136_13184.letrecs);
          top_level = (uu___136_13184.top_level);
          check_uvars = (uu___136_13184.check_uvars);
          use_eq = (uu___136_13184.use_eq);
          is_iface = (uu___136_13184.is_iface);
          admit = (uu___136_13184.admit);
          lax = (uu___136_13184.lax);
          lax_universes = (uu___136_13184.lax_universes);
          type_of = (uu___136_13184.type_of);
          universe_of = (uu___136_13184.universe_of);
          use_bv_sorts = (uu___136_13184.use_bv_sorts);
          qname_and_index = (uu___136_13184.qname_and_index);
          proof_ns = rest;
          synth = (uu___136_13184.synth);
          is_native_tactic = (uu___136_13184.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___137_13197 = e in
      {
        solver = (uu___137_13197.solver);
        range = (uu___137_13197.range);
        curmodule = (uu___137_13197.curmodule);
        gamma = (uu___137_13197.gamma);
        gamma_cache = (uu___137_13197.gamma_cache);
        modules = (uu___137_13197.modules);
        expected_typ = (uu___137_13197.expected_typ);
        sigtab = (uu___137_13197.sigtab);
        is_pattern = (uu___137_13197.is_pattern);
        instantiate_imp = (uu___137_13197.instantiate_imp);
        effects = (uu___137_13197.effects);
        generalize = (uu___137_13197.generalize);
        letrecs = (uu___137_13197.letrecs);
        top_level = (uu___137_13197.top_level);
        check_uvars = (uu___137_13197.check_uvars);
        use_eq = (uu___137_13197.use_eq);
        is_iface = (uu___137_13197.is_iface);
        admit = (uu___137_13197.admit);
        lax = (uu___137_13197.lax);
        lax_universes = (uu___137_13197.lax_universes);
        type_of = (uu___137_13197.type_of);
        universe_of = (uu___137_13197.universe_of);
        use_bv_sorts = (uu___137_13197.use_bv_sorts);
        qname_and_index = (uu___137_13197.qname_and_index);
        proof_ns = ns;
        synth = (uu___137_13197.synth);
        is_native_tactic = (uu___137_13197.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____13226 =
        FStar_List.map
          (fun fpns  ->
             let uu____13248 =
               let uu____13249 =
                 let uu____13250 =
                   FStar_List.map
                     (fun uu____13262  ->
                        match uu____13262 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____13250 in
               Prims.strcat uu____13249 "]" in
             Prims.strcat "[" uu____13248) pns in
      FStar_String.concat ";" uu____13226 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____13278  -> ());
    push = (fun uu____13280  -> ());
    pop = (fun uu____13282  -> ());
    mark = (fun uu____13284  -> ());
    reset_mark = (fun uu____13286  -> ());
    commit_mark = (fun uu____13288  -> ());
    encode_modul = (fun uu____13291  -> fun uu____13292  -> ());
    encode_sig = (fun uu____13295  -> fun uu____13296  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____13302 =
             let uu____13309 = FStar_Options.peek () in (e, g, uu____13309) in
           [uu____13302]);
    solve = (fun uu____13325  -> fun uu____13326  -> fun uu____13327  -> ());
    is_trivial = (fun uu____13334  -> fun uu____13335  -> false);
    finish = (fun uu____13337  -> ());
    refresh = (fun uu____13339  -> ())
  }