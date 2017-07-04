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
    match projectee with | Binding_var _0 -> true | uu____35 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____51 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____74 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____97 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____115 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | Always
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
  | UnfoldTac
let uu___is_Always: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Always  -> true | uu____144 -> false
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____149 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____154 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____159 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____165 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____178 -> false
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
      | (NoDelta ,uu____3494) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____3495,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____3496,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____3497 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____3509 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____3519 =
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
          let uu____3562 = new_gamma_cache () in
          let uu____3564 = new_sigtab () in
          let uu____3566 =
            let uu____3567 = FStar_Options.using_facts_from () in
            match uu____3567 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____3573 =
                  let uu____3578 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____3578 [([], false)] in
                [uu____3573]
            | FStar_Pervasives_Native.None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____3562;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____3564;
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
            proof_ns = uu____3566;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____3635  -> false)
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
  fun uu____3668  ->
    let uu____3669 = FStar_ST.read query_indices in
    match uu____3669 with
    | [] -> failwith "Empty query indices!"
    | uu____3683 ->
        let uu____3688 =
          let uu____3693 =
            let uu____3697 = FStar_ST.read query_indices in
            FStar_List.hd uu____3697 in
          let uu____3711 = FStar_ST.read query_indices in uu____3693 ::
            uu____3711 in
        FStar_ST.write query_indices uu____3688
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____3734  ->
    let uu____3735 = FStar_ST.read query_indices in
    match uu____3735 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____3772  ->
    match uu____3772 with
    | (l,n1) ->
        let uu____3777 = FStar_ST.read query_indices in
        (match uu____3777 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____3811 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3822  ->
    let uu____3823 = FStar_ST.read query_indices in FStar_List.hd uu____3823
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____3840  ->
    let uu____3841 = FStar_ST.read query_indices in
    match uu____3841 with
    | hd1::uu____3853::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____3880 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____3895 =
       let uu____3897 = FStar_ST.read stack in env :: uu____3897 in
     FStar_ST.write stack uu____3895);
    (let uu___115_3905 = env in
     let uu____3906 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____3908 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___115_3905.solver);
       range = (uu___115_3905.range);
       curmodule = (uu___115_3905.curmodule);
       gamma = (uu___115_3905.gamma);
       gamma_cache = uu____3906;
       modules = (uu___115_3905.modules);
       expected_typ = (uu___115_3905.expected_typ);
       sigtab = uu____3908;
       is_pattern = (uu___115_3905.is_pattern);
       instantiate_imp = (uu___115_3905.instantiate_imp);
       effects = (uu___115_3905.effects);
       generalize = (uu___115_3905.generalize);
       letrecs = (uu___115_3905.letrecs);
       top_level = (uu___115_3905.top_level);
       check_uvars = (uu___115_3905.check_uvars);
       use_eq = (uu___115_3905.use_eq);
       is_iface = (uu___115_3905.is_iface);
       admit = (uu___115_3905.admit);
       lax = (uu___115_3905.lax);
       lax_universes = (uu___115_3905.lax_universes);
       type_of = (uu___115_3905.type_of);
       universe_of = (uu___115_3905.universe_of);
       use_bv_sorts = (uu___115_3905.use_bv_sorts);
       qname_and_index = (uu___115_3905.qname_and_index);
       proof_ns = (uu___115_3905.proof_ns);
       synth = (uu___115_3905.synth);
       is_native_tactic = (uu___115_3905.is_native_tactic)
     })
let pop_stack: Prims.unit -> env =
  fun uu____3913  ->
    let uu____3914 = FStar_ST.read stack in
    match uu____3914 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____3926 -> failwith "Impossible: Too many pops"
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
    (let uu____3965 = pop_stack () in ());
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
        let uu____3986 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____4001  ->
                  match uu____4001 with
                  | (m,uu____4005) -> FStar_Ident.lid_equals l m)) in
        (match uu____3986 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___116_4010 = env in
               {
                 solver = (uu___116_4010.solver);
                 range = (uu___116_4010.range);
                 curmodule = (uu___116_4010.curmodule);
                 gamma = (uu___116_4010.gamma);
                 gamma_cache = (uu___116_4010.gamma_cache);
                 modules = (uu___116_4010.modules);
                 expected_typ = (uu___116_4010.expected_typ);
                 sigtab = (uu___116_4010.sigtab);
                 is_pattern = (uu___116_4010.is_pattern);
                 instantiate_imp = (uu___116_4010.instantiate_imp);
                 effects = (uu___116_4010.effects);
                 generalize = (uu___116_4010.generalize);
                 letrecs = (uu___116_4010.letrecs);
                 top_level = (uu___116_4010.top_level);
                 check_uvars = (uu___116_4010.check_uvars);
                 use_eq = (uu___116_4010.use_eq);
                 is_iface = (uu___116_4010.is_iface);
                 admit = (uu___116_4010.admit);
                 lax = (uu___116_4010.lax);
                 lax_universes = (uu___116_4010.lax_universes);
                 type_of = (uu___116_4010.type_of);
                 universe_of = (uu___116_4010.universe_of);
                 use_bv_sorts = (uu___116_4010.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___116_4010.proof_ns);
                 synth = (uu___116_4010.synth);
                 is_native_tactic = (uu___116_4010.is_native_tactic)
               }))
         | FStar_Pervasives_Native.Some (uu____4013,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___117_4019 = env in
               {
                 solver = (uu___117_4019.solver);
                 range = (uu___117_4019.range);
                 curmodule = (uu___117_4019.curmodule);
                 gamma = (uu___117_4019.gamma);
                 gamma_cache = (uu___117_4019.gamma_cache);
                 modules = (uu___117_4019.modules);
                 expected_typ = (uu___117_4019.expected_typ);
                 sigtab = (uu___117_4019.sigtab);
                 is_pattern = (uu___117_4019.is_pattern);
                 instantiate_imp = (uu___117_4019.instantiate_imp);
                 effects = (uu___117_4019.effects);
                 generalize = (uu___117_4019.generalize);
                 letrecs = (uu___117_4019.letrecs);
                 top_level = (uu___117_4019.top_level);
                 check_uvars = (uu___117_4019.check_uvars);
                 use_eq = (uu___117_4019.use_eq);
                 is_iface = (uu___117_4019.is_iface);
                 admit = (uu___117_4019.admit);
                 lax = (uu___117_4019.lax);
                 lax_universes = (uu___117_4019.lax_universes);
                 type_of = (uu___117_4019.type_of);
                 universe_of = (uu___117_4019.universe_of);
                 use_bv_sorts = (uu___117_4019.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___117_4019.proof_ns);
                 synth = (uu___117_4019.synth);
                 is_native_tactic = (uu___117_4019.is_native_tactic)
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
        (let uu___118_4039 = e in
         {
           solver = (uu___118_4039.solver);
           range = r;
           curmodule = (uu___118_4039.curmodule);
           gamma = (uu___118_4039.gamma);
           gamma_cache = (uu___118_4039.gamma_cache);
           modules = (uu___118_4039.modules);
           expected_typ = (uu___118_4039.expected_typ);
           sigtab = (uu___118_4039.sigtab);
           is_pattern = (uu___118_4039.is_pattern);
           instantiate_imp = (uu___118_4039.instantiate_imp);
           effects = (uu___118_4039.effects);
           generalize = (uu___118_4039.generalize);
           letrecs = (uu___118_4039.letrecs);
           top_level = (uu___118_4039.top_level);
           check_uvars = (uu___118_4039.check_uvars);
           use_eq = (uu___118_4039.use_eq);
           is_iface = (uu___118_4039.is_iface);
           admit = (uu___118_4039.admit);
           lax = (uu___118_4039.lax);
           lax_universes = (uu___118_4039.lax_universes);
           type_of = (uu___118_4039.type_of);
           universe_of = (uu___118_4039.universe_of);
           use_bv_sorts = (uu___118_4039.use_bv_sorts);
           qname_and_index = (uu___118_4039.qname_and_index);
           proof_ns = (uu___118_4039.proof_ns);
           synth = (uu___118_4039.synth);
           is_native_tactic = (uu___118_4039.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___119_4061 = env in
      {
        solver = (uu___119_4061.solver);
        range = (uu___119_4061.range);
        curmodule = lid;
        gamma = (uu___119_4061.gamma);
        gamma_cache = (uu___119_4061.gamma_cache);
        modules = (uu___119_4061.modules);
        expected_typ = (uu___119_4061.expected_typ);
        sigtab = (uu___119_4061.sigtab);
        is_pattern = (uu___119_4061.is_pattern);
        instantiate_imp = (uu___119_4061.instantiate_imp);
        effects = (uu___119_4061.effects);
        generalize = (uu___119_4061.generalize);
        letrecs = (uu___119_4061.letrecs);
        top_level = (uu___119_4061.top_level);
        check_uvars = (uu___119_4061.check_uvars);
        use_eq = (uu___119_4061.use_eq);
        is_iface = (uu___119_4061.is_iface);
        admit = (uu___119_4061.admit);
        lax = (uu___119_4061.lax);
        lax_universes = (uu___119_4061.lax_universes);
        type_of = (uu___119_4061.type_of);
        universe_of = (uu___119_4061.universe_of);
        use_bv_sorts = (uu___119_4061.use_bv_sorts);
        qname_and_index = (uu___119_4061.qname_and_index);
        proof_ns = (uu___119_4061.proof_ns);
        synth = (uu___119_4061.synth);
        is_native_tactic = (uu___119_4061.is_native_tactic)
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
    let uu____4090 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____4090
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____4094  ->
    let uu____4095 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____4095
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
      | ((formals,t),uu____4121) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____4143 = FStar_Syntax_Subst.subst vs t in (us, uu____4143)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___103_4149  ->
    match uu___103_4149 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____4164  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____4176 = inst_tscheme t in
      match uu____4176 with
      | (us,t1) ->
          let uu____4183 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____4183)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____4199  ->
          match uu____4199 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____4217 =
                         let uu____4218 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____4223 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____4228 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____4229 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____4218 uu____4223 uu____4228 uu____4229 in
                       failwith uu____4217)
                    else ();
                    (let uu____4231 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____4231))
               | uu____4235 ->
                   let uu____4236 =
                     let uu____4237 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____4237 in
                   failwith uu____4236)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____4242 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____4247 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____4252 -> false
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
             | ([],uu____4280) -> Maybe
             | (uu____4284,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____4296 -> No in
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
          let uu____4358 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____4358 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___104_4383  ->
                   match uu___104_4383 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____4406 =
                           let uu____4416 =
                             let uu____4424 = inst_tscheme t in
                             FStar_Util.Inl uu____4424 in
                           (uu____4416, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____4406
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____4458,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____4460);
                                     FStar_Syntax_Syntax.sigrng = uu____4461;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____4462;
                                     FStar_Syntax_Syntax.sigmeta = uu____4463;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____4464;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____4476 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____4476
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____4503 ->
                             FStar_Pervasives_Native.Some t
                         | uu____4507 -> cache t in
                       let uu____4508 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4508 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____4548 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4548 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____4592 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____4634 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____4634
         then
           let uu____4645 = find_in_sigtab env lid in
           match uu____4645 with
           | FStar_Pervasives_Native.Some se ->
               FStar_Pervasives_Native.Some
                 ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4711) ->
          add_sigelts env ses
      | uu____4716 ->
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
            | uu____4728 -> ()))
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
        (fun uu___105_4750  ->
           match uu___105_4750 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4763 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____4786,lb::[]),uu____4788) ->
          let uu____4795 =
            let uu____4800 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____4806 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____4800, uu____4806) in
          FStar_Pervasives_Native.Some uu____4795
      | FStar_Syntax_Syntax.Sig_let ((uu____4813,lbs),uu____4815) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4835 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4842 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____4842
                   then
                     let uu____4848 =
                       let uu____4853 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____4859 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____4853, uu____4859) in
                     FStar_Pervasives_Native.Some uu____4848
                   else FStar_Pervasives_Native.None)
      | uu____4871 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4891 =
          let uu____4896 =
            let uu____4899 =
              let uu____4900 =
                let uu____4903 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4903 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4900) in
            inst_tscheme uu____4899 in
          (uu____4896, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____4891
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4917,uu____4918) ->
        let uu____4921 =
          let uu____4926 =
            let uu____4929 =
              let uu____4930 =
                let uu____4933 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____4933 in
              (us, uu____4930) in
            inst_tscheme uu____4929 in
          (uu____4926, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____4921
    | uu____4944 -> FStar_Pervasives_Native.None
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
      let mapper uu____4981 =
        match uu____4981 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____5031,uvs,t,uu____5034,uu____5035,uu____5036);
                    FStar_Syntax_Syntax.sigrng = uu____5037;
                    FStar_Syntax_Syntax.sigquals = uu____5038;
                    FStar_Syntax_Syntax.sigmeta = uu____5039;
                    FStar_Syntax_Syntax.sigattrs = uu____5040;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____5051 =
                   let uu____5056 = inst_tscheme (uvs, t) in
                   (uu____5056, rng) in
                 FStar_Pervasives_Native.Some uu____5051
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____5068;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____5070;
                    FStar_Syntax_Syntax.sigattrs = uu____5071;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____5080 =
                   let uu____5081 = in_cur_mod env l in uu____5081 = Yes in
                 if uu____5080
                 then
                   let uu____5087 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____5087
                    then
                      let uu____5094 =
                        let uu____5099 = inst_tscheme (uvs, t) in
                        (uu____5099, rng) in
                      FStar_Pervasives_Native.Some uu____5094
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____5114 =
                      let uu____5119 = inst_tscheme (uvs, t) in
                      (uu____5119, rng) in
                    FStar_Pervasives_Native.Some uu____5114)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5132,uu____5133);
                    FStar_Syntax_Syntax.sigrng = uu____5134;
                    FStar_Syntax_Syntax.sigquals = uu____5135;
                    FStar_Syntax_Syntax.sigmeta = uu____5136;
                    FStar_Syntax_Syntax.sigattrs = uu____5137;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____5157 =
                        let uu____5162 = inst_tscheme (uvs, k) in
                        (uu____5162, rng) in
                      FStar_Pervasives_Native.Some uu____5157
                  | uu____5171 ->
                      let uu____5172 =
                        let uu____5177 =
                          let uu____5180 =
                            let uu____5181 =
                              let uu____5184 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5184 in
                            (uvs, uu____5181) in
                          inst_tscheme uu____5180 in
                        (uu____5177, rng) in
                      FStar_Pervasives_Native.Some uu____5172)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5199,uu____5200);
                    FStar_Syntax_Syntax.sigrng = uu____5201;
                    FStar_Syntax_Syntax.sigquals = uu____5202;
                    FStar_Syntax_Syntax.sigmeta = uu____5203;
                    FStar_Syntax_Syntax.sigattrs = uu____5204;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____5225 =
                        let uu____5230 = inst_tscheme_with (uvs, k) us in
                        (uu____5230, rng) in
                      FStar_Pervasives_Native.Some uu____5225
                  | uu____5239 ->
                      let uu____5240 =
                        let uu____5245 =
                          let uu____5248 =
                            let uu____5249 =
                              let uu____5252 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5252 in
                            (uvs, uu____5249) in
                          inst_tscheme_with uu____5248 us in
                        (uu____5245, rng) in
                      FStar_Pervasives_Native.Some uu____5240)
             | FStar_Util.Inr se ->
                 let uu____5272 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____5283;
                        FStar_Syntax_Syntax.sigrng = uu____5284;
                        FStar_Syntax_Syntax.sigquals = uu____5285;
                        FStar_Syntax_Syntax.sigmeta = uu____5286;
                        FStar_Syntax_Syntax.sigattrs = uu____5287;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____5295 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____5272
                   (FStar_Util.map_option
                      (fun uu____5321  ->
                         match uu____5321 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____5338 =
        let uu____5344 = lookup_qname env lid in
        FStar_Util.bind_opt uu____5344 mapper in
      match uu____5338 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___120_5397 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___120_5397.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___120_5397.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_5397.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5420 = lookup_qname env l in
      match uu____5420 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5440 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____5470 = try_lookup_bv env bv in
      match uu____5470 with
      | FStar_Pervasives_Native.None  ->
          let uu____5478 =
            let uu____5479 =
              let uu____5482 = variable_not_found bv in (uu____5482, bvr) in
            FStar_Errors.Error uu____5479 in
          raise uu____5478
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____5489 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____5490 = FStar_Range.set_use_range r bvr in
          (uu____5489, uu____5490)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5504 = try_lookup_lid_aux env l in
      match uu____5504 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____5546 =
            let uu____5551 =
              let uu____5554 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____5554) in
            (uu____5551, r1) in
          FStar_Pervasives_Native.Some uu____5546
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____5573 = try_lookup_lid env l in
      match uu____5573 with
      | FStar_Pervasives_Native.None  ->
          let uu____5587 =
            let uu____5588 =
              let uu____5591 = name_not_found l in
              (uu____5591, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____5588 in
          raise uu____5587
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___106_5616  ->
              match uu___106_5616 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5618 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____5631 = lookup_qname env lid in
      match uu____5631 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5646,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5649;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5651;
              FStar_Syntax_Syntax.sigattrs = uu____5652;_},FStar_Pervasives_Native.None
            ),uu____5653)
          ->
          let uu____5678 =
            let uu____5684 =
              let uu____5687 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____5687) in
            (uu____5684, q) in
          FStar_Pervasives_Native.Some uu____5678
      | uu____5696 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5720 = lookup_qname env lid in
      match uu____5720 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5733,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5736;
              FStar_Syntax_Syntax.sigquals = uu____5737;
              FStar_Syntax_Syntax.sigmeta = uu____5738;
              FStar_Syntax_Syntax.sigattrs = uu____5739;_},FStar_Pervasives_Native.None
            ),uu____5740)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5765 ->
          let uu____5776 =
            let uu____5777 =
              let uu____5780 = name_not_found lid in
              (uu____5780, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5777 in
          raise uu____5776
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5793 = lookup_qname env lid in
      match uu____5793 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5806,uvs,t,uu____5809,uu____5810,uu____5811);
              FStar_Syntax_Syntax.sigrng = uu____5812;
              FStar_Syntax_Syntax.sigquals = uu____5813;
              FStar_Syntax_Syntax.sigmeta = uu____5814;
              FStar_Syntax_Syntax.sigattrs = uu____5815;_},FStar_Pervasives_Native.None
            ),uu____5816)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5843 ->
          let uu____5854 =
            let uu____5855 =
              let uu____5858 = name_not_found lid in
              (uu____5858, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5855 in
          raise uu____5854
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5872 = lookup_qname env lid in
      match uu____5872 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5886,uu____5887,uu____5888,uu____5889,uu____5890,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5892;
              FStar_Syntax_Syntax.sigquals = uu____5893;
              FStar_Syntax_Syntax.sigmeta = uu____5894;
              FStar_Syntax_Syntax.sigattrs = uu____5895;_},uu____5896),uu____5897)
          -> (true, dcs)
      | uu____5928 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5948 = lookup_qname env lid in
      match uu____5948 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5959,uu____5960,uu____5961,l,uu____5963,uu____5964);
              FStar_Syntax_Syntax.sigrng = uu____5965;
              FStar_Syntax_Syntax.sigquals = uu____5966;
              FStar_Syntax_Syntax.sigmeta = uu____5967;
              FStar_Syntax_Syntax.sigattrs = uu____5968;_},uu____5969),uu____5970)
          -> l
      | uu____5998 ->
          let uu____6009 =
            let uu____6010 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____6010 in
          failwith uu____6009
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
          (delta_levels = [Always]) ||
            (FStar_All.pipe_right delta_levels
               (FStar_Util.for_some
                  (fun dl  ->
                     FStar_All.pipe_right quals
                       (FStar_Util.for_some (visible_at dl))))) in
        let uu____6039 = lookup_qname env lid in
        match uu____6039 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____6054) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____6080,lbs),uu____6082) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____6100 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____6100
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | FStar_Syntax_Syntax.Sig_declare_typ (uu____6121,uvs,t) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Pervasives_Native.Some (uvs, t)
             | uu____6126 -> FStar_Pervasives_Native.None)
        | uu____6129 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____6152 = lookup_qname env ftv in
      match uu____6152 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____6165) ->
          let uu____6188 = effect_signature se in
          (match uu____6188 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____6199,t),r) ->
               let uu____6208 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____6208)
      | uu____6209 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____6228 = try_lookup_effect_lid env ftv in
      match uu____6228 with
      | FStar_Pervasives_Native.None  ->
          let uu____6230 =
            let uu____6231 =
              let uu____6234 = name_not_found ftv in
              (uu____6234, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____6231 in
          raise uu____6230
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
        let uu____6251 = lookup_qname env lid0 in
        match uu____6251 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____6269);
                FStar_Syntax_Syntax.sigrng = uu____6270;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____6272;
                FStar_Syntax_Syntax.sigattrs = uu____6273;_},FStar_Pervasives_Native.None
              ),uu____6274)
            ->
            let lid1 =
              let uu____6302 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____6302 in
            let uu____6303 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___107_6306  ->
                      match uu___107_6306 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____6307 -> false)) in
            if uu____6303
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____6324 =
                      let uu____6325 =
                        let uu____6326 = get_range env in
                        FStar_Range.string_of_range uu____6326 in
                      let uu____6327 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____6328 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____6325 uu____6327 uu____6328 in
                    failwith uu____6324) in
               match (binders, univs1) with
               | ([],uu____6336) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____6345,uu____6346::uu____6347::uu____6348) ->
                   let uu____6351 =
                     let uu____6352 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____6353 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____6352 uu____6353 in
                   failwith uu____6351
               | uu____6361 ->
                   let uu____6364 =
                     let uu____6367 =
                       let uu____6368 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____6368) in
                     inst_tscheme_with uu____6367 insts in
                   (match uu____6364 with
                    | (uu____6376,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____6379 =
                          let uu____6380 = FStar_Syntax_Subst.compress t1 in
                          uu____6380.FStar_Syntax_Syntax.n in
                        (match uu____6379 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____6410 -> failwith "Impossible")))
        | uu____6414 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6442 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____6442 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____6449,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____6454 = find1 l2 in
            (match uu____6454 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____6459 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____6459 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____6462 = find1 l in
            (match uu____6462 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____6476 = lookup_qname env l1 in
      match uu____6476 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6488;
              FStar_Syntax_Syntax.sigrng = uu____6489;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6491;
              FStar_Syntax_Syntax.sigattrs = uu____6492;_},uu____6493),uu____6494)
          -> q
      | uu____6520 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6546 =
          let uu____6547 =
            let uu____6548 = FStar_Util.string_of_int i in
            let uu____6549 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6548 uu____6549 in
          failwith uu____6547 in
        let uu____6550 = lookup_datacon env lid in
        match uu____6550 with
        | (uu____6553,t) ->
            let uu____6555 =
              let uu____6556 = FStar_Syntax_Subst.compress t in
              uu____6556.FStar_Syntax_Syntax.n in
            (match uu____6555 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6560) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____6583 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____6583
                      FStar_Pervasives_Native.fst)
             | uu____6588 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6597 = lookup_qname env l in
      match uu____6597 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6608,uu____6609,uu____6610);
              FStar_Syntax_Syntax.sigrng = uu____6611;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6613;
              FStar_Syntax_Syntax.sigattrs = uu____6614;_},uu____6615),uu____6616)
          ->
          FStar_Util.for_some
            (fun uu___108_6644  ->
               match uu___108_6644 with
               | FStar_Syntax_Syntax.Projector uu____6645 -> true
               | uu____6648 -> false) quals
      | uu____6649 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6668 = lookup_qname env lid in
      match uu____6668 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6679,uu____6680,uu____6681,uu____6682,uu____6683,uu____6684);
              FStar_Syntax_Syntax.sigrng = uu____6685;
              FStar_Syntax_Syntax.sigquals = uu____6686;
              FStar_Syntax_Syntax.sigmeta = uu____6687;
              FStar_Syntax_Syntax.sigattrs = uu____6688;_},uu____6689),uu____6690)
          -> true
      | uu____6718 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6737 = lookup_qname env lid in
      match uu____6737 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6748,uu____6749,uu____6750,uu____6751,uu____6752,uu____6753);
              FStar_Syntax_Syntax.sigrng = uu____6754;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6756;
              FStar_Syntax_Syntax.sigattrs = uu____6757;_},uu____6758),uu____6759)
          ->
          FStar_Util.for_some
            (fun uu___109_6791  ->
               match uu___109_6791 with
               | FStar_Syntax_Syntax.RecordType uu____6792 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6797 -> true
               | uu____6802 -> false) quals
      | uu____6803 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6822 = lookup_qname env lid in
      match uu____6822 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6833,uu____6834);
              FStar_Syntax_Syntax.sigrng = uu____6835;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6837;
              FStar_Syntax_Syntax.sigattrs = uu____6838;_},uu____6839),uu____6840)
          ->
          FStar_Util.for_some
            (fun uu___110_6870  ->
               match uu___110_6870 with
               | FStar_Syntax_Syntax.Action uu____6871 -> true
               | uu____6872 -> false) quals
      | uu____6873 -> false
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
      let uu____6894 =
        let uu____6895 = FStar_Syntax_Util.un_uinst head1 in
        uu____6895.FStar_Syntax_Syntax.n in
      match uu____6894 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6899 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____6939 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____6948) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6957 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6961 ->
                 FStar_Pervasives_Native.Some true
             | uu____6970 -> FStar_Pervasives_Native.Some false) in
      let uu____6971 =
        let uu____6973 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6973 mapper in
      match uu____6971 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____7002 = lookup_qname env lid in
      match uu____7002 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____7013,uu____7014,tps,uu____7016,uu____7017,uu____7018);
              FStar_Syntax_Syntax.sigrng = uu____7019;
              FStar_Syntax_Syntax.sigquals = uu____7020;
              FStar_Syntax_Syntax.sigmeta = uu____7021;
              FStar_Syntax_Syntax.sigattrs = uu____7022;_},uu____7023),uu____7024)
          -> FStar_List.length tps
      | uu____7058 ->
          let uu____7069 =
            let uu____7070 =
              let uu____7073 = name_not_found lid in
              (uu____7073, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7070 in
          raise uu____7069
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
           (fun uu____7100  ->
              match uu____7100 with
              | (d,uu____7105) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____7116 = effect_decl_opt env l in
      match uu____7116 with
      | FStar_Pervasives_Native.None  ->
          let uu____7124 =
            let uu____7125 =
              let uu____7128 = name_not_found l in
              (uu____7128, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7125 in
          raise uu____7124
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
            (let uu____7178 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____7208  ->
                       match uu____7208 with
                       | (m1,m2,uu____7216,uu____7217,uu____7218) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____7178 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7227 =
                   let uu____7228 =
                     let uu____7231 =
                       let uu____7232 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____7233 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____7232
                         uu____7233 in
                     (uu____7231, (env.range)) in
                   FStar_Errors.Error uu____7228 in
                 raise uu____7227
             | FStar_Pervasives_Native.Some (uu____7237,uu____7238,m3,j1,j2)
                 -> (m3, j1, j2))
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
  let uu____7291 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____7306  ->
            match uu____7306 with
            | (d,uu____7310) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____7291 with
  | FStar_Pervasives_Native.None  ->
      let uu____7317 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____7317
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____7326 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____7326 with
       | (uu____7333,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____7341)::(wp,uu____7343)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____7365 -> failwith "Impossible"))
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
                 let uu____7407 = get_range env in
                 let uu____7408 =
                   let uu____7411 =
                     let uu____7412 =
                       let uu____7422 =
                         let uu____7424 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____7424] in
                       (null_wp, uu____7422) in
                     FStar_Syntax_Syntax.Tm_app uu____7412 in
                   FStar_Syntax_Syntax.mk uu____7411 in
                 uu____7408 FStar_Pervasives_Native.None uu____7407 in
               let uu____7434 =
                 let uu____7435 =
                   let uu____7441 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____7441] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____7435;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____7434)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_7452 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_7452.order);
              joins = (uu___121_7452.joins)
            } in
          let uu___122_7457 = env in
          {
            solver = (uu___122_7457.solver);
            range = (uu___122_7457.range);
            curmodule = (uu___122_7457.curmodule);
            gamma = (uu___122_7457.gamma);
            gamma_cache = (uu___122_7457.gamma_cache);
            modules = (uu___122_7457.modules);
            expected_typ = (uu___122_7457.expected_typ);
            sigtab = (uu___122_7457.sigtab);
            is_pattern = (uu___122_7457.is_pattern);
            instantiate_imp = (uu___122_7457.instantiate_imp);
            effects;
            generalize = (uu___122_7457.generalize);
            letrecs = (uu___122_7457.letrecs);
            top_level = (uu___122_7457.top_level);
            check_uvars = (uu___122_7457.check_uvars);
            use_eq = (uu___122_7457.use_eq);
            is_iface = (uu___122_7457.is_iface);
            admit = (uu___122_7457.admit);
            lax = (uu___122_7457.lax);
            lax_universes = (uu___122_7457.lax_universes);
            type_of = (uu___122_7457.type_of);
            universe_of = (uu___122_7457.universe_of);
            use_bv_sorts = (uu___122_7457.use_bv_sorts);
            qname_and_index = (uu___122_7457.qname_and_index);
            proof_ns = (uu___122_7457.proof_ns);
            synth = (uu___122_7457.synth);
            is_native_tactic = (uu___122_7457.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____7474 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____7474 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7558 = (e1.mlift).mlift_wp t wp in
                              let uu____7559 = l1 t wp e in
                              l2 t uu____7558 uu____7559))
                | uu____7560 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7595 = inst_tscheme lift_t in
            match uu____7595 with
            | (uu____7600,lift_t1) ->
                let uu____7602 =
                  let uu____7605 =
                    let uu____7606 =
                      let uu____7616 =
                        let uu____7618 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7619 =
                          let uu____7621 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7621] in
                        uu____7618 :: uu____7619 in
                      (lift_t1, uu____7616) in
                    FStar_Syntax_Syntax.Tm_app uu____7606 in
                  FStar_Syntax_Syntax.mk uu____7605 in
                uu____7602 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7666 = inst_tscheme lift_t in
            match uu____7666 with
            | (uu____7671,lift_t1) ->
                let uu____7673 =
                  let uu____7676 =
                    let uu____7677 =
                      let uu____7687 =
                        let uu____7689 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7690 =
                          let uu____7692 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7693 =
                            let uu____7695 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7695] in
                          uu____7692 :: uu____7693 in
                        uu____7689 :: uu____7690 in
                      (lift_t1, uu____7687) in
                    FStar_Syntax_Syntax.Tm_app uu____7677 in
                  FStar_Syntax_Syntax.mk uu____7676 in
                uu____7673 FStar_Pervasives_Native.None
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
              let uu____7736 =
                let uu____7737 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7737
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____7736 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7741 =
              let uu____7742 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7742 in
            let uu____7743 =
              let uu____7744 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7761 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7761) in
              FStar_Util.dflt "none" uu____7744 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7741
              uu____7743 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7777  ->
                    match uu____7777 with
                    | (e,uu____7782) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7795 =
            match uu____7795 with
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
              let uu____7821 =
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
                                    (let uu____7835 =
                                       let uu____7840 =
                                         find_edge order1 (i, k) in
                                       let uu____7842 =
                                         find_edge order1 (k, j) in
                                       (uu____7840, uu____7842) in
                                     match uu____7835 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____7851 = compose_edges e1 e2 in
                                         [uu____7851]
                                     | uu____7852 -> []))))) in
              FStar_List.append order1 uu____7821 in
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
                   let uu____7872 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____7874 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7874
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7872
                   then
                     let uu____7877 =
                       let uu____7878 =
                         let uu____7881 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7882 = get_range env in
                         (uu____7881, uu____7882) in
                       FStar_Errors.Error uu____7878 in
                     raise uu____7877
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
                                            let uu____7953 =
                                              let uu____7958 =
                                                find_edge order2 (i, k) in
                                              let uu____7960 =
                                                find_edge order2 (j, k) in
                                              (uu____7958, uu____7960) in
                                            match uu____7953 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____7983,uu____7984)
                                                     ->
                                                     let uu____7988 =
                                                       let uu____7991 =
                                                         let uu____7992 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7992 in
                                                       let uu____7994 =
                                                         let uu____7995 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7995 in
                                                       (uu____7991,
                                                         uu____7994) in
                                                     (match uu____7988 with
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
                                            | uu____8014 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___123_8053 = env.effects in
              { decls = (uu___123_8053.decls); order = order2; joins } in
            let uu___124_8054 = env in
            {
              solver = (uu___124_8054.solver);
              range = (uu___124_8054.range);
              curmodule = (uu___124_8054.curmodule);
              gamma = (uu___124_8054.gamma);
              gamma_cache = (uu___124_8054.gamma_cache);
              modules = (uu___124_8054.modules);
              expected_typ = (uu___124_8054.expected_typ);
              sigtab = (uu___124_8054.sigtab);
              is_pattern = (uu___124_8054.is_pattern);
              instantiate_imp = (uu___124_8054.instantiate_imp);
              effects;
              generalize = (uu___124_8054.generalize);
              letrecs = (uu___124_8054.letrecs);
              top_level = (uu___124_8054.top_level);
              check_uvars = (uu___124_8054.check_uvars);
              use_eq = (uu___124_8054.use_eq);
              is_iface = (uu___124_8054.is_iface);
              admit = (uu___124_8054.admit);
              lax = (uu___124_8054.lax);
              lax_universes = (uu___124_8054.lax_universes);
              type_of = (uu___124_8054.type_of);
              universe_of = (uu___124_8054.universe_of);
              use_bv_sorts = (uu___124_8054.use_bv_sorts);
              qname_and_index = (uu___124_8054.qname_and_index);
              proof_ns = (uu___124_8054.proof_ns);
              synth = (uu___124_8054.synth);
              is_native_tactic = (uu___124_8054.is_native_tactic)
            }))
      | uu____8055 -> env
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
        | uu____8079 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____8089 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____8089 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____8099 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____8099 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____8121 =
                     let uu____8122 =
                       let uu____8125 =
                         let uu____8126 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____8135 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____8146 =
                           let uu____8147 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____8147 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____8126 uu____8135 uu____8146 in
                       (uu____8125, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____8122 in
                   raise uu____8121)
                else ();
                (let inst1 =
                   let uu____8151 =
                     let uu____8157 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____8157 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____8170  ->
                        fun uu____8171  ->
                          match (uu____8170, uu____8171) with
                          | ((x,uu____8185),(t,uu____8187)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____8151 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____8202 =
                     let uu___125_8203 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_8203.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_8203.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_8203.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_8203.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____8202
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____8238 =
    let uu____8243 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____8243 in
  match uu____8238 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
      let uu____8259 =
        only_reifiable &&
          (let uu____8261 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____8261) in
      if uu____8259
      then FStar_Pervasives_Native.None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
         | uu____8274 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____8276 =
               let uu____8285 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____8285) in
             (match uu____8276 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____8319 =
                    let uu____8322 = get_range env in
                    let uu____8323 =
                      let uu____8326 =
                        let uu____8327 =
                          let uu____8337 =
                            let uu____8339 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____8339; wp] in
                          (repr, uu____8337) in
                        FStar_Syntax_Syntax.Tm_app uu____8327 in
                      FStar_Syntax_Syntax.mk uu____8326 in
                    uu____8323 FStar_Pervasives_Native.None uu____8322 in
                  FStar_Pervasives_Native.Some uu____8319))
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
          let uu____8389 =
            let uu____8390 =
              let uu____8393 =
                let uu____8394 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____8394 in
              let uu____8395 = get_range env in (uu____8393, uu____8395) in
            FStar_Errors.Error uu____8390 in
          raise uu____8389 in
        let uu____8396 = effect_repr_aux true env c u_c in
        match uu____8396 with
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
      | uu____8434 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____8443 =
        let uu____8444 = FStar_Syntax_Subst.compress t in
        uu____8444.FStar_Syntax_Syntax.n in
      match uu____8443 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____8447,c) ->
          is_reifiable_comp env c
      | uu____8459 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____8479)::uu____8480 -> x :: rest
        | (Binding_sig_inst uu____8485)::uu____8486 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____8495 = push1 x rest1 in local :: uu____8495 in
      let uu___126_8497 = env in
      let uu____8498 = push1 s env.gamma in
      {
        solver = (uu___126_8497.solver);
        range = (uu___126_8497.range);
        curmodule = (uu___126_8497.curmodule);
        gamma = uu____8498;
        gamma_cache = (uu___126_8497.gamma_cache);
        modules = (uu___126_8497.modules);
        expected_typ = (uu___126_8497.expected_typ);
        sigtab = (uu___126_8497.sigtab);
        is_pattern = (uu___126_8497.is_pattern);
        instantiate_imp = (uu___126_8497.instantiate_imp);
        effects = (uu___126_8497.effects);
        generalize = (uu___126_8497.generalize);
        letrecs = (uu___126_8497.letrecs);
        top_level = (uu___126_8497.top_level);
        check_uvars = (uu___126_8497.check_uvars);
        use_eq = (uu___126_8497.use_eq);
        is_iface = (uu___126_8497.is_iface);
        admit = (uu___126_8497.admit);
        lax = (uu___126_8497.lax);
        lax_universes = (uu___126_8497.lax_universes);
        type_of = (uu___126_8497.type_of);
        universe_of = (uu___126_8497.universe_of);
        use_bv_sorts = (uu___126_8497.use_bv_sorts);
        qname_and_index = (uu___126_8497.qname_and_index);
        proof_ns = (uu___126_8497.proof_ns);
        synth = (uu___126_8497.synth);
        is_native_tactic = (uu___126_8497.is_native_tactic)
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
      let uu___127_8532 = env in
      {
        solver = (uu___127_8532.solver);
        range = (uu___127_8532.range);
        curmodule = (uu___127_8532.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___127_8532.gamma_cache);
        modules = (uu___127_8532.modules);
        expected_typ = (uu___127_8532.expected_typ);
        sigtab = (uu___127_8532.sigtab);
        is_pattern = (uu___127_8532.is_pattern);
        instantiate_imp = (uu___127_8532.instantiate_imp);
        effects = (uu___127_8532.effects);
        generalize = (uu___127_8532.generalize);
        letrecs = (uu___127_8532.letrecs);
        top_level = (uu___127_8532.top_level);
        check_uvars = (uu___127_8532.check_uvars);
        use_eq = (uu___127_8532.use_eq);
        is_iface = (uu___127_8532.is_iface);
        admit = (uu___127_8532.admit);
        lax = (uu___127_8532.lax);
        lax_universes = (uu___127_8532.lax_universes);
        type_of = (uu___127_8532.type_of);
        universe_of = (uu___127_8532.universe_of);
        use_bv_sorts = (uu___127_8532.use_bv_sorts);
        qname_and_index = (uu___127_8532.qname_and_index);
        proof_ns = (uu___127_8532.proof_ns);
        synth = (uu___127_8532.synth);
        is_native_tactic = (uu___127_8532.is_native_tactic)
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
            (let uu___128_8557 = env in
             {
               solver = (uu___128_8557.solver);
               range = (uu___128_8557.range);
               curmodule = (uu___128_8557.curmodule);
               gamma = rest;
               gamma_cache = (uu___128_8557.gamma_cache);
               modules = (uu___128_8557.modules);
               expected_typ = (uu___128_8557.expected_typ);
               sigtab = (uu___128_8557.sigtab);
               is_pattern = (uu___128_8557.is_pattern);
               instantiate_imp = (uu___128_8557.instantiate_imp);
               effects = (uu___128_8557.effects);
               generalize = (uu___128_8557.generalize);
               letrecs = (uu___128_8557.letrecs);
               top_level = (uu___128_8557.top_level);
               check_uvars = (uu___128_8557.check_uvars);
               use_eq = (uu___128_8557.use_eq);
               is_iface = (uu___128_8557.is_iface);
               admit = (uu___128_8557.admit);
               lax = (uu___128_8557.lax);
               lax_universes = (uu___128_8557.lax_universes);
               type_of = (uu___128_8557.type_of);
               universe_of = (uu___128_8557.universe_of);
               use_bv_sorts = (uu___128_8557.use_bv_sorts);
               qname_and_index = (uu___128_8557.qname_and_index);
               proof_ns = (uu___128_8557.proof_ns);
               synth = (uu___128_8557.synth);
               is_native_tactic = (uu___128_8557.is_native_tactic)
             }))
    | uu____8558 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8577  ->
             match uu____8577 with | (x,uu____8581) -> push_bv env1 x) env bs
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
            let uu___129_8604 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_8604.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_8604.FStar_Syntax_Syntax.index);
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
      (let uu___130_8635 = env in
       {
         solver = (uu___130_8635.solver);
         range = (uu___130_8635.range);
         curmodule = (uu___130_8635.curmodule);
         gamma = [];
         gamma_cache = (uu___130_8635.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_8635.sigtab);
         is_pattern = (uu___130_8635.is_pattern);
         instantiate_imp = (uu___130_8635.instantiate_imp);
         effects = (uu___130_8635.effects);
         generalize = (uu___130_8635.generalize);
         letrecs = (uu___130_8635.letrecs);
         top_level = (uu___130_8635.top_level);
         check_uvars = (uu___130_8635.check_uvars);
         use_eq = (uu___130_8635.use_eq);
         is_iface = (uu___130_8635.is_iface);
         admit = (uu___130_8635.admit);
         lax = (uu___130_8635.lax);
         lax_universes = (uu___130_8635.lax_universes);
         type_of = (uu___130_8635.type_of);
         universe_of = (uu___130_8635.universe_of);
         use_bv_sorts = (uu___130_8635.use_bv_sorts);
         qname_and_index = (uu___130_8635.qname_and_index);
         proof_ns = (uu___130_8635.proof_ns);
         synth = (uu___130_8635.synth);
         is_native_tactic = (uu___130_8635.is_native_tactic)
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
        let uu____8666 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8666 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8682 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8682)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___131_8694 = env in
      {
        solver = (uu___131_8694.solver);
        range = (uu___131_8694.range);
        curmodule = (uu___131_8694.curmodule);
        gamma = (uu___131_8694.gamma);
        gamma_cache = (uu___131_8694.gamma_cache);
        modules = (uu___131_8694.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_8694.sigtab);
        is_pattern = (uu___131_8694.is_pattern);
        instantiate_imp = (uu___131_8694.instantiate_imp);
        effects = (uu___131_8694.effects);
        generalize = (uu___131_8694.generalize);
        letrecs = (uu___131_8694.letrecs);
        top_level = (uu___131_8694.top_level);
        check_uvars = (uu___131_8694.check_uvars);
        use_eq = false;
        is_iface = (uu___131_8694.is_iface);
        admit = (uu___131_8694.admit);
        lax = (uu___131_8694.lax);
        lax_universes = (uu___131_8694.lax_universes);
        type_of = (uu___131_8694.type_of);
        universe_of = (uu___131_8694.universe_of);
        use_bv_sorts = (uu___131_8694.use_bv_sorts);
        qname_and_index = (uu___131_8694.qname_and_index);
        proof_ns = (uu___131_8694.proof_ns);
        synth = (uu___131_8694.synth);
        is_native_tactic = (uu___131_8694.is_native_tactic)
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
    let uu____8712 = expected_typ env_ in
    ((let uu___132_8716 = env_ in
      {
        solver = (uu___132_8716.solver);
        range = (uu___132_8716.range);
        curmodule = (uu___132_8716.curmodule);
        gamma = (uu___132_8716.gamma);
        gamma_cache = (uu___132_8716.gamma_cache);
        modules = (uu___132_8716.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_8716.sigtab);
        is_pattern = (uu___132_8716.is_pattern);
        instantiate_imp = (uu___132_8716.instantiate_imp);
        effects = (uu___132_8716.effects);
        generalize = (uu___132_8716.generalize);
        letrecs = (uu___132_8716.letrecs);
        top_level = (uu___132_8716.top_level);
        check_uvars = (uu___132_8716.check_uvars);
        use_eq = false;
        is_iface = (uu___132_8716.is_iface);
        admit = (uu___132_8716.admit);
        lax = (uu___132_8716.lax);
        lax_universes = (uu___132_8716.lax_universes);
        type_of = (uu___132_8716.type_of);
        universe_of = (uu___132_8716.universe_of);
        use_bv_sorts = (uu___132_8716.use_bv_sorts);
        qname_and_index = (uu___132_8716.qname_and_index);
        proof_ns = (uu___132_8716.proof_ns);
        synth = (uu___132_8716.synth);
        is_native_tactic = (uu___132_8716.is_native_tactic)
      }), uu____8712)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____8729 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___111_8736  ->
                    match uu___111_8736 with
                    | Binding_sig (uu____8738,se) -> [se]
                    | uu____8742 -> [])) in
          FStar_All.pipe_right uu____8729 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___133_8747 = env in
       {
         solver = (uu___133_8747.solver);
         range = (uu___133_8747.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___133_8747.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_8747.expected_typ);
         sigtab = (uu___133_8747.sigtab);
         is_pattern = (uu___133_8747.is_pattern);
         instantiate_imp = (uu___133_8747.instantiate_imp);
         effects = (uu___133_8747.effects);
         generalize = (uu___133_8747.generalize);
         letrecs = (uu___133_8747.letrecs);
         top_level = (uu___133_8747.top_level);
         check_uvars = (uu___133_8747.check_uvars);
         use_eq = (uu___133_8747.use_eq);
         is_iface = (uu___133_8747.is_iface);
         admit = (uu___133_8747.admit);
         lax = (uu___133_8747.lax);
         lax_universes = (uu___133_8747.lax_universes);
         type_of = (uu___133_8747.type_of);
         universe_of = (uu___133_8747.universe_of);
         use_bv_sorts = (uu___133_8747.use_bv_sorts);
         qname_and_index = (uu___133_8747.qname_and_index);
         proof_ns = (uu___133_8747.proof_ns);
         synth = (uu___133_8747.synth);
         is_native_tactic = (uu___133_8747.is_native_tactic)
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
      | (Binding_univ uu____8798)::tl1 -> aux out tl1
      | (Binding_lid (uu____8801,(uu____8802,t)))::tl1 ->
          let uu____8811 =
            let uu____8815 = FStar_Syntax_Free.uvars t in ext out uu____8815 in
          aux uu____8811 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8819;
            FStar_Syntax_Syntax.index = uu____8820;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8826 =
            let uu____8830 = FStar_Syntax_Free.uvars t in ext out uu____8830 in
          aux uu____8826 tl1
      | (Binding_sig uu____8834)::uu____8835 -> out
      | (Binding_sig_inst uu____8840)::uu____8841 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8879)::tl1 -> aux out tl1
      | (Binding_univ uu____8886)::tl1 -> aux out tl1
      | (Binding_lid (uu____8889,(uu____8890,t)))::tl1 ->
          let uu____8899 =
            let uu____8901 = FStar_Syntax_Free.univs t in ext out uu____8901 in
          aux uu____8899 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8903;
            FStar_Syntax_Syntax.index = uu____8904;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8910 =
            let uu____8912 = FStar_Syntax_Free.univs t in ext out uu____8912 in
          aux uu____8910 tl1
      | (Binding_sig uu____8914)::uu____8915 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8953)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8963 = FStar_Util.set_add uname out in aux uu____8963 tl1
      | (Binding_lid (uu____8965,(uu____8966,t)))::tl1 ->
          let uu____8975 =
            let uu____8977 = FStar_Syntax_Free.univnames t in
            ext out uu____8977 in
          aux uu____8975 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8979;
            FStar_Syntax_Syntax.index = uu____8980;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8986 =
            let uu____8988 = FStar_Syntax_Free.univnames t in
            ext out uu____8988 in
          aux uu____8986 tl1
      | (Binding_sig uu____8990)::uu____8991 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___112_9010  ->
            match uu___112_9010 with
            | Binding_var x -> [x]
            | Binding_lid uu____9013 -> []
            | Binding_sig uu____9016 -> []
            | Binding_univ uu____9020 -> []
            | Binding_sig_inst uu____9021 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____9032 =
      let uu____9034 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____9034
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____9032 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____9053 =
      let uu____9054 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___113_9061  ->
                match uu___113_9061 with
                | Binding_var x ->
                    let uu____9063 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____9063
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____9066) ->
                    let uu____9067 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____9067
                | Binding_sig (ls,uu____9069) ->
                    let uu____9072 =
                      let uu____9073 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____9073
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____9072
                | Binding_sig_inst (ls,uu____9079,uu____9080) ->
                    let uu____9083 =
                      let uu____9084 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____9084
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____9083)) in
      FStar_All.pipe_right uu____9054 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____9053 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____9098 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____9098
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____9125  ->
                 fun uu____9126  ->
                   match (uu____9125, uu____9126) with
                   | ((b1,uu____9136),(b2,uu____9138)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___114_9192  ->
             match uu___114_9192 with
             | Binding_sig (lids,uu____9196) -> FStar_List.append lids keys
             | uu____9199 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____9204  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____9231) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____9243,uu____9244) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____9268 = list_prefix p path1 in
            if uu____9268 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9280 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____9280
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___134_9303 = e in
            {
              solver = (uu___134_9303.solver);
              range = (uu___134_9303.range);
              curmodule = (uu___134_9303.curmodule);
              gamma = (uu___134_9303.gamma);
              gamma_cache = (uu___134_9303.gamma_cache);
              modules = (uu___134_9303.modules);
              expected_typ = (uu___134_9303.expected_typ);
              sigtab = (uu___134_9303.sigtab);
              is_pattern = (uu___134_9303.is_pattern);
              instantiate_imp = (uu___134_9303.instantiate_imp);
              effects = (uu___134_9303.effects);
              generalize = (uu___134_9303.generalize);
              letrecs = (uu___134_9303.letrecs);
              top_level = (uu___134_9303.top_level);
              check_uvars = (uu___134_9303.check_uvars);
              use_eq = (uu___134_9303.use_eq);
              is_iface = (uu___134_9303.is_iface);
              admit = (uu___134_9303.admit);
              lax = (uu___134_9303.lax);
              lax_universes = (uu___134_9303.lax_universes);
              type_of = (uu___134_9303.type_of);
              universe_of = (uu___134_9303.universe_of);
              use_bv_sorts = (uu___134_9303.use_bv_sorts);
              qname_and_index = (uu___134_9303.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___134_9303.synth);
              is_native_tactic = (uu___134_9303.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___135_9327 = e in
    {
      solver = (uu___135_9327.solver);
      range = (uu___135_9327.range);
      curmodule = (uu___135_9327.curmodule);
      gamma = (uu___135_9327.gamma);
      gamma_cache = (uu___135_9327.gamma_cache);
      modules = (uu___135_9327.modules);
      expected_typ = (uu___135_9327.expected_typ);
      sigtab = (uu___135_9327.sigtab);
      is_pattern = (uu___135_9327.is_pattern);
      instantiate_imp = (uu___135_9327.instantiate_imp);
      effects = (uu___135_9327.effects);
      generalize = (uu___135_9327.generalize);
      letrecs = (uu___135_9327.letrecs);
      top_level = (uu___135_9327.top_level);
      check_uvars = (uu___135_9327.check_uvars);
      use_eq = (uu___135_9327.use_eq);
      is_iface = (uu___135_9327.is_iface);
      admit = (uu___135_9327.admit);
      lax = (uu___135_9327.lax);
      lax_universes = (uu___135_9327.lax_universes);
      type_of = (uu___135_9327.type_of);
      universe_of = (uu___135_9327.universe_of);
      use_bv_sorts = (uu___135_9327.use_bv_sorts);
      qname_and_index = (uu___135_9327.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___135_9327.synth);
      is_native_tactic = (uu___135_9327.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____9337::rest ->
        let uu___136_9340 = e in
        {
          solver = (uu___136_9340.solver);
          range = (uu___136_9340.range);
          curmodule = (uu___136_9340.curmodule);
          gamma = (uu___136_9340.gamma);
          gamma_cache = (uu___136_9340.gamma_cache);
          modules = (uu___136_9340.modules);
          expected_typ = (uu___136_9340.expected_typ);
          sigtab = (uu___136_9340.sigtab);
          is_pattern = (uu___136_9340.is_pattern);
          instantiate_imp = (uu___136_9340.instantiate_imp);
          effects = (uu___136_9340.effects);
          generalize = (uu___136_9340.generalize);
          letrecs = (uu___136_9340.letrecs);
          top_level = (uu___136_9340.top_level);
          check_uvars = (uu___136_9340.check_uvars);
          use_eq = (uu___136_9340.use_eq);
          is_iface = (uu___136_9340.is_iface);
          admit = (uu___136_9340.admit);
          lax = (uu___136_9340.lax);
          lax_universes = (uu___136_9340.lax_universes);
          type_of = (uu___136_9340.type_of);
          universe_of = (uu___136_9340.universe_of);
          use_bv_sorts = (uu___136_9340.use_bv_sorts);
          qname_and_index = (uu___136_9340.qname_and_index);
          proof_ns = rest;
          synth = (uu___136_9340.synth);
          is_native_tactic = (uu___136_9340.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___137_9353 = e in
      {
        solver = (uu___137_9353.solver);
        range = (uu___137_9353.range);
        curmodule = (uu___137_9353.curmodule);
        gamma = (uu___137_9353.gamma);
        gamma_cache = (uu___137_9353.gamma_cache);
        modules = (uu___137_9353.modules);
        expected_typ = (uu___137_9353.expected_typ);
        sigtab = (uu___137_9353.sigtab);
        is_pattern = (uu___137_9353.is_pattern);
        instantiate_imp = (uu___137_9353.instantiate_imp);
        effects = (uu___137_9353.effects);
        generalize = (uu___137_9353.generalize);
        letrecs = (uu___137_9353.letrecs);
        top_level = (uu___137_9353.top_level);
        check_uvars = (uu___137_9353.check_uvars);
        use_eq = (uu___137_9353.use_eq);
        is_iface = (uu___137_9353.is_iface);
        admit = (uu___137_9353.admit);
        lax = (uu___137_9353.lax);
        lax_universes = (uu___137_9353.lax_universes);
        type_of = (uu___137_9353.type_of);
        universe_of = (uu___137_9353.universe_of);
        use_bv_sorts = (uu___137_9353.use_bv_sorts);
        qname_and_index = (uu___137_9353.qname_and_index);
        proof_ns = ns;
        synth = (uu___137_9353.synth);
        is_native_tactic = (uu___137_9353.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____9372 =
        FStar_List.map
          (fun fpns  ->
             let uu____9385 =
               let uu____9386 =
                 let uu____9387 =
                   FStar_List.map
                     (fun uu____9395  ->
                        match uu____9395 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____9387 in
               Prims.strcat uu____9386 "]" in
             Prims.strcat "[" uu____9385) pns in
      FStar_String.concat ";" uu____9372 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____9406  -> ());
    push = (fun uu____9408  -> ());
    pop = (fun uu____9410  -> ());
    mark = (fun uu____9412  -> ());
    reset_mark = (fun uu____9414  -> ());
    commit_mark = (fun uu____9416  -> ());
    encode_modul = (fun uu____9419  -> fun uu____9420  -> ());
    encode_sig = (fun uu____9423  -> fun uu____9424  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____9430 =
             let uu____9434 = FStar_Options.peek () in (e, g, uu____9434) in
           [uu____9430]);
    solve = (fun uu____9444  -> fun uu____9445  -> fun uu____9446  -> ());
    is_trivial = (fun uu____9452  -> fun uu____9453  -> false);
    finish = (fun uu____9455  -> ());
    refresh = (fun uu____9457  -> ())
  }