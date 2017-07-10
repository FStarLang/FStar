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
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
  | UnfoldTac
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____144 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____149 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____154 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____160 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____173 -> false
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
      | (NoDelta ,uu____3489) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____3490,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____3491,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____3492 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____3504 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____3514 =
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
          let uu____3557 = new_gamma_cache () in
          let uu____3559 = new_sigtab () in
          let uu____3561 =
            let uu____3562 = FStar_Options.using_facts_from () in
            match uu____3562 with
            | FStar_Pervasives_Native.Some ns ->
                let uu____3568 =
                  let uu____3573 =
                    FStar_List.map
                      (fun s  -> ((FStar_Ident.path_of_text s), true)) ns in
                  FStar_List.append uu____3573 [([], false)] in
                [uu____3568]
            | FStar_Pervasives_Native.None  -> [[]] in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____3557;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____3559;
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
            proof_ns = uu____3561;
            synth =
              (fun e  ->
                 fun g  -> fun tau  -> failwith "no synthesizer available");
            is_native_tactic = (fun uu____3630  -> false)
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
  fun uu____3663  ->
    let uu____3664 = FStar_ST.read query_indices in
    match uu____3664 with
    | [] -> failwith "Empty query indices!"
    | uu____3678 ->
        let uu____3683 =
          let uu____3688 =
            let uu____3692 = FStar_ST.read query_indices in
            FStar_List.hd uu____3692 in
          let uu____3706 = FStar_ST.read query_indices in uu____3688 ::
            uu____3706 in
        FStar_ST.write query_indices uu____3683
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____3729  ->
    let uu____3730 = FStar_ST.read query_indices in
    match uu____3730 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____3767  ->
    match uu____3767 with
    | (l,n1) ->
        let uu____3772 = FStar_ST.read query_indices in
        (match uu____3772 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____3806 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____3817  ->
    let uu____3818 = FStar_ST.read query_indices in FStar_List.hd uu____3818
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____3835  ->
    let uu____3836 = FStar_ST.read query_indices in
    match uu____3836 with
    | hd1::uu____3848::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____3875 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____3890 =
       let uu____3892 = FStar_ST.read stack in env :: uu____3892 in
     FStar_ST.write stack uu____3890);
    (let uu___115_3900 = env in
     let uu____3901 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____3903 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___115_3900.solver);
       range = (uu___115_3900.range);
       curmodule = (uu___115_3900.curmodule);
       gamma = (uu___115_3900.gamma);
       gamma_cache = uu____3901;
       modules = (uu___115_3900.modules);
       expected_typ = (uu___115_3900.expected_typ);
       sigtab = uu____3903;
       is_pattern = (uu___115_3900.is_pattern);
       instantiate_imp = (uu___115_3900.instantiate_imp);
       effects = (uu___115_3900.effects);
       generalize = (uu___115_3900.generalize);
       letrecs = (uu___115_3900.letrecs);
       top_level = (uu___115_3900.top_level);
       check_uvars = (uu___115_3900.check_uvars);
       use_eq = (uu___115_3900.use_eq);
       is_iface = (uu___115_3900.is_iface);
       admit = (uu___115_3900.admit);
       lax = (uu___115_3900.lax);
       lax_universes = (uu___115_3900.lax_universes);
       type_of = (uu___115_3900.type_of);
       universe_of = (uu___115_3900.universe_of);
       use_bv_sorts = (uu___115_3900.use_bv_sorts);
       qname_and_index = (uu___115_3900.qname_and_index);
       proof_ns = (uu___115_3900.proof_ns);
       synth = (uu___115_3900.synth);
       is_native_tactic = (uu___115_3900.is_native_tactic)
     })
let pop_stack: Prims.unit -> env =
  fun uu____3908  ->
    let uu____3909 = FStar_ST.read stack in
    match uu____3909 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____3921 -> failwith "Impossible: Too many pops"
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
    (let uu____3960 = pop_stack () in ());
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
        let uu____3981 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____3996  ->
                  match uu____3996 with
                  | (m,uu____4000) -> FStar_Ident.lid_equals l m)) in
        (match uu____3981 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___116_4005 = env in
               {
                 solver = (uu___116_4005.solver);
                 range = (uu___116_4005.range);
                 curmodule = (uu___116_4005.curmodule);
                 gamma = (uu___116_4005.gamma);
                 gamma_cache = (uu___116_4005.gamma_cache);
                 modules = (uu___116_4005.modules);
                 expected_typ = (uu___116_4005.expected_typ);
                 sigtab = (uu___116_4005.sigtab);
                 is_pattern = (uu___116_4005.is_pattern);
                 instantiate_imp = (uu___116_4005.instantiate_imp);
                 effects = (uu___116_4005.effects);
                 generalize = (uu___116_4005.generalize);
                 letrecs = (uu___116_4005.letrecs);
                 top_level = (uu___116_4005.top_level);
                 check_uvars = (uu___116_4005.check_uvars);
                 use_eq = (uu___116_4005.use_eq);
                 is_iface = (uu___116_4005.is_iface);
                 admit = (uu___116_4005.admit);
                 lax = (uu___116_4005.lax);
                 lax_universes = (uu___116_4005.lax_universes);
                 type_of = (uu___116_4005.type_of);
                 universe_of = (uu___116_4005.universe_of);
                 use_bv_sorts = (uu___116_4005.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___116_4005.proof_ns);
                 synth = (uu___116_4005.synth);
                 is_native_tactic = (uu___116_4005.is_native_tactic)
               }))
         | FStar_Pervasives_Native.Some (uu____4008,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___117_4014 = env in
               {
                 solver = (uu___117_4014.solver);
                 range = (uu___117_4014.range);
                 curmodule = (uu___117_4014.curmodule);
                 gamma = (uu___117_4014.gamma);
                 gamma_cache = (uu___117_4014.gamma_cache);
                 modules = (uu___117_4014.modules);
                 expected_typ = (uu___117_4014.expected_typ);
                 sigtab = (uu___117_4014.sigtab);
                 is_pattern = (uu___117_4014.is_pattern);
                 instantiate_imp = (uu___117_4014.instantiate_imp);
                 effects = (uu___117_4014.effects);
                 generalize = (uu___117_4014.generalize);
                 letrecs = (uu___117_4014.letrecs);
                 top_level = (uu___117_4014.top_level);
                 check_uvars = (uu___117_4014.check_uvars);
                 use_eq = (uu___117_4014.use_eq);
                 is_iface = (uu___117_4014.is_iface);
                 admit = (uu___117_4014.admit);
                 lax = (uu___117_4014.lax);
                 lax_universes = (uu___117_4014.lax_universes);
                 type_of = (uu___117_4014.type_of);
                 universe_of = (uu___117_4014.universe_of);
                 use_bv_sorts = (uu___117_4014.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___117_4014.proof_ns);
                 synth = (uu___117_4014.synth);
                 is_native_tactic = (uu___117_4014.is_native_tactic)
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
        (let uu___118_4034 = e in
         {
           solver = (uu___118_4034.solver);
           range = r;
           curmodule = (uu___118_4034.curmodule);
           gamma = (uu___118_4034.gamma);
           gamma_cache = (uu___118_4034.gamma_cache);
           modules = (uu___118_4034.modules);
           expected_typ = (uu___118_4034.expected_typ);
           sigtab = (uu___118_4034.sigtab);
           is_pattern = (uu___118_4034.is_pattern);
           instantiate_imp = (uu___118_4034.instantiate_imp);
           effects = (uu___118_4034.effects);
           generalize = (uu___118_4034.generalize);
           letrecs = (uu___118_4034.letrecs);
           top_level = (uu___118_4034.top_level);
           check_uvars = (uu___118_4034.check_uvars);
           use_eq = (uu___118_4034.use_eq);
           is_iface = (uu___118_4034.is_iface);
           admit = (uu___118_4034.admit);
           lax = (uu___118_4034.lax);
           lax_universes = (uu___118_4034.lax_universes);
           type_of = (uu___118_4034.type_of);
           universe_of = (uu___118_4034.universe_of);
           use_bv_sorts = (uu___118_4034.use_bv_sorts);
           qname_and_index = (uu___118_4034.qname_and_index);
           proof_ns = (uu___118_4034.proof_ns);
           synth = (uu___118_4034.synth);
           is_native_tactic = (uu___118_4034.is_native_tactic)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___119_4056 = env in
      {
        solver = (uu___119_4056.solver);
        range = (uu___119_4056.range);
        curmodule = lid;
        gamma = (uu___119_4056.gamma);
        gamma_cache = (uu___119_4056.gamma_cache);
        modules = (uu___119_4056.modules);
        expected_typ = (uu___119_4056.expected_typ);
        sigtab = (uu___119_4056.sigtab);
        is_pattern = (uu___119_4056.is_pattern);
        instantiate_imp = (uu___119_4056.instantiate_imp);
        effects = (uu___119_4056.effects);
        generalize = (uu___119_4056.generalize);
        letrecs = (uu___119_4056.letrecs);
        top_level = (uu___119_4056.top_level);
        check_uvars = (uu___119_4056.check_uvars);
        use_eq = (uu___119_4056.use_eq);
        is_iface = (uu___119_4056.is_iface);
        admit = (uu___119_4056.admit);
        lax = (uu___119_4056.lax);
        lax_universes = (uu___119_4056.lax_universes);
        type_of = (uu___119_4056.type_of);
        universe_of = (uu___119_4056.universe_of);
        use_bv_sorts = (uu___119_4056.use_bv_sorts);
        qname_and_index = (uu___119_4056.qname_and_index);
        proof_ns = (uu___119_4056.proof_ns);
        synth = (uu___119_4056.synth);
        is_native_tactic = (uu___119_4056.is_native_tactic)
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
    let uu____4085 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____4085
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____4089  ->
    let uu____4090 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____4090
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
      | ((formals,t),uu____4116) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____4138 = FStar_Syntax_Subst.subst vs t in (us, uu____4138)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___103_4144  ->
    match uu___103_4144 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____4159  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____4171 = inst_tscheme t in
      match uu____4171 with
      | (us,t1) ->
          let uu____4178 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____4178)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____4194  ->
          match uu____4194 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____4212 =
                         let uu____4213 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____4218 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____4223 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____4224 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____4213 uu____4218 uu____4223 uu____4224 in
                       failwith uu____4212)
                    else ();
                    (let uu____4226 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____4226))
               | uu____4230 ->
                   let uu____4231 =
                     let uu____4232 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____4232 in
                   failwith uu____4231)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____4237 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____4242 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____4247 -> false
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
             | ([],uu____4275) -> Maybe
             | (uu____4279,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____4291 -> No in
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
          let uu____4353 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____4353 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___104_4378  ->
                   match uu___104_4378 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____4401 =
                           let uu____4411 =
                             let uu____4419 = inst_tscheme t in
                             FStar_Util.Inl uu____4419 in
                           (uu____4411, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____4401
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____4453,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____4455);
                                     FStar_Syntax_Syntax.sigrng = uu____4456;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____4457;
                                     FStar_Syntax_Syntax.sigmeta = uu____4458;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____4459;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____4471 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____4471
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____4498 ->
                             FStar_Pervasives_Native.Some t
                         | uu____4502 -> cache t in
                       let uu____4503 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4503 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____4543 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____4543 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____4587 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____4629 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____4629
         then
           let uu____4640 = find_in_sigtab env lid in
           match uu____4640 with
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
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4706) ->
          add_sigelts env ses
      | uu____4711 ->
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
            | uu____4723 -> ()))
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
        (fun uu___105_4745  ->
           match uu___105_4745 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4758 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____4781,lb::[]),uu____4783) ->
          let uu____4790 =
            let uu____4795 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____4801 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____4795, uu____4801) in
          FStar_Pervasives_Native.Some uu____4790
      | FStar_Syntax_Syntax.Sig_let ((uu____4808,lbs),uu____4810) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4830 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4837 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____4837
                   then
                     let uu____4843 =
                       let uu____4848 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____4854 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____4848, uu____4854) in
                     FStar_Pervasives_Native.Some uu____4843
                   else FStar_Pervasives_Native.None)
      | uu____4866 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4886 =
          let uu____4891 =
            let uu____4894 =
              let uu____4895 =
                let uu____4898 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4898 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4895) in
            inst_tscheme uu____4894 in
          (uu____4891, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____4886
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4912,uu____4913) ->
        let uu____4916 =
          let uu____4921 =
            let uu____4924 =
              let uu____4925 =
                let uu____4928 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____4928 in
              (us, uu____4925) in
            inst_tscheme uu____4924 in
          (uu____4921, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____4916
    | uu____4939 -> FStar_Pervasives_Native.None
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
      let mapper uu____4976 =
        match uu____4976 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____5026,uvs,t,uu____5029,uu____5030,uu____5031);
                    FStar_Syntax_Syntax.sigrng = uu____5032;
                    FStar_Syntax_Syntax.sigquals = uu____5033;
                    FStar_Syntax_Syntax.sigmeta = uu____5034;
                    FStar_Syntax_Syntax.sigattrs = uu____5035;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____5046 =
                   let uu____5051 = inst_tscheme (uvs, t) in
                   (uu____5051, rng) in
                 FStar_Pervasives_Native.Some uu____5046
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____5063;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____5065;
                    FStar_Syntax_Syntax.sigattrs = uu____5066;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____5075 =
                   let uu____5076 = in_cur_mod env l in uu____5076 = Yes in
                 if uu____5075
                 then
                   let uu____5082 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____5082
                    then
                      let uu____5089 =
                        let uu____5094 = inst_tscheme (uvs, t) in
                        (uu____5094, rng) in
                      FStar_Pervasives_Native.Some uu____5089
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____5109 =
                      let uu____5114 = inst_tscheme (uvs, t) in
                      (uu____5114, rng) in
                    FStar_Pervasives_Native.Some uu____5109)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5127,uu____5128);
                    FStar_Syntax_Syntax.sigrng = uu____5129;
                    FStar_Syntax_Syntax.sigquals = uu____5130;
                    FStar_Syntax_Syntax.sigmeta = uu____5131;
                    FStar_Syntax_Syntax.sigattrs = uu____5132;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____5152 =
                        let uu____5157 = inst_tscheme (uvs, k) in
                        (uu____5157, rng) in
                      FStar_Pervasives_Native.Some uu____5152
                  | uu____5166 ->
                      let uu____5167 =
                        let uu____5172 =
                          let uu____5175 =
                            let uu____5176 =
                              let uu____5179 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5179 in
                            (uvs, uu____5176) in
                          inst_tscheme uu____5175 in
                        (uu____5172, rng) in
                      FStar_Pervasives_Native.Some uu____5167)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5194,uu____5195);
                    FStar_Syntax_Syntax.sigrng = uu____5196;
                    FStar_Syntax_Syntax.sigquals = uu____5197;
                    FStar_Syntax_Syntax.sigmeta = uu____5198;
                    FStar_Syntax_Syntax.sigattrs = uu____5199;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____5220 =
                        let uu____5225 = inst_tscheme_with (uvs, k) us in
                        (uu____5225, rng) in
                      FStar_Pervasives_Native.Some uu____5220
                  | uu____5234 ->
                      let uu____5235 =
                        let uu____5240 =
                          let uu____5243 =
                            let uu____5244 =
                              let uu____5247 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5247 in
                            (uvs, uu____5244) in
                          inst_tscheme_with uu____5243 us in
                        (uu____5240, rng) in
                      FStar_Pervasives_Native.Some uu____5235)
             | FStar_Util.Inr se ->
                 let uu____5267 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____5278;
                        FStar_Syntax_Syntax.sigrng = uu____5279;
                        FStar_Syntax_Syntax.sigquals = uu____5280;
                        FStar_Syntax_Syntax.sigmeta = uu____5281;
                        FStar_Syntax_Syntax.sigattrs = uu____5282;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____5290 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____5267
                   (FStar_Util.map_option
                      (fun uu____5316  ->
                         match uu____5316 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____5333 =
        let uu____5339 = lookup_qname env lid in
        FStar_Util.bind_opt uu____5339 mapper in
      match uu____5333 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___120_5392 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___120_5392.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___120_5392.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5413 = lookup_qname env l in
      match uu____5413 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5433 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____5463 = try_lookup_bv env bv in
      match uu____5463 with
      | FStar_Pervasives_Native.None  ->
          let uu____5471 =
            let uu____5472 =
              let uu____5475 = variable_not_found bv in (uu____5475, bvr) in
            FStar_Errors.Error uu____5472 in
          raise uu____5471
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____5482 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____5483 = FStar_Range.set_use_range r bvr in
          (uu____5482, uu____5483)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5497 = try_lookup_lid_aux env l in
      match uu____5497 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____5539 =
            let uu____5544 =
              let uu____5547 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____5547) in
            (uu____5544, r1) in
          FStar_Pervasives_Native.Some uu____5539
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____5566 = try_lookup_lid env l in
      match uu____5566 with
      | FStar_Pervasives_Native.None  ->
          let uu____5580 =
            let uu____5581 =
              let uu____5584 = name_not_found l in
              (uu____5584, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____5581 in
          raise uu____5580
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___106_5609  ->
              match uu___106_5609 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5611 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____5624 = lookup_qname env lid in
      match uu____5624 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5639,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5642;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5644;
              FStar_Syntax_Syntax.sigattrs = uu____5645;_},FStar_Pervasives_Native.None
            ),uu____5646)
          ->
          let uu____5671 =
            let uu____5677 =
              let uu____5680 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____5680) in
            (uu____5677, q) in
          FStar_Pervasives_Native.Some uu____5671
      | uu____5689 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5713 = lookup_qname env lid in
      match uu____5713 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5726,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5729;
              FStar_Syntax_Syntax.sigquals = uu____5730;
              FStar_Syntax_Syntax.sigmeta = uu____5731;
              FStar_Syntax_Syntax.sigattrs = uu____5732;_},FStar_Pervasives_Native.None
            ),uu____5733)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5758 ->
          let uu____5769 =
            let uu____5770 =
              let uu____5773 = name_not_found lid in
              (uu____5773, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5770 in
          raise uu____5769
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5786 = lookup_qname env lid in
      match uu____5786 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5799,uvs,t,uu____5802,uu____5803,uu____5804);
              FStar_Syntax_Syntax.sigrng = uu____5805;
              FStar_Syntax_Syntax.sigquals = uu____5806;
              FStar_Syntax_Syntax.sigmeta = uu____5807;
              FStar_Syntax_Syntax.sigattrs = uu____5808;_},FStar_Pervasives_Native.None
            ),uu____5809)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5836 ->
          let uu____5847 =
            let uu____5848 =
              let uu____5851 = name_not_found lid in
              (uu____5851, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5848 in
          raise uu____5847
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5865 = lookup_qname env lid in
      match uu____5865 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5879,uu____5880,uu____5881,uu____5882,uu____5883,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5885;
              FStar_Syntax_Syntax.sigquals = uu____5886;
              FStar_Syntax_Syntax.sigmeta = uu____5887;
              FStar_Syntax_Syntax.sigattrs = uu____5888;_},uu____5889),uu____5890)
          -> (true, dcs)
      | uu____5921 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5941 = lookup_qname env lid in
      match uu____5941 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5952,uu____5953,uu____5954,l,uu____5956,uu____5957);
              FStar_Syntax_Syntax.sigrng = uu____5958;
              FStar_Syntax_Syntax.sigquals = uu____5959;
              FStar_Syntax_Syntax.sigmeta = uu____5960;
              FStar_Syntax_Syntax.sigattrs = uu____5961;_},uu____5962),uu____5963)
          -> l
      | uu____5991 ->
          let uu____6002 =
            let uu____6003 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____6003 in
          failwith uu____6002
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
        let uu____6031 = lookup_qname env lid in
        match uu____6031 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____6046) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____6072,lbs),uu____6074) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____6092 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____6092
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____6113 -> FStar_Pervasives_Native.None)
        | uu____6116 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____6139 = lookup_qname env ftv in
      match uu____6139 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____6152) ->
          let uu____6175 = effect_signature se in
          (match uu____6175 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____6186,t),r) ->
               let uu____6195 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____6195)
      | uu____6196 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____6215 = try_lookup_effect_lid env ftv in
      match uu____6215 with
      | FStar_Pervasives_Native.None  ->
          let uu____6217 =
            let uu____6218 =
              let uu____6221 = name_not_found ftv in
              (uu____6221, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____6218 in
          raise uu____6217
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
        let uu____6238 = lookup_qname env lid0 in
        match uu____6238 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____6256);
                FStar_Syntax_Syntax.sigrng = uu____6257;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____6259;
                FStar_Syntax_Syntax.sigattrs = uu____6260;_},FStar_Pervasives_Native.None
              ),uu____6261)
            ->
            let lid1 =
              let uu____6289 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____6289 in
            let uu____6290 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___107_6293  ->
                      match uu___107_6293 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____6294 -> false)) in
            if uu____6290
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____6311 =
                      let uu____6312 =
                        let uu____6313 = get_range env in
                        FStar_Range.string_of_range uu____6313 in
                      let uu____6314 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____6315 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____6312 uu____6314 uu____6315 in
                    failwith uu____6311) in
               match (binders, univs1) with
               | ([],uu____6323) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____6332,uu____6333::uu____6334::uu____6335) ->
                   let uu____6338 =
                     let uu____6339 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____6340 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____6339 uu____6340 in
                   failwith uu____6338
               | uu____6348 ->
                   let uu____6351 =
                     let uu____6354 =
                       let uu____6355 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____6355) in
                     inst_tscheme_with uu____6354 insts in
                   (match uu____6351 with
                    | (uu____6363,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____6366 =
                          let uu____6367 = FStar_Syntax_Subst.compress t1 in
                          uu____6367.FStar_Syntax_Syntax.n in
                        (match uu____6366 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____6397 -> failwith "Impossible")))
        | uu____6401 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6429 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____6429 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____6436,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____6441 = find1 l2 in
            (match uu____6441 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____6446 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____6446 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____6449 = find1 l in
            (match uu____6449 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____6463 = lookup_qname env l1 in
      match uu____6463 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6475;
              FStar_Syntax_Syntax.sigrng = uu____6476;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6478;
              FStar_Syntax_Syntax.sigattrs = uu____6479;_},uu____6480),uu____6481)
          -> q
      | uu____6507 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6533 =
          let uu____6534 =
            let uu____6535 = FStar_Util.string_of_int i in
            let uu____6536 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6535 uu____6536 in
          failwith uu____6534 in
        let uu____6537 = lookup_datacon env lid in
        match uu____6537 with
        | (uu____6540,t) ->
            let uu____6542 =
              let uu____6543 = FStar_Syntax_Subst.compress t in
              uu____6543.FStar_Syntax_Syntax.n in
            (match uu____6542 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6547) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____6570 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____6570
                      FStar_Pervasives_Native.fst)
             | uu____6575 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6584 = lookup_qname env l in
      match uu____6584 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6595,uu____6596,uu____6597);
              FStar_Syntax_Syntax.sigrng = uu____6598;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6600;
              FStar_Syntax_Syntax.sigattrs = uu____6601;_},uu____6602),uu____6603)
          ->
          FStar_Util.for_some
            (fun uu___108_6631  ->
               match uu___108_6631 with
               | FStar_Syntax_Syntax.Projector uu____6632 -> true
               | uu____6635 -> false) quals
      | uu____6636 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6655 = lookup_qname env lid in
      match uu____6655 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6666,uu____6667,uu____6668,uu____6669,uu____6670,uu____6671);
              FStar_Syntax_Syntax.sigrng = uu____6672;
              FStar_Syntax_Syntax.sigquals = uu____6673;
              FStar_Syntax_Syntax.sigmeta = uu____6674;
              FStar_Syntax_Syntax.sigattrs = uu____6675;_},uu____6676),uu____6677)
          -> true
      | uu____6705 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6724 = lookup_qname env lid in
      match uu____6724 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6735,uu____6736,uu____6737,uu____6738,uu____6739,uu____6740);
              FStar_Syntax_Syntax.sigrng = uu____6741;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6743;
              FStar_Syntax_Syntax.sigattrs = uu____6744;_},uu____6745),uu____6746)
          ->
          FStar_Util.for_some
            (fun uu___109_6778  ->
               match uu___109_6778 with
               | FStar_Syntax_Syntax.RecordType uu____6779 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6784 -> true
               | uu____6789 -> false) quals
      | uu____6790 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6809 = lookup_qname env lid in
      match uu____6809 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6820,uu____6821);
              FStar_Syntax_Syntax.sigrng = uu____6822;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6824;
              FStar_Syntax_Syntax.sigattrs = uu____6825;_},uu____6826),uu____6827)
          ->
          FStar_Util.for_some
            (fun uu___110_6857  ->
               match uu___110_6857 with
               | FStar_Syntax_Syntax.Action uu____6858 -> true
               | uu____6859 -> false) quals
      | uu____6860 -> false
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
      let uu____6881 =
        let uu____6882 = FStar_Syntax_Util.un_uinst head1 in
        uu____6882.FStar_Syntax_Syntax.n in
      match uu____6881 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6886 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____6926 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____6935) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6944 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6948 ->
                 FStar_Pervasives_Native.Some true
             | uu____6957 -> FStar_Pervasives_Native.Some false) in
      let uu____6958 =
        let uu____6960 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6960 mapper in
      match uu____6958 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6989 = lookup_qname env lid in
      match uu____6989 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____7000,uu____7001,tps,uu____7003,uu____7004,uu____7005);
              FStar_Syntax_Syntax.sigrng = uu____7006;
              FStar_Syntax_Syntax.sigquals = uu____7007;
              FStar_Syntax_Syntax.sigmeta = uu____7008;
              FStar_Syntax_Syntax.sigattrs = uu____7009;_},uu____7010),uu____7011)
          -> FStar_List.length tps
      | uu____7045 ->
          let uu____7056 =
            let uu____7057 =
              let uu____7060 = name_not_found lid in
              (uu____7060, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7057 in
          raise uu____7056
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
           (fun uu____7087  ->
              match uu____7087 with
              | (d,uu____7092) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____7103 = effect_decl_opt env l in
      match uu____7103 with
      | FStar_Pervasives_Native.None  ->
          let uu____7111 =
            let uu____7112 =
              let uu____7115 = name_not_found l in
              (uu____7115, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7112 in
          raise uu____7111
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
            (let uu____7165 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____7195  ->
                       match uu____7195 with
                       | (m1,m2,uu____7203,uu____7204,uu____7205) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____7165 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7214 =
                   let uu____7215 =
                     let uu____7218 =
                       let uu____7219 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____7220 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____7219
                         uu____7220 in
                     (uu____7218, (env.range)) in
                   FStar_Errors.Error uu____7215 in
                 raise uu____7214
             | FStar_Pervasives_Native.Some (uu____7224,uu____7225,m3,j1,j2)
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
  let uu____7278 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____7293  ->
            match uu____7293 with
            | (d,uu____7297) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____7278 with
  | FStar_Pervasives_Native.None  ->
      let uu____7304 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____7304
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____7313 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____7313 with
       | (uu____7320,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____7328)::(wp,uu____7330)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____7352 -> failwith "Impossible"))
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
                 let uu____7394 = get_range env in
                 let uu____7395 =
                   let uu____7398 =
                     let uu____7399 =
                       let uu____7409 =
                         let uu____7411 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____7411] in
                       (null_wp, uu____7409) in
                     FStar_Syntax_Syntax.Tm_app uu____7399 in
                   FStar_Syntax_Syntax.mk uu____7398 in
                 uu____7395 FStar_Pervasives_Native.None uu____7394 in
               let uu____7421 =
                 let uu____7422 =
                   let uu____7428 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____7428] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____7422;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____7421)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_7439 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_7439.order);
              joins = (uu___121_7439.joins)
            } in
          let uu___122_7444 = env in
          {
            solver = (uu___122_7444.solver);
            range = (uu___122_7444.range);
            curmodule = (uu___122_7444.curmodule);
            gamma = (uu___122_7444.gamma);
            gamma_cache = (uu___122_7444.gamma_cache);
            modules = (uu___122_7444.modules);
            expected_typ = (uu___122_7444.expected_typ);
            sigtab = (uu___122_7444.sigtab);
            is_pattern = (uu___122_7444.is_pattern);
            instantiate_imp = (uu___122_7444.instantiate_imp);
            effects;
            generalize = (uu___122_7444.generalize);
            letrecs = (uu___122_7444.letrecs);
            top_level = (uu___122_7444.top_level);
            check_uvars = (uu___122_7444.check_uvars);
            use_eq = (uu___122_7444.use_eq);
            is_iface = (uu___122_7444.is_iface);
            admit = (uu___122_7444.admit);
            lax = (uu___122_7444.lax);
            lax_universes = (uu___122_7444.lax_universes);
            type_of = (uu___122_7444.type_of);
            universe_of = (uu___122_7444.universe_of);
            use_bv_sorts = (uu___122_7444.use_bv_sorts);
            qname_and_index = (uu___122_7444.qname_and_index);
            proof_ns = (uu___122_7444.proof_ns);
            synth = (uu___122_7444.synth);
            is_native_tactic = (uu___122_7444.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____7461 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____7461 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7545 = (e1.mlift).mlift_wp t wp in
                              let uu____7546 = l1 t wp e in
                              l2 t uu____7545 uu____7546))
                | uu____7547 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7582 = inst_tscheme lift_t in
            match uu____7582 with
            | (uu____7587,lift_t1) ->
                let uu____7589 =
                  let uu____7592 =
                    let uu____7593 =
                      let uu____7603 =
                        let uu____7605 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7606 =
                          let uu____7608 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7608] in
                        uu____7605 :: uu____7606 in
                      (lift_t1, uu____7603) in
                    FStar_Syntax_Syntax.Tm_app uu____7593 in
                  FStar_Syntax_Syntax.mk uu____7592 in
                uu____7589 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7653 = inst_tscheme lift_t in
            match uu____7653 with
            | (uu____7658,lift_t1) ->
                let uu____7660 =
                  let uu____7663 =
                    let uu____7664 =
                      let uu____7674 =
                        let uu____7676 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7677 =
                          let uu____7679 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7680 =
                            let uu____7682 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7682] in
                          uu____7679 :: uu____7680 in
                        uu____7676 :: uu____7677 in
                      (lift_t1, uu____7674) in
                    FStar_Syntax_Syntax.Tm_app uu____7664 in
                  FStar_Syntax_Syntax.mk uu____7663 in
                uu____7660 FStar_Pervasives_Native.None
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
              let uu____7723 =
                let uu____7724 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7724
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____7723 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7728 =
              let uu____7729 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7729 in
            let uu____7730 =
              let uu____7731 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7748 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7748) in
              FStar_Util.dflt "none" uu____7731 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7728
              uu____7730 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7764  ->
                    match uu____7764 with
                    | (e,uu____7769) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7782 =
            match uu____7782 with
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
              let uu____7808 =
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
                                    (let uu____7822 =
                                       let uu____7827 =
                                         find_edge order1 (i, k) in
                                       let uu____7829 =
                                         find_edge order1 (k, j) in
                                       (uu____7827, uu____7829) in
                                     match uu____7822 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____7838 = compose_edges e1 e2 in
                                         [uu____7838]
                                     | uu____7839 -> []))))) in
              FStar_List.append order1 uu____7808 in
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
                   let uu____7859 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____7861 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7861
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7859
                   then
                     let uu____7864 =
                       let uu____7865 =
                         let uu____7868 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7869 = get_range env in
                         (uu____7868, uu____7869) in
                       FStar_Errors.Error uu____7865 in
                     raise uu____7864
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
                                            let uu____7940 =
                                              let uu____7945 =
                                                find_edge order2 (i, k) in
                                              let uu____7947 =
                                                find_edge order2 (j, k) in
                                              (uu____7945, uu____7947) in
                                            match uu____7940 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____7970,uu____7971)
                                                     ->
                                                     let uu____7975 =
                                                       let uu____7978 =
                                                         let uu____7979 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7979 in
                                                       let uu____7981 =
                                                         let uu____7982 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7982 in
                                                       (uu____7978,
                                                         uu____7981) in
                                                     (match uu____7975 with
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
                                            | uu____8001 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___123_8040 = env.effects in
              { decls = (uu___123_8040.decls); order = order2; joins } in
            let uu___124_8041 = env in
            {
              solver = (uu___124_8041.solver);
              range = (uu___124_8041.range);
              curmodule = (uu___124_8041.curmodule);
              gamma = (uu___124_8041.gamma);
              gamma_cache = (uu___124_8041.gamma_cache);
              modules = (uu___124_8041.modules);
              expected_typ = (uu___124_8041.expected_typ);
              sigtab = (uu___124_8041.sigtab);
              is_pattern = (uu___124_8041.is_pattern);
              instantiate_imp = (uu___124_8041.instantiate_imp);
              effects;
              generalize = (uu___124_8041.generalize);
              letrecs = (uu___124_8041.letrecs);
              top_level = (uu___124_8041.top_level);
              check_uvars = (uu___124_8041.check_uvars);
              use_eq = (uu___124_8041.use_eq);
              is_iface = (uu___124_8041.is_iface);
              admit = (uu___124_8041.admit);
              lax = (uu___124_8041.lax);
              lax_universes = (uu___124_8041.lax_universes);
              type_of = (uu___124_8041.type_of);
              universe_of = (uu___124_8041.universe_of);
              use_bv_sorts = (uu___124_8041.use_bv_sorts);
              qname_and_index = (uu___124_8041.qname_and_index);
              proof_ns = (uu___124_8041.proof_ns);
              synth = (uu___124_8041.synth);
              is_native_tactic = (uu___124_8041.is_native_tactic)
            }))
      | uu____8042 -> env
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
        | uu____8066 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____8076 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____8076 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____8086 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____8086 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____8108 =
                     let uu____8109 =
                       let uu____8112 =
                         let uu____8113 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____8122 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____8133 =
                           let uu____8134 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____8134 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____8113 uu____8122 uu____8133 in
                       (uu____8112, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____8109 in
                   raise uu____8108)
                else ();
                (let inst1 =
                   let uu____8138 =
                     let uu____8144 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____8144 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____8157  ->
                        fun uu____8158  ->
                          match (uu____8157, uu____8158) with
                          | ((x,uu____8172),(t,uu____8174)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____8138 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____8189 =
                     let uu___125_8190 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_8190.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_8190.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_8190.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_8190.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____8189
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____8225 =
    let uu____8230 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____8230 in
  match uu____8225 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
      let uu____8246 =
        only_reifiable &&
          (let uu____8248 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____8248) in
      if uu____8246
      then FStar_Pervasives_Native.None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
         | uu____8261 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____8263 =
               let uu____8272 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____8272) in
             (match uu____8263 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____8306 =
                    let uu____8309 = get_range env in
                    let uu____8310 =
                      let uu____8313 =
                        let uu____8314 =
                          let uu____8324 =
                            let uu____8326 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____8326; wp] in
                          (repr, uu____8324) in
                        FStar_Syntax_Syntax.Tm_app uu____8314 in
                      FStar_Syntax_Syntax.mk uu____8313 in
                    uu____8310 FStar_Pervasives_Native.None uu____8309 in
                  FStar_Pervasives_Native.Some uu____8306))
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
          let uu____8376 =
            let uu____8377 =
              let uu____8380 =
                let uu____8381 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____8381 in
              let uu____8382 = get_range env in (uu____8380, uu____8382) in
            FStar_Errors.Error uu____8377 in
          raise uu____8376 in
        let uu____8383 = effect_repr_aux true env c u_c in
        match uu____8383 with
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
      | uu____8421 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____8430 =
        let uu____8431 = FStar_Syntax_Subst.compress t in
        uu____8431.FStar_Syntax_Syntax.n in
      match uu____8430 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____8434,c) ->
          is_reifiable_comp env c
      | uu____8446 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____8466)::uu____8467 -> x :: rest
        | (Binding_sig_inst uu____8472)::uu____8473 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____8482 = push1 x rest1 in local :: uu____8482 in
      let uu___126_8484 = env in
      let uu____8485 = push1 s env.gamma in
      {
        solver = (uu___126_8484.solver);
        range = (uu___126_8484.range);
        curmodule = (uu___126_8484.curmodule);
        gamma = uu____8485;
        gamma_cache = (uu___126_8484.gamma_cache);
        modules = (uu___126_8484.modules);
        expected_typ = (uu___126_8484.expected_typ);
        sigtab = (uu___126_8484.sigtab);
        is_pattern = (uu___126_8484.is_pattern);
        instantiate_imp = (uu___126_8484.instantiate_imp);
        effects = (uu___126_8484.effects);
        generalize = (uu___126_8484.generalize);
        letrecs = (uu___126_8484.letrecs);
        top_level = (uu___126_8484.top_level);
        check_uvars = (uu___126_8484.check_uvars);
        use_eq = (uu___126_8484.use_eq);
        is_iface = (uu___126_8484.is_iface);
        admit = (uu___126_8484.admit);
        lax = (uu___126_8484.lax);
        lax_universes = (uu___126_8484.lax_universes);
        type_of = (uu___126_8484.type_of);
        universe_of = (uu___126_8484.universe_of);
        use_bv_sorts = (uu___126_8484.use_bv_sorts);
        qname_and_index = (uu___126_8484.qname_and_index);
        proof_ns = (uu___126_8484.proof_ns);
        synth = (uu___126_8484.synth);
        is_native_tactic = (uu___126_8484.is_native_tactic)
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
      let uu___127_8519 = env in
      {
        solver = (uu___127_8519.solver);
        range = (uu___127_8519.range);
        curmodule = (uu___127_8519.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___127_8519.gamma_cache);
        modules = (uu___127_8519.modules);
        expected_typ = (uu___127_8519.expected_typ);
        sigtab = (uu___127_8519.sigtab);
        is_pattern = (uu___127_8519.is_pattern);
        instantiate_imp = (uu___127_8519.instantiate_imp);
        effects = (uu___127_8519.effects);
        generalize = (uu___127_8519.generalize);
        letrecs = (uu___127_8519.letrecs);
        top_level = (uu___127_8519.top_level);
        check_uvars = (uu___127_8519.check_uvars);
        use_eq = (uu___127_8519.use_eq);
        is_iface = (uu___127_8519.is_iface);
        admit = (uu___127_8519.admit);
        lax = (uu___127_8519.lax);
        lax_universes = (uu___127_8519.lax_universes);
        type_of = (uu___127_8519.type_of);
        universe_of = (uu___127_8519.universe_of);
        use_bv_sorts = (uu___127_8519.use_bv_sorts);
        qname_and_index = (uu___127_8519.qname_and_index);
        proof_ns = (uu___127_8519.proof_ns);
        synth = (uu___127_8519.synth);
        is_native_tactic = (uu___127_8519.is_native_tactic)
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
            (let uu___128_8544 = env in
             {
               solver = (uu___128_8544.solver);
               range = (uu___128_8544.range);
               curmodule = (uu___128_8544.curmodule);
               gamma = rest;
               gamma_cache = (uu___128_8544.gamma_cache);
               modules = (uu___128_8544.modules);
               expected_typ = (uu___128_8544.expected_typ);
               sigtab = (uu___128_8544.sigtab);
               is_pattern = (uu___128_8544.is_pattern);
               instantiate_imp = (uu___128_8544.instantiate_imp);
               effects = (uu___128_8544.effects);
               generalize = (uu___128_8544.generalize);
               letrecs = (uu___128_8544.letrecs);
               top_level = (uu___128_8544.top_level);
               check_uvars = (uu___128_8544.check_uvars);
               use_eq = (uu___128_8544.use_eq);
               is_iface = (uu___128_8544.is_iface);
               admit = (uu___128_8544.admit);
               lax = (uu___128_8544.lax);
               lax_universes = (uu___128_8544.lax_universes);
               type_of = (uu___128_8544.type_of);
               universe_of = (uu___128_8544.universe_of);
               use_bv_sorts = (uu___128_8544.use_bv_sorts);
               qname_and_index = (uu___128_8544.qname_and_index);
               proof_ns = (uu___128_8544.proof_ns);
               synth = (uu___128_8544.synth);
               is_native_tactic = (uu___128_8544.is_native_tactic)
             }))
    | uu____8545 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8564  ->
             match uu____8564 with | (x,uu____8568) -> push_bv env1 x) env bs
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
            let uu___129_8591 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_8591.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_8591.FStar_Syntax_Syntax.index);
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
      (let uu___130_8622 = env in
       {
         solver = (uu___130_8622.solver);
         range = (uu___130_8622.range);
         curmodule = (uu___130_8622.curmodule);
         gamma = [];
         gamma_cache = (uu___130_8622.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_8622.sigtab);
         is_pattern = (uu___130_8622.is_pattern);
         instantiate_imp = (uu___130_8622.instantiate_imp);
         effects = (uu___130_8622.effects);
         generalize = (uu___130_8622.generalize);
         letrecs = (uu___130_8622.letrecs);
         top_level = (uu___130_8622.top_level);
         check_uvars = (uu___130_8622.check_uvars);
         use_eq = (uu___130_8622.use_eq);
         is_iface = (uu___130_8622.is_iface);
         admit = (uu___130_8622.admit);
         lax = (uu___130_8622.lax);
         lax_universes = (uu___130_8622.lax_universes);
         type_of = (uu___130_8622.type_of);
         universe_of = (uu___130_8622.universe_of);
         use_bv_sorts = (uu___130_8622.use_bv_sorts);
         qname_and_index = (uu___130_8622.qname_and_index);
         proof_ns = (uu___130_8622.proof_ns);
         synth = (uu___130_8622.synth);
         is_native_tactic = (uu___130_8622.is_native_tactic)
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
        let uu____8653 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8653 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8669 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8669)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___131_8681 = env in
      {
        solver = (uu___131_8681.solver);
        range = (uu___131_8681.range);
        curmodule = (uu___131_8681.curmodule);
        gamma = (uu___131_8681.gamma);
        gamma_cache = (uu___131_8681.gamma_cache);
        modules = (uu___131_8681.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_8681.sigtab);
        is_pattern = (uu___131_8681.is_pattern);
        instantiate_imp = (uu___131_8681.instantiate_imp);
        effects = (uu___131_8681.effects);
        generalize = (uu___131_8681.generalize);
        letrecs = (uu___131_8681.letrecs);
        top_level = (uu___131_8681.top_level);
        check_uvars = (uu___131_8681.check_uvars);
        use_eq = false;
        is_iface = (uu___131_8681.is_iface);
        admit = (uu___131_8681.admit);
        lax = (uu___131_8681.lax);
        lax_universes = (uu___131_8681.lax_universes);
        type_of = (uu___131_8681.type_of);
        universe_of = (uu___131_8681.universe_of);
        use_bv_sorts = (uu___131_8681.use_bv_sorts);
        qname_and_index = (uu___131_8681.qname_and_index);
        proof_ns = (uu___131_8681.proof_ns);
        synth = (uu___131_8681.synth);
        is_native_tactic = (uu___131_8681.is_native_tactic)
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
    let uu____8699 = expected_typ env_ in
    ((let uu___132_8703 = env_ in
      {
        solver = (uu___132_8703.solver);
        range = (uu___132_8703.range);
        curmodule = (uu___132_8703.curmodule);
        gamma = (uu___132_8703.gamma);
        gamma_cache = (uu___132_8703.gamma_cache);
        modules = (uu___132_8703.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_8703.sigtab);
        is_pattern = (uu___132_8703.is_pattern);
        instantiate_imp = (uu___132_8703.instantiate_imp);
        effects = (uu___132_8703.effects);
        generalize = (uu___132_8703.generalize);
        letrecs = (uu___132_8703.letrecs);
        top_level = (uu___132_8703.top_level);
        check_uvars = (uu___132_8703.check_uvars);
        use_eq = false;
        is_iface = (uu___132_8703.is_iface);
        admit = (uu___132_8703.admit);
        lax = (uu___132_8703.lax);
        lax_universes = (uu___132_8703.lax_universes);
        type_of = (uu___132_8703.type_of);
        universe_of = (uu___132_8703.universe_of);
        use_bv_sorts = (uu___132_8703.use_bv_sorts);
        qname_and_index = (uu___132_8703.qname_and_index);
        proof_ns = (uu___132_8703.proof_ns);
        synth = (uu___132_8703.synth);
        is_native_tactic = (uu___132_8703.is_native_tactic)
      }), uu____8699)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____8716 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___111_8723  ->
                    match uu___111_8723 with
                    | Binding_sig (uu____8725,se) -> [se]
                    | uu____8729 -> [])) in
          FStar_All.pipe_right uu____8716 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___133_8734 = env in
       {
         solver = (uu___133_8734.solver);
         range = (uu___133_8734.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___133_8734.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_8734.expected_typ);
         sigtab = (uu___133_8734.sigtab);
         is_pattern = (uu___133_8734.is_pattern);
         instantiate_imp = (uu___133_8734.instantiate_imp);
         effects = (uu___133_8734.effects);
         generalize = (uu___133_8734.generalize);
         letrecs = (uu___133_8734.letrecs);
         top_level = (uu___133_8734.top_level);
         check_uvars = (uu___133_8734.check_uvars);
         use_eq = (uu___133_8734.use_eq);
         is_iface = (uu___133_8734.is_iface);
         admit = (uu___133_8734.admit);
         lax = (uu___133_8734.lax);
         lax_universes = (uu___133_8734.lax_universes);
         type_of = (uu___133_8734.type_of);
         universe_of = (uu___133_8734.universe_of);
         use_bv_sorts = (uu___133_8734.use_bv_sorts);
         qname_and_index = (uu___133_8734.qname_and_index);
         proof_ns = (uu___133_8734.proof_ns);
         synth = (uu___133_8734.synth);
         is_native_tactic = (uu___133_8734.is_native_tactic)
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
      | (Binding_univ uu____8785)::tl1 -> aux out tl1
      | (Binding_lid (uu____8788,(uu____8789,t)))::tl1 ->
          let uu____8798 =
            let uu____8802 = FStar_Syntax_Free.uvars t in ext out uu____8802 in
          aux uu____8798 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8806;
            FStar_Syntax_Syntax.index = uu____8807;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8813 =
            let uu____8817 = FStar_Syntax_Free.uvars t in ext out uu____8817 in
          aux uu____8813 tl1
      | (Binding_sig uu____8821)::uu____8822 -> out
      | (Binding_sig_inst uu____8827)::uu____8828 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8866)::tl1 -> aux out tl1
      | (Binding_univ uu____8873)::tl1 -> aux out tl1
      | (Binding_lid (uu____8876,(uu____8877,t)))::tl1 ->
          let uu____8886 =
            let uu____8888 = FStar_Syntax_Free.univs t in ext out uu____8888 in
          aux uu____8886 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8890;
            FStar_Syntax_Syntax.index = uu____8891;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8897 =
            let uu____8899 = FStar_Syntax_Free.univs t in ext out uu____8899 in
          aux uu____8897 tl1
      | (Binding_sig uu____8901)::uu____8902 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8940)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8950 = FStar_Util.set_add uname out in aux uu____8950 tl1
      | (Binding_lid (uu____8952,(uu____8953,t)))::tl1 ->
          let uu____8962 =
            let uu____8964 = FStar_Syntax_Free.univnames t in
            ext out uu____8964 in
          aux uu____8962 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8966;
            FStar_Syntax_Syntax.index = uu____8967;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8973 =
            let uu____8975 = FStar_Syntax_Free.univnames t in
            ext out uu____8975 in
          aux uu____8973 tl1
      | (Binding_sig uu____8977)::uu____8978 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___112_8997  ->
            match uu___112_8997 with
            | Binding_var x -> [x]
            | Binding_lid uu____9000 -> []
            | Binding_sig uu____9003 -> []
            | Binding_univ uu____9007 -> []
            | Binding_sig_inst uu____9008 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____9019 =
      let uu____9021 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____9021
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____9019 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____9040 =
      let uu____9041 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___113_9048  ->
                match uu___113_9048 with
                | Binding_var x ->
                    let uu____9050 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____9050
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____9053) ->
                    let uu____9054 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____9054
                | Binding_sig (ls,uu____9056) ->
                    let uu____9059 =
                      let uu____9060 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____9060
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____9059
                | Binding_sig_inst (ls,uu____9066,uu____9067) ->
                    let uu____9070 =
                      let uu____9071 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____9071
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____9070)) in
      FStar_All.pipe_right uu____9041 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____9040 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____9085 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____9085
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____9112  ->
                 fun uu____9113  ->
                   match (uu____9112, uu____9113) with
                   | ((b1,uu____9123),(b2,uu____9125)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___114_9179  ->
             match uu___114_9179 with
             | Binding_sig (lids,uu____9183) -> FStar_List.append lids keys
             | uu____9186 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____9191  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____9218) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____9230,uu____9231) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____9255 = list_prefix p path1 in
            if uu____9255 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9267 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____9267
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___134_9290 = e in
            {
              solver = (uu___134_9290.solver);
              range = (uu___134_9290.range);
              curmodule = (uu___134_9290.curmodule);
              gamma = (uu___134_9290.gamma);
              gamma_cache = (uu___134_9290.gamma_cache);
              modules = (uu___134_9290.modules);
              expected_typ = (uu___134_9290.expected_typ);
              sigtab = (uu___134_9290.sigtab);
              is_pattern = (uu___134_9290.is_pattern);
              instantiate_imp = (uu___134_9290.instantiate_imp);
              effects = (uu___134_9290.effects);
              generalize = (uu___134_9290.generalize);
              letrecs = (uu___134_9290.letrecs);
              top_level = (uu___134_9290.top_level);
              check_uvars = (uu___134_9290.check_uvars);
              use_eq = (uu___134_9290.use_eq);
              is_iface = (uu___134_9290.is_iface);
              admit = (uu___134_9290.admit);
              lax = (uu___134_9290.lax);
              lax_universes = (uu___134_9290.lax_universes);
              type_of = (uu___134_9290.type_of);
              universe_of = (uu___134_9290.universe_of);
              use_bv_sorts = (uu___134_9290.use_bv_sorts);
              qname_and_index = (uu___134_9290.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___134_9290.synth);
              is_native_tactic = (uu___134_9290.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___135_9314 = e in
    {
      solver = (uu___135_9314.solver);
      range = (uu___135_9314.range);
      curmodule = (uu___135_9314.curmodule);
      gamma = (uu___135_9314.gamma);
      gamma_cache = (uu___135_9314.gamma_cache);
      modules = (uu___135_9314.modules);
      expected_typ = (uu___135_9314.expected_typ);
      sigtab = (uu___135_9314.sigtab);
      is_pattern = (uu___135_9314.is_pattern);
      instantiate_imp = (uu___135_9314.instantiate_imp);
      effects = (uu___135_9314.effects);
      generalize = (uu___135_9314.generalize);
      letrecs = (uu___135_9314.letrecs);
      top_level = (uu___135_9314.top_level);
      check_uvars = (uu___135_9314.check_uvars);
      use_eq = (uu___135_9314.use_eq);
      is_iface = (uu___135_9314.is_iface);
      admit = (uu___135_9314.admit);
      lax = (uu___135_9314.lax);
      lax_universes = (uu___135_9314.lax_universes);
      type_of = (uu___135_9314.type_of);
      universe_of = (uu___135_9314.universe_of);
      use_bv_sorts = (uu___135_9314.use_bv_sorts);
      qname_and_index = (uu___135_9314.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___135_9314.synth);
      is_native_tactic = (uu___135_9314.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____9324::rest ->
        let uu___136_9327 = e in
        {
          solver = (uu___136_9327.solver);
          range = (uu___136_9327.range);
          curmodule = (uu___136_9327.curmodule);
          gamma = (uu___136_9327.gamma);
          gamma_cache = (uu___136_9327.gamma_cache);
          modules = (uu___136_9327.modules);
          expected_typ = (uu___136_9327.expected_typ);
          sigtab = (uu___136_9327.sigtab);
          is_pattern = (uu___136_9327.is_pattern);
          instantiate_imp = (uu___136_9327.instantiate_imp);
          effects = (uu___136_9327.effects);
          generalize = (uu___136_9327.generalize);
          letrecs = (uu___136_9327.letrecs);
          top_level = (uu___136_9327.top_level);
          check_uvars = (uu___136_9327.check_uvars);
          use_eq = (uu___136_9327.use_eq);
          is_iface = (uu___136_9327.is_iface);
          admit = (uu___136_9327.admit);
          lax = (uu___136_9327.lax);
          lax_universes = (uu___136_9327.lax_universes);
          type_of = (uu___136_9327.type_of);
          universe_of = (uu___136_9327.universe_of);
          use_bv_sorts = (uu___136_9327.use_bv_sorts);
          qname_and_index = (uu___136_9327.qname_and_index);
          proof_ns = rest;
          synth = (uu___136_9327.synth);
          is_native_tactic = (uu___136_9327.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___137_9340 = e in
      {
        solver = (uu___137_9340.solver);
        range = (uu___137_9340.range);
        curmodule = (uu___137_9340.curmodule);
        gamma = (uu___137_9340.gamma);
        gamma_cache = (uu___137_9340.gamma_cache);
        modules = (uu___137_9340.modules);
        expected_typ = (uu___137_9340.expected_typ);
        sigtab = (uu___137_9340.sigtab);
        is_pattern = (uu___137_9340.is_pattern);
        instantiate_imp = (uu___137_9340.instantiate_imp);
        effects = (uu___137_9340.effects);
        generalize = (uu___137_9340.generalize);
        letrecs = (uu___137_9340.letrecs);
        top_level = (uu___137_9340.top_level);
        check_uvars = (uu___137_9340.check_uvars);
        use_eq = (uu___137_9340.use_eq);
        is_iface = (uu___137_9340.is_iface);
        admit = (uu___137_9340.admit);
        lax = (uu___137_9340.lax);
        lax_universes = (uu___137_9340.lax_universes);
        type_of = (uu___137_9340.type_of);
        universe_of = (uu___137_9340.universe_of);
        use_bv_sorts = (uu___137_9340.use_bv_sorts);
        qname_and_index = (uu___137_9340.qname_and_index);
        proof_ns = ns;
        synth = (uu___137_9340.synth);
        is_native_tactic = (uu___137_9340.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____9359 =
        FStar_List.map
          (fun fpns  ->
             let uu____9372 =
               let uu____9373 =
                 let uu____9374 =
                   FStar_List.map
                     (fun uu____9382  ->
                        match uu____9382 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____9374 in
               Prims.strcat uu____9373 "]" in
             Prims.strcat "[" uu____9372) pns in
      FStar_String.concat ";" uu____9359 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____9393  -> ());
    push = (fun uu____9395  -> ());
    pop = (fun uu____9397  -> ());
    mark = (fun uu____9399  -> ());
    reset_mark = (fun uu____9401  -> ());
    commit_mark = (fun uu____9403  -> ());
    encode_modul = (fun uu____9406  -> fun uu____9407  -> ());
    encode_sig = (fun uu____9410  -> fun uu____9411  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____9417 =
             let uu____9421 = FStar_Options.peek () in (e, g, uu____9421) in
           [uu____9417]);
    solve = (fun uu____9431  -> fun uu____9432  -> fun uu____9433  -> ());
    is_trivial = (fun uu____9439  -> fun uu____9440  -> false);
    finish = (fun uu____9442  -> ());
    refresh = (fun uu____9444  -> ())
  }