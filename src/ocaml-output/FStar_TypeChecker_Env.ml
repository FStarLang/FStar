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
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___105_4744  ->
           match uu___105_4744 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____4754 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____4776,lb::[]),uu____4778) ->
          let uu____4785 =
            let uu____4790 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____4795 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____4790, uu____4795) in
          FStar_Pervasives_Native.Some uu____4785
      | FStar_Syntax_Syntax.Sig_let ((uu____4802,lbs),uu____4804) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____4824 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____4831 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____4831
                   then
                     let uu____4837 =
                       let uu____4842 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____4847 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____4842, uu____4847) in
                     FStar_Pervasives_Native.Some uu____4837
                   else FStar_Pervasives_Native.None)
      | uu____4859 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____4879 =
          let uu____4884 =
            let uu____4887 =
              let uu____4888 =
                let uu____4890 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____4890 in
              ((ne.FStar_Syntax_Syntax.univs), uu____4888) in
            inst_tscheme uu____4887 in
          (uu____4884, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____4879
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____4902,uu____4903) ->
        let uu____4906 =
          let uu____4911 =
            let uu____4914 =
              let uu____4915 =
                let uu____4917 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____4917 in
              (us, uu____4915) in
            inst_tscheme uu____4914 in
          (uu____4911, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____4906
    | uu____4926 -> FStar_Pervasives_Native.None
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
      let mapper uu____4962 =
        match uu____4962 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____5012,uvs,t,uu____5015,uu____5016,uu____5017);
                    FStar_Syntax_Syntax.sigrng = uu____5018;
                    FStar_Syntax_Syntax.sigquals = uu____5019;
                    FStar_Syntax_Syntax.sigmeta = uu____5020;
                    FStar_Syntax_Syntax.sigattrs = uu____5021;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____5032 =
                   let uu____5037 = inst_tscheme (uvs, t) in
                   (uu____5037, rng) in
                 FStar_Pervasives_Native.Some uu____5032
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____5049;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____5051;
                    FStar_Syntax_Syntax.sigattrs = uu____5052;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____5061 =
                   let uu____5062 = in_cur_mod env l in uu____5062 = Yes in
                 if uu____5061
                 then
                   let uu____5068 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____5068
                    then
                      let uu____5075 =
                        let uu____5080 = inst_tscheme (uvs, t) in
                        (uu____5080, rng) in
                      FStar_Pervasives_Native.Some uu____5075
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____5095 =
                      let uu____5100 = inst_tscheme (uvs, t) in
                      (uu____5100, rng) in
                    FStar_Pervasives_Native.Some uu____5095)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5113,uu____5114);
                    FStar_Syntax_Syntax.sigrng = uu____5115;
                    FStar_Syntax_Syntax.sigquals = uu____5116;
                    FStar_Syntax_Syntax.sigmeta = uu____5117;
                    FStar_Syntax_Syntax.sigattrs = uu____5118;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____5138 =
                        let uu____5143 = inst_tscheme (uvs, k) in
                        (uu____5143, rng) in
                      FStar_Pervasives_Native.Some uu____5138
                  | uu____5152 ->
                      let uu____5153 =
                        let uu____5158 =
                          let uu____5161 =
                            let uu____5162 =
                              let uu____5164 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5164 in
                            (uvs, uu____5162) in
                          inst_tscheme uu____5161 in
                        (uu____5158, rng) in
                      FStar_Pervasives_Native.Some uu____5153)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____5177,uu____5178);
                    FStar_Syntax_Syntax.sigrng = uu____5179;
                    FStar_Syntax_Syntax.sigquals = uu____5180;
                    FStar_Syntax_Syntax.sigmeta = uu____5181;
                    FStar_Syntax_Syntax.sigattrs = uu____5182;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____5203 =
                        let uu____5208 = inst_tscheme_with (uvs, k) us in
                        (uu____5208, rng) in
                      FStar_Pervasives_Native.Some uu____5203
                  | uu____5217 ->
                      let uu____5218 =
                        let uu____5223 =
                          let uu____5226 =
                            let uu____5227 =
                              let uu____5229 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____5229 in
                            (uvs, uu____5227) in
                          inst_tscheme_with uu____5226 us in
                        (uu____5223, rng) in
                      FStar_Pervasives_Native.Some uu____5218)
             | FStar_Util.Inr se ->
                 let uu____5247 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____5258;
                        FStar_Syntax_Syntax.sigrng = uu____5259;
                        FStar_Syntax_Syntax.sigquals = uu____5260;
                        FStar_Syntax_Syntax.sigmeta = uu____5261;
                        FStar_Syntax_Syntax.sigattrs = uu____5262;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____5270 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____5247
                   (FStar_Util.map_option
                      (fun uu____5296  ->
                         match uu____5296 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____5313 =
        let uu____5319 = lookup_qname env lid in
        FStar_Util.bind_opt uu____5319 mapper in
      match uu____5313 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___120_5368 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___120_5368.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___120_5368.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____5388 = lookup_qname env l in
      match uu____5388 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____5408 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____5438 = try_lookup_bv env bv in
      match uu____5438 with
      | FStar_Pervasives_Native.None  ->
          let uu____5446 =
            let uu____5447 =
              let uu____5450 = variable_not_found bv in (uu____5450, bvr) in
            FStar_Errors.Error uu____5447 in
          raise uu____5446
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____5457 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____5458 = FStar_Range.set_use_range r bvr in
          (uu____5457, uu____5458)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____5472 = try_lookup_lid_aux env l in
      match uu____5472 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____5508 =
            let uu____5513 =
              let uu____5516 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____5516) in
            (uu____5513, r1) in
          FStar_Pervasives_Native.Some uu____5508
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____5535 = try_lookup_lid env l in
      match uu____5535 with
      | FStar_Pervasives_Native.None  ->
          let uu____5549 =
            let uu____5550 =
              let uu____5553 = name_not_found l in
              (uu____5553, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____5550 in
          raise uu____5549
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___106_5578  ->
              match uu___106_5578 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____5580 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____5593 = lookup_qname env lid in
      match uu____5593 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5608,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5611;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____5613;
              FStar_Syntax_Syntax.sigattrs = uu____5614;_},FStar_Pervasives_Native.None
            ),uu____5615)
          ->
          let uu____5640 =
            let uu____5646 =
              let uu____5649 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____5649) in
            (uu____5646, q) in
          FStar_Pervasives_Native.Some uu____5640
      | uu____5658 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5682 = lookup_qname env lid in
      match uu____5682 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____5695,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____5698;
              FStar_Syntax_Syntax.sigquals = uu____5699;
              FStar_Syntax_Syntax.sigmeta = uu____5700;
              FStar_Syntax_Syntax.sigattrs = uu____5701;_},FStar_Pervasives_Native.None
            ),uu____5702)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5727 ->
          let uu____5738 =
            let uu____5739 =
              let uu____5742 = name_not_found lid in
              (uu____5742, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5739 in
          raise uu____5738
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5755 = lookup_qname env lid in
      match uu____5755 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5768,uvs,t,uu____5771,uu____5772,uu____5773);
              FStar_Syntax_Syntax.sigrng = uu____5774;
              FStar_Syntax_Syntax.sigquals = uu____5775;
              FStar_Syntax_Syntax.sigmeta = uu____5776;
              FStar_Syntax_Syntax.sigattrs = uu____5777;_},FStar_Pervasives_Native.None
            ),uu____5778)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____5805 ->
          let uu____5816 =
            let uu____5817 =
              let uu____5820 = name_not_found lid in
              (uu____5820, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____5817 in
          raise uu____5816
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____5834 = lookup_qname env lid in
      match uu____5834 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____5848,uu____5849,uu____5850,uu____5851,uu____5852,dcs);
              FStar_Syntax_Syntax.sigrng = uu____5854;
              FStar_Syntax_Syntax.sigquals = uu____5855;
              FStar_Syntax_Syntax.sigmeta = uu____5856;
              FStar_Syntax_Syntax.sigattrs = uu____5857;_},uu____5858),uu____5859)
          -> (true, dcs)
      | uu____5890 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____5910 = lookup_qname env lid in
      match uu____5910 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____5921,uu____5922,uu____5923,l,uu____5925,uu____5926);
              FStar_Syntax_Syntax.sigrng = uu____5927;
              FStar_Syntax_Syntax.sigquals = uu____5928;
              FStar_Syntax_Syntax.sigmeta = uu____5929;
              FStar_Syntax_Syntax.sigattrs = uu____5930;_},uu____5931),uu____5932)
          -> l
      | uu____5960 ->
          let uu____5971 =
            let uu____5972 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____5972 in
          failwith uu____5971
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
        let uu____6000 = lookup_qname env lid in
        match uu____6000 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____6015) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____6041,lbs),uu____6043) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____6060 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____6060
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____6077 -> FStar_Pervasives_Native.None)
        | uu____6080 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____6103 = lookup_qname env ftv in
      match uu____6103 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____6116) ->
          let uu____6139 = effect_signature se in
          (match uu____6139 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____6150,t),r) ->
               let uu____6159 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____6159)
      | uu____6160 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____6179 = try_lookup_effect_lid env ftv in
      match uu____6179 with
      | FStar_Pervasives_Native.None  ->
          let uu____6181 =
            let uu____6182 =
              let uu____6185 = name_not_found ftv in
              (uu____6185, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____6182 in
          raise uu____6181
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
        let uu____6202 = lookup_qname env lid0 in
        match uu____6202 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____6220);
                FStar_Syntax_Syntax.sigrng = uu____6221;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____6223;
                FStar_Syntax_Syntax.sigattrs = uu____6224;_},FStar_Pervasives_Native.None
              ),uu____6225)
            ->
            let lid1 =
              let uu____6253 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____6253 in
            let uu____6254 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___107_6257  ->
                      match uu___107_6257 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____6258 -> false)) in
            if uu____6254
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____6275 =
                      let uu____6276 =
                        let uu____6277 = get_range env in
                        FStar_Range.string_of_range uu____6277 in
                      let uu____6278 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____6279 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____6276 uu____6278 uu____6279 in
                    failwith uu____6275) in
               match (binders, univs1) with
               | ([],uu____6287) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____6296,uu____6297::uu____6298::uu____6299) ->
                   let uu____6302 =
                     let uu____6303 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____6304 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____6303 uu____6304 in
                   failwith uu____6302
               | uu____6312 ->
                   let uu____6315 =
                     let uu____6318 =
                       let uu____6319 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____6319) in
                     inst_tscheme_with uu____6318 insts in
                   (match uu____6315 with
                    | (uu____6325,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____6328 =
                          let uu____6329 = FStar_Syntax_Subst.compress t1 in
                          uu____6329.FStar_Syntax_Syntax.n in
                        (match uu____6328 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____6354 -> failwith "Impossible")))
        | uu____6358 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____6386 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____6386 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____6393,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____6398 = find1 l2 in
            (match uu____6398 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____6403 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____6403 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____6406 = find1 l in
            (match uu____6406 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____6420 = lookup_qname env l1 in
      match uu____6420 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____6432;
              FStar_Syntax_Syntax.sigrng = uu____6433;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____6435;
              FStar_Syntax_Syntax.sigattrs = uu____6436;_},uu____6437),uu____6438)
          -> q
      | uu____6464 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____6490 =
          let uu____6491 =
            let uu____6492 = FStar_Util.string_of_int i in
            let uu____6493 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____6492 uu____6493 in
          failwith uu____6491 in
        let uu____6494 = lookup_datacon env lid in
        match uu____6494 with
        | (uu____6497,t) ->
            let uu____6499 =
              let uu____6500 = FStar_Syntax_Subst.compress t in
              uu____6500.FStar_Syntax_Syntax.n in
            (match uu____6499 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____6503) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____6524 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____6524
                      FStar_Pervasives_Native.fst)
             | uu____6529 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____6538 = lookup_qname env l in
      match uu____6538 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____6549,uu____6550,uu____6551);
              FStar_Syntax_Syntax.sigrng = uu____6552;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6554;
              FStar_Syntax_Syntax.sigattrs = uu____6555;_},uu____6556),uu____6557)
          ->
          FStar_Util.for_some
            (fun uu___108_6585  ->
               match uu___108_6585 with
               | FStar_Syntax_Syntax.Projector uu____6586 -> true
               | uu____6589 -> false) quals
      | uu____6590 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6609 = lookup_qname env lid in
      match uu____6609 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____6620,uu____6621,uu____6622,uu____6623,uu____6624,uu____6625);
              FStar_Syntax_Syntax.sigrng = uu____6626;
              FStar_Syntax_Syntax.sigquals = uu____6627;
              FStar_Syntax_Syntax.sigmeta = uu____6628;
              FStar_Syntax_Syntax.sigattrs = uu____6629;_},uu____6630),uu____6631)
          -> true
      | uu____6659 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6678 = lookup_qname env lid in
      match uu____6678 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6689,uu____6690,uu____6691,uu____6692,uu____6693,uu____6694);
              FStar_Syntax_Syntax.sigrng = uu____6695;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6697;
              FStar_Syntax_Syntax.sigattrs = uu____6698;_},uu____6699),uu____6700)
          ->
          FStar_Util.for_some
            (fun uu___109_6732  ->
               match uu___109_6732 with
               | FStar_Syntax_Syntax.RecordType uu____6733 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____6738 -> true
               | uu____6743 -> false) quals
      | uu____6744 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____6763 = lookup_qname env lid in
      match uu____6763 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____6774,uu____6775);
              FStar_Syntax_Syntax.sigrng = uu____6776;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____6778;
              FStar_Syntax_Syntax.sigattrs = uu____6779;_},uu____6780),uu____6781)
          ->
          FStar_Util.for_some
            (fun uu___110_6811  ->
               match uu___110_6811 with
               | FStar_Syntax_Syntax.Action uu____6812 -> true
               | uu____6813 -> false) quals
      | uu____6814 -> false
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
      let uu____6835 =
        let uu____6836 = FStar_Syntax_Util.un_uinst head1 in
        uu____6836.FStar_Syntax_Syntax.n in
      match uu____6835 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____6839 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____6879 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____6888) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____6897 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____6901 ->
                 FStar_Pervasives_Native.Some true
             | uu____6910 -> FStar_Pervasives_Native.Some false) in
      let uu____6911 =
        let uu____6913 = lookup_qname env lid in
        FStar_Util.bind_opt uu____6913 mapper in
      match uu____6911 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____6942 = lookup_qname env lid in
      match uu____6942 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____6953,uu____6954,tps,uu____6956,uu____6957,uu____6958);
              FStar_Syntax_Syntax.sigrng = uu____6959;
              FStar_Syntax_Syntax.sigquals = uu____6960;
              FStar_Syntax_Syntax.sigmeta = uu____6961;
              FStar_Syntax_Syntax.sigattrs = uu____6962;_},uu____6963),uu____6964)
          -> FStar_List.length tps
      | uu____6998 ->
          let uu____7009 =
            let uu____7010 =
              let uu____7013 = name_not_found lid in
              (uu____7013, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____7010 in
          raise uu____7009
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
           (fun uu____7040  ->
              match uu____7040 with
              | (d,uu____7045) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____7056 = effect_decl_opt env l in
      match uu____7056 with
      | FStar_Pervasives_Native.None  ->
          let uu____7064 =
            let uu____7065 =
              let uu____7068 = name_not_found l in
              (uu____7068, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____7065 in
          raise uu____7064
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
            (let uu____7118 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____7148  ->
                       match uu____7148 with
                       | (m1,m2,uu____7156,uu____7157,uu____7158) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____7118 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7167 =
                   let uu____7168 =
                     let uu____7171 =
                       let uu____7172 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____7173 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____7172
                         uu____7173 in
                     (uu____7171, (env.range)) in
                   FStar_Errors.Error uu____7168 in
                 raise uu____7167
             | FStar_Pervasives_Native.Some (uu____7177,uu____7178,m3,j1,j2)
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
  let uu____7230 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____7245  ->
            match uu____7245 with
            | (d,uu____7249) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____7230 with
  | FStar_Pervasives_Native.None  ->
      let uu____7255 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____7255
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____7263 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____7263 with
       | (uu____7269,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____7276)::(wp,uu____7278)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____7297 -> failwith "Impossible"))
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
                 let uu____7337 = get_range env in
                 let uu____7338 =
                   let uu____7340 =
                     let uu____7341 =
                       let uu____7349 =
                         let uu____7351 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____7351] in
                       (null_wp, uu____7349) in
                     FStar_Syntax_Syntax.Tm_app uu____7341 in
                   FStar_Syntax_Syntax.mk uu____7340 in
                 uu____7338 FStar_Pervasives_Native.None uu____7337 in
               let uu____7359 =
                 let uu____7360 =
                   let uu____7365 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____7365] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____7360;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____7359)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___121_7376 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___121_7376.order);
              joins = (uu___121_7376.joins)
            } in
          let uu___122_7381 = env in
          {
            solver = (uu___122_7381.solver);
            range = (uu___122_7381.range);
            curmodule = (uu___122_7381.curmodule);
            gamma = (uu___122_7381.gamma);
            gamma_cache = (uu___122_7381.gamma_cache);
            modules = (uu___122_7381.modules);
            expected_typ = (uu___122_7381.expected_typ);
            sigtab = (uu___122_7381.sigtab);
            is_pattern = (uu___122_7381.is_pattern);
            instantiate_imp = (uu___122_7381.instantiate_imp);
            effects;
            generalize = (uu___122_7381.generalize);
            letrecs = (uu___122_7381.letrecs);
            top_level = (uu___122_7381.top_level);
            check_uvars = (uu___122_7381.check_uvars);
            use_eq = (uu___122_7381.use_eq);
            is_iface = (uu___122_7381.is_iface);
            admit = (uu___122_7381.admit);
            lax = (uu___122_7381.lax);
            lax_universes = (uu___122_7381.lax_universes);
            type_of = (uu___122_7381.type_of);
            universe_of = (uu___122_7381.universe_of);
            use_bv_sorts = (uu___122_7381.use_bv_sorts);
            qname_and_index = (uu___122_7381.qname_and_index);
            proof_ns = (uu___122_7381.proof_ns);
            synth = (uu___122_7381.synth);
            is_native_tactic = (uu___122_7381.is_native_tactic)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____7398 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____7398 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____7482 = (e1.mlift).mlift_wp t wp in
                              let uu____7483 = l1 t wp e in
                              l2 t uu____7482 uu____7483))
                | uu____7484 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____7518 = inst_tscheme lift_t in
            match uu____7518 with
            | (uu____7522,lift_t1) ->
                let uu____7524 =
                  let uu____7526 =
                    let uu____7527 =
                      let uu____7535 =
                        let uu____7537 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7538 =
                          let uu____7540 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____7540] in
                        uu____7537 :: uu____7538 in
                      (lift_t1, uu____7535) in
                    FStar_Syntax_Syntax.Tm_app uu____7527 in
                  FStar_Syntax_Syntax.mk uu____7526 in
                uu____7524 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____7579 = inst_tscheme lift_t in
            match uu____7579 with
            | (uu____7583,lift_t1) ->
                let uu____7585 =
                  let uu____7587 =
                    let uu____7588 =
                      let uu____7596 =
                        let uu____7598 = FStar_Syntax_Syntax.as_arg r in
                        let uu____7599 =
                          let uu____7601 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____7602 =
                            let uu____7604 = FStar_Syntax_Syntax.as_arg e in
                            [uu____7604] in
                          uu____7601 :: uu____7602 in
                        uu____7598 :: uu____7599 in
                      (lift_t1, uu____7596) in
                    FStar_Syntax_Syntax.Tm_app uu____7588 in
                  FStar_Syntax_Syntax.mk uu____7587 in
                uu____7585 FStar_Pervasives_Native.None
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
              let uu____7641 =
                let uu____7642 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____7642
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____7641 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____7646 =
              let uu____7647 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____7647 in
            let uu____7648 =
              let uu____7649 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____7666 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____7666) in
              FStar_Util.dflt "none" uu____7649 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____7646
              uu____7648 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____7682  ->
                    match uu____7682 with
                    | (e,uu____7687) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____7700 =
            match uu____7700 with
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
              let uu____7726 =
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
                                    (let uu____7740 =
                                       let uu____7745 =
                                         find_edge order1 (i, k) in
                                       let uu____7747 =
                                         find_edge order1 (k, j) in
                                       (uu____7745, uu____7747) in
                                     match uu____7740 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____7756 = compose_edges e1 e2 in
                                         [uu____7756]
                                     | uu____7757 -> []))))) in
              FStar_List.append order1 uu____7726 in
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
                   let uu____7777 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____7779 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____7779
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____7777
                   then
                     let uu____7782 =
                       let uu____7783 =
                         let uu____7786 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____7787 = get_range env in
                         (uu____7786, uu____7787) in
                       FStar_Errors.Error uu____7783 in
                     raise uu____7782
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
                                            let uu____7858 =
                                              let uu____7863 =
                                                find_edge order2 (i, k) in
                                              let uu____7865 =
                                                find_edge order2 (j, k) in
                                              (uu____7863, uu____7865) in
                                            match uu____7858 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____7888,uu____7889)
                                                     ->
                                                     let uu____7893 =
                                                       let uu____7896 =
                                                         let uu____7897 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____7897 in
                                                       let uu____7899 =
                                                         let uu____7900 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____7900 in
                                                       (uu____7896,
                                                         uu____7899) in
                                                     (match uu____7893 with
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
                                            | uu____7919 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___123_7958 = env.effects in
              { decls = (uu___123_7958.decls); order = order2; joins } in
            let uu___124_7959 = env in
            {
              solver = (uu___124_7959.solver);
              range = (uu___124_7959.range);
              curmodule = (uu___124_7959.curmodule);
              gamma = (uu___124_7959.gamma);
              gamma_cache = (uu___124_7959.gamma_cache);
              modules = (uu___124_7959.modules);
              expected_typ = (uu___124_7959.expected_typ);
              sigtab = (uu___124_7959.sigtab);
              is_pattern = (uu___124_7959.is_pattern);
              instantiate_imp = (uu___124_7959.instantiate_imp);
              effects;
              generalize = (uu___124_7959.generalize);
              letrecs = (uu___124_7959.letrecs);
              top_level = (uu___124_7959.top_level);
              check_uvars = (uu___124_7959.check_uvars);
              use_eq = (uu___124_7959.use_eq);
              is_iface = (uu___124_7959.is_iface);
              admit = (uu___124_7959.admit);
              lax = (uu___124_7959.lax);
              lax_universes = (uu___124_7959.lax_universes);
              type_of = (uu___124_7959.type_of);
              universe_of = (uu___124_7959.universe_of);
              use_bv_sorts = (uu___124_7959.use_bv_sorts);
              qname_and_index = (uu___124_7959.qname_and_index);
              proof_ns = (uu___124_7959.proof_ns);
              synth = (uu___124_7959.synth);
              is_native_tactic = (uu___124_7959.is_native_tactic)
            }))
      | uu____7960 -> env
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
        | uu____7980 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____7990 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____7990 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____8000 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____8000 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____8021 =
                     let uu____8022 =
                       let uu____8025 =
                         let uu____8026 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____8035 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____8045 =
                           let uu____8046 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____8046 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____8026 uu____8035 uu____8045 in
                       (uu____8025, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____8022 in
                   raise uu____8021)
                else ();
                (let inst1 =
                   let uu____8050 =
                     let uu____8055 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____8055 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____8067  ->
                        fun uu____8068  ->
                          match (uu____8067, uu____8068) with
                          | ((x,uu____8080),(t,uu____8082)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____8050 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____8093 =
                     let uu___125_8094 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___125_8094.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___125_8094.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___125_8094.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___125_8094.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____8093
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
          let uu____8115 =
            let uu____8120 =
              norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
            effect_decl_opt env uu____8120 in
          match uu____8115 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____8134 =
                only_reifiable &&
                  (let uu____8136 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____8136) in
              if uu____8134
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____8145 ->
                     let c1 = unfold_effect_abbrev env c in
                     let uu____8147 =
                       let uu____8154 =
                         FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
                       ((c1.FStar_Syntax_Syntax.result_typ), uu____8154) in
                     (match uu____8147 with
                      | (res_typ,wp) ->
                          let repr =
                            inst_effect_fun_with [u_c] env ed
                              ([], (ed.FStar_Syntax_Syntax.repr)) in
                          let uu____8179 =
                            let uu____8181 = get_range env in
                            let uu____8182 =
                              let uu____8184 =
                                let uu____8185 =
                                  let uu____8193 =
                                    let uu____8195 =
                                      FStar_Syntax_Syntax.as_arg res_typ in
                                    [uu____8195; wp] in
                                  (repr, uu____8193) in
                                FStar_Syntax_Syntax.Tm_app uu____8185 in
                              FStar_Syntax_Syntax.mk uu____8184 in
                            uu____8182 FStar_Pervasives_Native.None
                              uu____8181 in
                          FStar_Pervasives_Native.Some uu____8179))
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
          let uu____8240 =
            let uu____8241 =
              let uu____8244 =
                let uu____8245 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____8245 in
              let uu____8246 = get_range env in (uu____8244, uu____8246) in
            FStar_Errors.Error uu____8241 in
          raise uu____8240 in
        let uu____8247 = effect_repr_aux true env c u_c in
        match uu____8247 with
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
      | uu____8281 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____8290 =
        let uu____8291 = FStar_Syntax_Subst.compress t in
        uu____8291.FStar_Syntax_Syntax.n in
      match uu____8290 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____8293,c) ->
          is_reifiable_comp env c
      | uu____8303 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____8323)::uu____8324 -> x :: rest
        | (Binding_sig_inst uu____8329)::uu____8330 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____8339 = push1 x rest1 in local :: uu____8339 in
      let uu___126_8341 = env in
      let uu____8342 = push1 s env.gamma in
      {
        solver = (uu___126_8341.solver);
        range = (uu___126_8341.range);
        curmodule = (uu___126_8341.curmodule);
        gamma = uu____8342;
        gamma_cache = (uu___126_8341.gamma_cache);
        modules = (uu___126_8341.modules);
        expected_typ = (uu___126_8341.expected_typ);
        sigtab = (uu___126_8341.sigtab);
        is_pattern = (uu___126_8341.is_pattern);
        instantiate_imp = (uu___126_8341.instantiate_imp);
        effects = (uu___126_8341.effects);
        generalize = (uu___126_8341.generalize);
        letrecs = (uu___126_8341.letrecs);
        top_level = (uu___126_8341.top_level);
        check_uvars = (uu___126_8341.check_uvars);
        use_eq = (uu___126_8341.use_eq);
        is_iface = (uu___126_8341.is_iface);
        admit = (uu___126_8341.admit);
        lax = (uu___126_8341.lax);
        lax_universes = (uu___126_8341.lax_universes);
        type_of = (uu___126_8341.type_of);
        universe_of = (uu___126_8341.universe_of);
        use_bv_sorts = (uu___126_8341.use_bv_sorts);
        qname_and_index = (uu___126_8341.qname_and_index);
        proof_ns = (uu___126_8341.proof_ns);
        synth = (uu___126_8341.synth);
        is_native_tactic = (uu___126_8341.is_native_tactic)
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
      let uu___127_8376 = env in
      {
        solver = (uu___127_8376.solver);
        range = (uu___127_8376.range);
        curmodule = (uu___127_8376.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___127_8376.gamma_cache);
        modules = (uu___127_8376.modules);
        expected_typ = (uu___127_8376.expected_typ);
        sigtab = (uu___127_8376.sigtab);
        is_pattern = (uu___127_8376.is_pattern);
        instantiate_imp = (uu___127_8376.instantiate_imp);
        effects = (uu___127_8376.effects);
        generalize = (uu___127_8376.generalize);
        letrecs = (uu___127_8376.letrecs);
        top_level = (uu___127_8376.top_level);
        check_uvars = (uu___127_8376.check_uvars);
        use_eq = (uu___127_8376.use_eq);
        is_iface = (uu___127_8376.is_iface);
        admit = (uu___127_8376.admit);
        lax = (uu___127_8376.lax);
        lax_universes = (uu___127_8376.lax_universes);
        type_of = (uu___127_8376.type_of);
        universe_of = (uu___127_8376.universe_of);
        use_bv_sorts = (uu___127_8376.use_bv_sorts);
        qname_and_index = (uu___127_8376.qname_and_index);
        proof_ns = (uu___127_8376.proof_ns);
        synth = (uu___127_8376.synth);
        is_native_tactic = (uu___127_8376.is_native_tactic)
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
            (let uu___128_8401 = env in
             {
               solver = (uu___128_8401.solver);
               range = (uu___128_8401.range);
               curmodule = (uu___128_8401.curmodule);
               gamma = rest;
               gamma_cache = (uu___128_8401.gamma_cache);
               modules = (uu___128_8401.modules);
               expected_typ = (uu___128_8401.expected_typ);
               sigtab = (uu___128_8401.sigtab);
               is_pattern = (uu___128_8401.is_pattern);
               instantiate_imp = (uu___128_8401.instantiate_imp);
               effects = (uu___128_8401.effects);
               generalize = (uu___128_8401.generalize);
               letrecs = (uu___128_8401.letrecs);
               top_level = (uu___128_8401.top_level);
               check_uvars = (uu___128_8401.check_uvars);
               use_eq = (uu___128_8401.use_eq);
               is_iface = (uu___128_8401.is_iface);
               admit = (uu___128_8401.admit);
               lax = (uu___128_8401.lax);
               lax_universes = (uu___128_8401.lax_universes);
               type_of = (uu___128_8401.type_of);
               universe_of = (uu___128_8401.universe_of);
               use_bv_sorts = (uu___128_8401.use_bv_sorts);
               qname_and_index = (uu___128_8401.qname_and_index);
               proof_ns = (uu___128_8401.proof_ns);
               synth = (uu___128_8401.synth);
               is_native_tactic = (uu___128_8401.is_native_tactic)
             }))
    | uu____8402 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____8421  ->
             match uu____8421 with | (x,uu____8425) -> push_bv env1 x) env bs
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
            let uu___129_8446 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___129_8446.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___129_8446.FStar_Syntax_Syntax.index);
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
      (let uu___130_8475 = env in
       {
         solver = (uu___130_8475.solver);
         range = (uu___130_8475.range);
         curmodule = (uu___130_8475.curmodule);
         gamma = [];
         gamma_cache = (uu___130_8475.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___130_8475.sigtab);
         is_pattern = (uu___130_8475.is_pattern);
         instantiate_imp = (uu___130_8475.instantiate_imp);
         effects = (uu___130_8475.effects);
         generalize = (uu___130_8475.generalize);
         letrecs = (uu___130_8475.letrecs);
         top_level = (uu___130_8475.top_level);
         check_uvars = (uu___130_8475.check_uvars);
         use_eq = (uu___130_8475.use_eq);
         is_iface = (uu___130_8475.is_iface);
         admit = (uu___130_8475.admit);
         lax = (uu___130_8475.lax);
         lax_universes = (uu___130_8475.lax_universes);
         type_of = (uu___130_8475.type_of);
         universe_of = (uu___130_8475.universe_of);
         use_bv_sorts = (uu___130_8475.use_bv_sorts);
         qname_and_index = (uu___130_8475.qname_and_index);
         proof_ns = (uu___130_8475.proof_ns);
         synth = (uu___130_8475.synth);
         is_native_tactic = (uu___130_8475.is_native_tactic)
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
        let uu____8506 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____8506 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____8522 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____8522)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___131_8534 = env in
      {
        solver = (uu___131_8534.solver);
        range = (uu___131_8534.range);
        curmodule = (uu___131_8534.curmodule);
        gamma = (uu___131_8534.gamma);
        gamma_cache = (uu___131_8534.gamma_cache);
        modules = (uu___131_8534.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___131_8534.sigtab);
        is_pattern = (uu___131_8534.is_pattern);
        instantiate_imp = (uu___131_8534.instantiate_imp);
        effects = (uu___131_8534.effects);
        generalize = (uu___131_8534.generalize);
        letrecs = (uu___131_8534.letrecs);
        top_level = (uu___131_8534.top_level);
        check_uvars = (uu___131_8534.check_uvars);
        use_eq = false;
        is_iface = (uu___131_8534.is_iface);
        admit = (uu___131_8534.admit);
        lax = (uu___131_8534.lax);
        lax_universes = (uu___131_8534.lax_universes);
        type_of = (uu___131_8534.type_of);
        universe_of = (uu___131_8534.universe_of);
        use_bv_sorts = (uu___131_8534.use_bv_sorts);
        qname_and_index = (uu___131_8534.qname_and_index);
        proof_ns = (uu___131_8534.proof_ns);
        synth = (uu___131_8534.synth);
        is_native_tactic = (uu___131_8534.is_native_tactic)
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
    let uu____8552 = expected_typ env_ in
    ((let uu___132_8556 = env_ in
      {
        solver = (uu___132_8556.solver);
        range = (uu___132_8556.range);
        curmodule = (uu___132_8556.curmodule);
        gamma = (uu___132_8556.gamma);
        gamma_cache = (uu___132_8556.gamma_cache);
        modules = (uu___132_8556.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___132_8556.sigtab);
        is_pattern = (uu___132_8556.is_pattern);
        instantiate_imp = (uu___132_8556.instantiate_imp);
        effects = (uu___132_8556.effects);
        generalize = (uu___132_8556.generalize);
        letrecs = (uu___132_8556.letrecs);
        top_level = (uu___132_8556.top_level);
        check_uvars = (uu___132_8556.check_uvars);
        use_eq = false;
        is_iface = (uu___132_8556.is_iface);
        admit = (uu___132_8556.admit);
        lax = (uu___132_8556.lax);
        lax_universes = (uu___132_8556.lax_universes);
        type_of = (uu___132_8556.type_of);
        universe_of = (uu___132_8556.universe_of);
        use_bv_sorts = (uu___132_8556.use_bv_sorts);
        qname_and_index = (uu___132_8556.qname_and_index);
        proof_ns = (uu___132_8556.proof_ns);
        synth = (uu___132_8556.synth);
        is_native_tactic = (uu___132_8556.is_native_tactic)
      }), uu____8552)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____8569 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___111_8576  ->
                    match uu___111_8576 with
                    | Binding_sig (uu____8578,se) -> [se]
                    | uu____8582 -> [])) in
          FStar_All.pipe_right uu____8569 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___133_8587 = env in
       {
         solver = (uu___133_8587.solver);
         range = (uu___133_8587.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___133_8587.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___133_8587.expected_typ);
         sigtab = (uu___133_8587.sigtab);
         is_pattern = (uu___133_8587.is_pattern);
         instantiate_imp = (uu___133_8587.instantiate_imp);
         effects = (uu___133_8587.effects);
         generalize = (uu___133_8587.generalize);
         letrecs = (uu___133_8587.letrecs);
         top_level = (uu___133_8587.top_level);
         check_uvars = (uu___133_8587.check_uvars);
         use_eq = (uu___133_8587.use_eq);
         is_iface = (uu___133_8587.is_iface);
         admit = (uu___133_8587.admit);
         lax = (uu___133_8587.lax);
         lax_universes = (uu___133_8587.lax_universes);
         type_of = (uu___133_8587.type_of);
         universe_of = (uu___133_8587.universe_of);
         use_bv_sorts = (uu___133_8587.use_bv_sorts);
         qname_and_index = (uu___133_8587.qname_and_index);
         proof_ns = (uu___133_8587.proof_ns);
         synth = (uu___133_8587.synth);
         is_native_tactic = (uu___133_8587.is_native_tactic)
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
      | (Binding_univ uu____8638)::tl1 -> aux out tl1
      | (Binding_lid (uu____8641,(uu____8642,t)))::tl1 ->
          let uu____8651 =
            let uu____8655 = FStar_Syntax_Free.uvars t in ext out uu____8655 in
          aux uu____8651 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8659;
            FStar_Syntax_Syntax.index = uu____8660;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8665 =
            let uu____8669 = FStar_Syntax_Free.uvars t in ext out uu____8669 in
          aux uu____8665 tl1
      | (Binding_sig uu____8673)::uu____8674 -> out
      | (Binding_sig_inst uu____8679)::uu____8680 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8718)::tl1 -> aux out tl1
      | (Binding_univ uu____8725)::tl1 -> aux out tl1
      | (Binding_lid (uu____8728,(uu____8729,t)))::tl1 ->
          let uu____8738 =
            let uu____8740 = FStar_Syntax_Free.univs t in ext out uu____8740 in
          aux uu____8738 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8742;
            FStar_Syntax_Syntax.index = uu____8743;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8748 =
            let uu____8750 = FStar_Syntax_Free.univs t in ext out uu____8750 in
          aux uu____8748 tl1
      | (Binding_sig uu____8752)::uu____8753 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____8791)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____8801 = FStar_Util.set_add uname out in aux uu____8801 tl1
      | (Binding_lid (uu____8803,(uu____8804,t)))::tl1 ->
          let uu____8813 =
            let uu____8815 = FStar_Syntax_Free.univnames t in
            ext out uu____8815 in
          aux uu____8813 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____8817;
            FStar_Syntax_Syntax.index = uu____8818;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____8823 =
            let uu____8825 = FStar_Syntax_Free.univnames t in
            ext out uu____8825 in
          aux uu____8823 tl1
      | (Binding_sig uu____8827)::uu____8828 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___112_8847  ->
            match uu___112_8847 with
            | Binding_var x -> [x]
            | Binding_lid uu____8850 -> []
            | Binding_sig uu____8853 -> []
            | Binding_univ uu____8857 -> []
            | Binding_sig_inst uu____8858 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____8869 =
      let uu____8871 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____8871
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____8869 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____8890 =
      let uu____8891 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___113_8898  ->
                match uu___113_8898 with
                | Binding_var x ->
                    let uu____8900 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____8900
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____8903) ->
                    let uu____8904 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____8904
                | Binding_sig (ls,uu____8906) ->
                    let uu____8909 =
                      let uu____8910 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8910
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____8909
                | Binding_sig_inst (ls,uu____8916,uu____8917) ->
                    let uu____8920 =
                      let uu____8921 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____8921
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____8920)) in
      FStar_All.pipe_right uu____8891 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____8890 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____8935 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____8935
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____8962  ->
                 fun uu____8963  ->
                   match (uu____8962, uu____8963) with
                   | ((b1,uu____8973),(b2,uu____8975)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___114_9029  ->
             match uu___114_9029 with
             | Binding_sig (lids,uu____9033) -> FStar_List.append lids keys
             | uu____9036 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____9041  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____9068) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____9080,uu____9081) -> false in
      let rec should_enc_path' pns path1 =
        match pns with
        | [] -> true
        | (p,b)::pns1 ->
            let uu____9105 = list_prefix p path1 in
            if uu____9105 then b else should_enc_path' pns1 path1 in
      should_enc_path' (FStar_List.flatten env.proof_ns) path
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____9117 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____9117
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        match e.proof_ns with
        | [] -> failwith "empty proof_ns stack!"
        | pns::rest ->
            let pns' = (path, b) :: pns in
            let uu___134_9140 = e in
            {
              solver = (uu___134_9140.solver);
              range = (uu___134_9140.range);
              curmodule = (uu___134_9140.curmodule);
              gamma = (uu___134_9140.gamma);
              gamma_cache = (uu___134_9140.gamma_cache);
              modules = (uu___134_9140.modules);
              expected_typ = (uu___134_9140.expected_typ);
              sigtab = (uu___134_9140.sigtab);
              is_pattern = (uu___134_9140.is_pattern);
              instantiate_imp = (uu___134_9140.instantiate_imp);
              effects = (uu___134_9140.effects);
              generalize = (uu___134_9140.generalize);
              letrecs = (uu___134_9140.letrecs);
              top_level = (uu___134_9140.top_level);
              check_uvars = (uu___134_9140.check_uvars);
              use_eq = (uu___134_9140.use_eq);
              is_iface = (uu___134_9140.is_iface);
              admit = (uu___134_9140.admit);
              lax = (uu___134_9140.lax);
              lax_universes = (uu___134_9140.lax_universes);
              type_of = (uu___134_9140.type_of);
              universe_of = (uu___134_9140.universe_of);
              use_bv_sorts = (uu___134_9140.use_bv_sorts);
              qname_and_index = (uu___134_9140.qname_and_index);
              proof_ns = (pns' :: rest);
              synth = (uu___134_9140.synth);
              is_native_tactic = (uu___134_9140.is_native_tactic)
            }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let push_proof_ns: env -> env =
  fun e  ->
    let uu___135_9164 = e in
    {
      solver = (uu___135_9164.solver);
      range = (uu___135_9164.range);
      curmodule = (uu___135_9164.curmodule);
      gamma = (uu___135_9164.gamma);
      gamma_cache = (uu___135_9164.gamma_cache);
      modules = (uu___135_9164.modules);
      expected_typ = (uu___135_9164.expected_typ);
      sigtab = (uu___135_9164.sigtab);
      is_pattern = (uu___135_9164.is_pattern);
      instantiate_imp = (uu___135_9164.instantiate_imp);
      effects = (uu___135_9164.effects);
      generalize = (uu___135_9164.generalize);
      letrecs = (uu___135_9164.letrecs);
      top_level = (uu___135_9164.top_level);
      check_uvars = (uu___135_9164.check_uvars);
      use_eq = (uu___135_9164.use_eq);
      is_iface = (uu___135_9164.is_iface);
      admit = (uu___135_9164.admit);
      lax = (uu___135_9164.lax);
      lax_universes = (uu___135_9164.lax_universes);
      type_of = (uu___135_9164.type_of);
      universe_of = (uu___135_9164.universe_of);
      use_bv_sorts = (uu___135_9164.use_bv_sorts);
      qname_and_index = (uu___135_9164.qname_and_index);
      proof_ns = ([] :: (e.proof_ns));
      synth = (uu___135_9164.synth);
      is_native_tactic = (uu___135_9164.is_native_tactic)
    }
let pop_proof_ns: env -> env =
  fun e  ->
    match e.proof_ns with
    | [] -> failwith "empty proof_ns stack!"
    | uu____9174::rest ->
        let uu___136_9177 = e in
        {
          solver = (uu___136_9177.solver);
          range = (uu___136_9177.range);
          curmodule = (uu___136_9177.curmodule);
          gamma = (uu___136_9177.gamma);
          gamma_cache = (uu___136_9177.gamma_cache);
          modules = (uu___136_9177.modules);
          expected_typ = (uu___136_9177.expected_typ);
          sigtab = (uu___136_9177.sigtab);
          is_pattern = (uu___136_9177.is_pattern);
          instantiate_imp = (uu___136_9177.instantiate_imp);
          effects = (uu___136_9177.effects);
          generalize = (uu___136_9177.generalize);
          letrecs = (uu___136_9177.letrecs);
          top_level = (uu___136_9177.top_level);
          check_uvars = (uu___136_9177.check_uvars);
          use_eq = (uu___136_9177.use_eq);
          is_iface = (uu___136_9177.is_iface);
          admit = (uu___136_9177.admit);
          lax = (uu___136_9177.lax);
          lax_universes = (uu___136_9177.lax_universes);
          type_of = (uu___136_9177.type_of);
          universe_of = (uu___136_9177.universe_of);
          use_bv_sorts = (uu___136_9177.use_bv_sorts);
          qname_and_index = (uu___136_9177.qname_and_index);
          proof_ns = rest;
          synth = (uu___136_9177.synth);
          is_native_tactic = (uu___136_9177.is_native_tactic)
        }
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___137_9190 = e in
      {
        solver = (uu___137_9190.solver);
        range = (uu___137_9190.range);
        curmodule = (uu___137_9190.curmodule);
        gamma = (uu___137_9190.gamma);
        gamma_cache = (uu___137_9190.gamma_cache);
        modules = (uu___137_9190.modules);
        expected_typ = (uu___137_9190.expected_typ);
        sigtab = (uu___137_9190.sigtab);
        is_pattern = (uu___137_9190.is_pattern);
        instantiate_imp = (uu___137_9190.instantiate_imp);
        effects = (uu___137_9190.effects);
        generalize = (uu___137_9190.generalize);
        letrecs = (uu___137_9190.letrecs);
        top_level = (uu___137_9190.top_level);
        check_uvars = (uu___137_9190.check_uvars);
        use_eq = (uu___137_9190.use_eq);
        is_iface = (uu___137_9190.is_iface);
        admit = (uu___137_9190.admit);
        lax = (uu___137_9190.lax);
        lax_universes = (uu___137_9190.lax_universes);
        type_of = (uu___137_9190.type_of);
        universe_of = (uu___137_9190.universe_of);
        use_bv_sorts = (uu___137_9190.use_bv_sorts);
        qname_and_index = (uu___137_9190.qname_and_index);
        proof_ns = ns;
        synth = (uu___137_9190.synth);
        is_native_tactic = (uu___137_9190.is_native_tactic)
      }
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let string_of_proof_ns' pns =
      let uu____9209 =
        FStar_List.map
          (fun fpns  ->
             let uu____9222 =
               let uu____9223 =
                 let uu____9224 =
                   FStar_List.map
                     (fun uu____9232  ->
                        match uu____9232 with
                        | (p,b) ->
                            Prims.strcat (if b then "+" else "-")
                              (FStar_String.concat "." p)) fpns in
                 FStar_String.concat "," uu____9224 in
               Prims.strcat uu____9223 "]" in
             Prims.strcat "[" uu____9222) pns in
      FStar_String.concat ";" uu____9209 in
    string_of_proof_ns' env.proof_ns
let dummy_solver: solver_t =
  {
    init = (fun uu____9243  -> ());
    push = (fun uu____9245  -> ());
    pop = (fun uu____9247  -> ());
    mark = (fun uu____9249  -> ());
    reset_mark = (fun uu____9251  -> ());
    commit_mark = (fun uu____9253  -> ());
    encode_modul = (fun uu____9256  -> fun uu____9257  -> ());
    encode_sig = (fun uu____9260  -> fun uu____9261  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____9267 =
             let uu____9271 = FStar_Options.peek () in (e, g, uu____9271) in
           [uu____9267]);
    solve = (fun uu____9281  -> fun uu____9282  -> fun uu____9283  -> ());
    is_trivial = (fun uu____9289  -> fun uu____9290  -> false);
    finish = (fun uu____9292  -> ());
    refresh = (fun uu____9294  -> ())
  }