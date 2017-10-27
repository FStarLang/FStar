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
    match projectee with | Binding_var _0 -> true | uu____43 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____59 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____89 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____119 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____139 -> false
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
    match projectee with | NoDelta  -> true | uu____178 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____182 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____186 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____191 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
let uu___is_UnfoldTac: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____202 -> false
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
type proof_namespace =
  (name_prefix,Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list[@@deriving
                                                                    show]
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
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref;
  tc_hooks: tcenv_hooks;
  dsenv: FStar_ToSyntax_Env.env;}[@@deriving show]
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
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> Prims.unit;}[@@deriving show]
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__solver
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__range
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__curmodule
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__gamma
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__modules
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__sigtab
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__effects
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__letrecs
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__top_level
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__use_eq
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__is_iface
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__admit
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__lax
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__failhard
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__nosynth
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__tc_term
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__type_of
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        failhard = __fname__failhard; nosynth = __fname__nosynth;
        tc_term = __fname__tc_term; type_of = __fname__type_of;
        universe_of = __fname__universe_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qname_and_index = __fname__qname_and_index;
        proof_ns = __fname__proof_ns; synth = __fname__synth;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__proof_ns
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__synth
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__identifier_info
let __proj__Mkenv__item__tc_hooks: env -> tcenv_hooks =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__tc_hooks
let __proj__Mkenv__item__dsenv: env -> FStar_ToSyntax_Env.env =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;_} ->
        __fname__dsenv
let __proj__Mksolver_t__item__init: solver_t -> env -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
let __proj__Mksolver_t__item__push: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
let __proj__Mksolver_t__item__pop: solver_t -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
let __proj__Mksolver_t__item__encode_modul:
  solver_t -> env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
let __proj__Mksolver_t__item__encode_sig:
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
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
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
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
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
let __proj__Mksolver_t__item__finish: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
let __proj__Mksolver_t__item__refresh: solver_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
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
let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook:
  tcenv_hooks -> env -> binding -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
let rename_gamma:
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___248_4831  ->
              match uu___248_4831 with
              | Binding_var x ->
                  let y =
                    let uu____4834 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____4834 in
                  let uu____4835 =
                    let uu____4836 = FStar_Syntax_Subst.compress y in
                    uu____4836.FStar_Syntax_Syntax.n in
                  (match uu____4835 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____4840 =
                         let uu___262_4841 = y1 in
                         let uu____4842 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___262_4841.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___262_4841.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____4842
                         } in
                       Binding_var uu____4840
                   | uu____4845 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___263_4853 = env in
      let uu____4854 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___263_4853.solver);
        range = (uu___263_4853.range);
        curmodule = (uu___263_4853.curmodule);
        gamma = uu____4854;
        gamma_cache = (uu___263_4853.gamma_cache);
        modules = (uu___263_4853.modules);
        expected_typ = (uu___263_4853.expected_typ);
        sigtab = (uu___263_4853.sigtab);
        is_pattern = (uu___263_4853.is_pattern);
        instantiate_imp = (uu___263_4853.instantiate_imp);
        effects = (uu___263_4853.effects);
        generalize = (uu___263_4853.generalize);
        letrecs = (uu___263_4853.letrecs);
        top_level = (uu___263_4853.top_level);
        check_uvars = (uu___263_4853.check_uvars);
        use_eq = (uu___263_4853.use_eq);
        is_iface = (uu___263_4853.is_iface);
        admit = (uu___263_4853.admit);
        lax = (uu___263_4853.lax);
        lax_universes = (uu___263_4853.lax_universes);
        failhard = (uu___263_4853.failhard);
        nosynth = (uu___263_4853.nosynth);
        tc_term = (uu___263_4853.tc_term);
        type_of = (uu___263_4853.type_of);
        universe_of = (uu___263_4853.universe_of);
        use_bv_sorts = (uu___263_4853.use_bv_sorts);
        qname_and_index = (uu___263_4853.qname_and_index);
        proof_ns = (uu___263_4853.proof_ns);
        synth = (uu___263_4853.synth);
        is_native_tactic = (uu___263_4853.is_native_tactic);
        identifier_info = (uu___263_4853.identifier_info);
        tc_hooks = (uu___263_4853.tc_hooks);
        dsenv = (uu___263_4853.dsenv)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____4861  -> fun uu____4862  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___264_4872 = env in
      {
        solver = (uu___264_4872.solver);
        range = (uu___264_4872.range);
        curmodule = (uu___264_4872.curmodule);
        gamma = (uu___264_4872.gamma);
        gamma_cache = (uu___264_4872.gamma_cache);
        modules = (uu___264_4872.modules);
        expected_typ = (uu___264_4872.expected_typ);
        sigtab = (uu___264_4872.sigtab);
        is_pattern = (uu___264_4872.is_pattern);
        instantiate_imp = (uu___264_4872.instantiate_imp);
        effects = (uu___264_4872.effects);
        generalize = (uu___264_4872.generalize);
        letrecs = (uu___264_4872.letrecs);
        top_level = (uu___264_4872.top_level);
        check_uvars = (uu___264_4872.check_uvars);
        use_eq = (uu___264_4872.use_eq);
        is_iface = (uu___264_4872.is_iface);
        admit = (uu___264_4872.admit);
        lax = (uu___264_4872.lax);
        lax_universes = (uu___264_4872.lax_universes);
        failhard = (uu___264_4872.failhard);
        nosynth = (uu___264_4872.nosynth);
        tc_term = (uu___264_4872.tc_term);
        type_of = (uu___264_4872.type_of);
        universe_of = (uu___264_4872.universe_of);
        use_bv_sorts = (uu___264_4872.use_bv_sorts);
        qname_and_index = (uu___264_4872.qname_and_index);
        proof_ns = (uu___264_4872.proof_ns);
        synth = (uu___264_4872.synth);
        is_native_tactic = (uu___264_4872.is_native_tactic);
        identifier_info = (uu___264_4872.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___264_4872.dsenv)
      }
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
      | (NoDelta ,uu____4884) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____4885,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____4886,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____4887 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____4894 . Prims.unit -> 'Auu____4894 FStar_Util.smap =
  fun uu____4900  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____4903 . Prims.unit -> 'Auu____4903 FStar_Util.smap =
  fun uu____4909  -> FStar_Util.smap_create (Prims.parse_int "100")
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
            let uu____4979 = new_gamma_cache () in
            let uu____4982 = new_sigtab () in
            let uu____4985 = FStar_Options.using_facts_from () in
            let uu____4986 =
              FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty in
            let uu____4989 = FStar_ToSyntax_Env.empty_env () in
            {
              solver;
              range = FStar_Range.dummyRange;
              curmodule = module_lid;
              gamma = [];
              gamma_cache = uu____4979;
              modules = [];
              expected_typ = FStar_Pervasives_Native.None;
              sigtab = uu____4982;
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
              proof_ns = uu____4985;
              synth =
                (fun e  ->
                   fun g  -> fun tau  -> failwith "no synthesizer available");
              is_native_tactic = (fun uu____5021  -> false);
              identifier_info = uu____4986;
              tc_hooks = default_tc_hooks;
              dsenv = uu____4989
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
  fun uu____5089  ->
    let uu____5090 = FStar_ST.op_Bang query_indices in
    match uu____5090 with
    | [] -> failwith "Empty query indices!"
    | uu____5167 ->
        let uu____5176 =
          let uu____5185 =
            let uu____5192 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5192 in
          let uu____5269 = FStar_ST.op_Bang query_indices in uu____5185 ::
            uu____5269 in
        FStar_ST.op_Colon_Equals query_indices uu____5176
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5410  ->
    let uu____5411 = FStar_ST.op_Bang query_indices in
    match uu____5411 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5578  ->
    match uu____5578 with
    | (l,n1) ->
        let uu____5585 = FStar_ST.op_Bang query_indices in
        (match uu____5585 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5750 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____5767  ->
    let uu____5768 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____5768
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____5862 =
       let uu____5865 = FStar_ST.op_Bang stack in env :: uu____5865 in
     FStar_ST.op_Colon_Equals stack uu____5862);
    (let uu___265_5968 = env in
     let uu____5969 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____5972 = FStar_Util.smap_copy (sigtab env) in
     let uu____5975 =
       let uu____5978 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____5978 in
     {
       solver = (uu___265_5968.solver);
       range = (uu___265_5968.range);
       curmodule = (uu___265_5968.curmodule);
       gamma = (uu___265_5968.gamma);
       gamma_cache = uu____5969;
       modules = (uu___265_5968.modules);
       expected_typ = (uu___265_5968.expected_typ);
       sigtab = uu____5972;
       is_pattern = (uu___265_5968.is_pattern);
       instantiate_imp = (uu___265_5968.instantiate_imp);
       effects = (uu___265_5968.effects);
       generalize = (uu___265_5968.generalize);
       letrecs = (uu___265_5968.letrecs);
       top_level = (uu___265_5968.top_level);
       check_uvars = (uu___265_5968.check_uvars);
       use_eq = (uu___265_5968.use_eq);
       is_iface = (uu___265_5968.is_iface);
       admit = (uu___265_5968.admit);
       lax = (uu___265_5968.lax);
       lax_universes = (uu___265_5968.lax_universes);
       failhard = (uu___265_5968.failhard);
       nosynth = (uu___265_5968.nosynth);
       tc_term = (uu___265_5968.tc_term);
       type_of = (uu___265_5968.type_of);
       universe_of = (uu___265_5968.universe_of);
       use_bv_sorts = (uu___265_5968.use_bv_sorts);
       qname_and_index = (uu___265_5968.qname_and_index);
       proof_ns = (uu___265_5968.proof_ns);
       synth = (uu___265_5968.synth);
       is_native_tactic = (uu___265_5968.is_native_tactic);
       identifier_info = uu____5975;
       tc_hooks = (uu___265_5968.tc_hooks);
       dsenv = (uu___265_5968.dsenv)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6041  ->
    let uu____6042 = FStar_ST.op_Bang stack in
    match uu____6042 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6150 -> failwith "Impossible: Too many pops"
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
        let uu____6189 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6215  ->
                  match uu____6215 with
                  | (m,uu____6221) -> FStar_Ident.lid_equals l m)) in
        (match uu____6189 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___266_6228 = env in
               {
                 solver = (uu___266_6228.solver);
                 range = (uu___266_6228.range);
                 curmodule = (uu___266_6228.curmodule);
                 gamma = (uu___266_6228.gamma);
                 gamma_cache = (uu___266_6228.gamma_cache);
                 modules = (uu___266_6228.modules);
                 expected_typ = (uu___266_6228.expected_typ);
                 sigtab = (uu___266_6228.sigtab);
                 is_pattern = (uu___266_6228.is_pattern);
                 instantiate_imp = (uu___266_6228.instantiate_imp);
                 effects = (uu___266_6228.effects);
                 generalize = (uu___266_6228.generalize);
                 letrecs = (uu___266_6228.letrecs);
                 top_level = (uu___266_6228.top_level);
                 check_uvars = (uu___266_6228.check_uvars);
                 use_eq = (uu___266_6228.use_eq);
                 is_iface = (uu___266_6228.is_iface);
                 admit = (uu___266_6228.admit);
                 lax = (uu___266_6228.lax);
                 lax_universes = (uu___266_6228.lax_universes);
                 failhard = (uu___266_6228.failhard);
                 nosynth = (uu___266_6228.nosynth);
                 tc_term = (uu___266_6228.tc_term);
                 type_of = (uu___266_6228.type_of);
                 universe_of = (uu___266_6228.universe_of);
                 use_bv_sorts = (uu___266_6228.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___266_6228.proof_ns);
                 synth = (uu___266_6228.synth);
                 is_native_tactic = (uu___266_6228.is_native_tactic);
                 identifier_info = (uu___266_6228.identifier_info);
                 tc_hooks = (uu___266_6228.tc_hooks);
                 dsenv = (uu___266_6228.dsenv)
               }))
         | FStar_Pervasives_Native.Some (uu____6233,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___267_6241 = env in
               {
                 solver = (uu___267_6241.solver);
                 range = (uu___267_6241.range);
                 curmodule = (uu___267_6241.curmodule);
                 gamma = (uu___267_6241.gamma);
                 gamma_cache = (uu___267_6241.gamma_cache);
                 modules = (uu___267_6241.modules);
                 expected_typ = (uu___267_6241.expected_typ);
                 sigtab = (uu___267_6241.sigtab);
                 is_pattern = (uu___267_6241.is_pattern);
                 instantiate_imp = (uu___267_6241.instantiate_imp);
                 effects = (uu___267_6241.effects);
                 generalize = (uu___267_6241.generalize);
                 letrecs = (uu___267_6241.letrecs);
                 top_level = (uu___267_6241.top_level);
                 check_uvars = (uu___267_6241.check_uvars);
                 use_eq = (uu___267_6241.use_eq);
                 is_iface = (uu___267_6241.is_iface);
                 admit = (uu___267_6241.admit);
                 lax = (uu___267_6241.lax);
                 lax_universes = (uu___267_6241.lax_universes);
                 failhard = (uu___267_6241.failhard);
                 nosynth = (uu___267_6241.nosynth);
                 tc_term = (uu___267_6241.tc_term);
                 type_of = (uu___267_6241.type_of);
                 universe_of = (uu___267_6241.universe_of);
                 use_bv_sorts = (uu___267_6241.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___267_6241.proof_ns);
                 synth = (uu___267_6241.synth);
                 is_native_tactic = (uu___267_6241.is_native_tactic);
                 identifier_info = (uu___267_6241.identifier_info);
                 tc_hooks = (uu___267_6241.tc_hooks);
                 dsenv = (uu___267_6241.dsenv)
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
        (let uu___268_6259 = e in
         {
           solver = (uu___268_6259.solver);
           range = r;
           curmodule = (uu___268_6259.curmodule);
           gamma = (uu___268_6259.gamma);
           gamma_cache = (uu___268_6259.gamma_cache);
           modules = (uu___268_6259.modules);
           expected_typ = (uu___268_6259.expected_typ);
           sigtab = (uu___268_6259.sigtab);
           is_pattern = (uu___268_6259.is_pattern);
           instantiate_imp = (uu___268_6259.instantiate_imp);
           effects = (uu___268_6259.effects);
           generalize = (uu___268_6259.generalize);
           letrecs = (uu___268_6259.letrecs);
           top_level = (uu___268_6259.top_level);
           check_uvars = (uu___268_6259.check_uvars);
           use_eq = (uu___268_6259.use_eq);
           is_iface = (uu___268_6259.is_iface);
           admit = (uu___268_6259.admit);
           lax = (uu___268_6259.lax);
           lax_universes = (uu___268_6259.lax_universes);
           failhard = (uu___268_6259.failhard);
           nosynth = (uu___268_6259.nosynth);
           tc_term = (uu___268_6259.tc_term);
           type_of = (uu___268_6259.type_of);
           universe_of = (uu___268_6259.universe_of);
           use_bv_sorts = (uu___268_6259.use_bv_sorts);
           qname_and_index = (uu___268_6259.qname_and_index);
           proof_ns = (uu___268_6259.proof_ns);
           synth = (uu___268_6259.synth);
           is_native_tactic = (uu___268_6259.is_native_tactic);
           identifier_info = (uu___268_6259.identifier_info);
           tc_hooks = (uu___268_6259.tc_hooks);
           dsenv = (uu___268_6259.dsenv)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6269 =
        let uu____6270 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6270 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6269
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6372 =
          let uu____6373 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6373 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6372
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6475 =
          let uu____6476 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6476 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6475
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6580 =
        let uu____6581 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6581 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6580
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___269_6688 = env in
      {
        solver = (uu___269_6688.solver);
        range = (uu___269_6688.range);
        curmodule = lid;
        gamma = (uu___269_6688.gamma);
        gamma_cache = (uu___269_6688.gamma_cache);
        modules = (uu___269_6688.modules);
        expected_typ = (uu___269_6688.expected_typ);
        sigtab = (uu___269_6688.sigtab);
        is_pattern = (uu___269_6688.is_pattern);
        instantiate_imp = (uu___269_6688.instantiate_imp);
        effects = (uu___269_6688.effects);
        generalize = (uu___269_6688.generalize);
        letrecs = (uu___269_6688.letrecs);
        top_level = (uu___269_6688.top_level);
        check_uvars = (uu___269_6688.check_uvars);
        use_eq = (uu___269_6688.use_eq);
        is_iface = (uu___269_6688.is_iface);
        admit = (uu___269_6688.admit);
        lax = (uu___269_6688.lax);
        lax_universes = (uu___269_6688.lax_universes);
        failhard = (uu___269_6688.failhard);
        nosynth = (uu___269_6688.nosynth);
        tc_term = (uu___269_6688.tc_term);
        type_of = (uu___269_6688.type_of);
        universe_of = (uu___269_6688.universe_of);
        use_bv_sorts = (uu___269_6688.use_bv_sorts);
        qname_and_index = (uu___269_6688.qname_and_index);
        proof_ns = (uu___269_6688.proof_ns);
        synth = (uu___269_6688.synth);
        is_native_tactic = (uu___269_6688.is_native_tactic);
        identifier_info = (uu___269_6688.identifier_info);
        tc_hooks = (uu___269_6688.tc_hooks);
        dsenv = (uu___269_6688.dsenv)
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
    let uu____6713 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6713
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6716  ->
    let uu____6717 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6717
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
      | ((formals,t),uu____6755) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____6779 = FStar_Syntax_Subst.subst vs t in (us, uu____6779)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___249_6792  ->
    match uu___249_6792 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____6816  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____6829 = inst_tscheme t in
      match uu____6829 with
      | (us,t1) ->
          let uu____6840 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____6840)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____6852  ->
          match uu____6852 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____6867 =
                         let uu____6868 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____6869 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____6870 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____6871 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____6868 uu____6869 uu____6870 uu____6871 in
                       failwith uu____6867)
                    else ();
                    (let uu____6873 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____6873))
               | uu____6880 ->
                   let uu____6881 =
                     let uu____6882 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____6882 in
                   failwith uu____6881)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____6886 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____6890 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____6894 -> false
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
             | ([],uu____6928) -> Maybe
             | (uu____6935,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____6954 -> No in
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
          let uu____7059 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7059 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___250_7104  ->
                   match uu___250_7104 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7147 =
                           let uu____7166 =
                             let uu____7181 = inst_tscheme t in
                             FStar_Util.Inl uu____7181 in
                           (uu____7166, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7147
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7247,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7249);
                                     FStar_Syntax_Syntax.sigrng = uu____7250;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7251;
                                     FStar_Syntax_Syntax.sigmeta = uu____7252;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7253;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7273 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7273
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7319 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7326 -> cache t in
                       let uu____7327 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7327 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7402 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7402 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7488 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7568 = find_in_sigtab env lid in
         match uu____7568 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7667) ->
          add_sigelts env ses
      | uu____7676 ->
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
            | uu____7690 -> ()))
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
        (fun uu___251_7717  ->
           match uu___251_7717 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7735 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____7768,lb::[]),uu____7770) ->
          let uu____7783 =
            let uu____7792 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____7801 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____7792, uu____7801) in
          FStar_Pervasives_Native.Some uu____7783
      | FStar_Syntax_Syntax.Sig_let ((uu____7814,lbs),uu____7816) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____7852 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____7864 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____7864
                   then
                     let uu____7875 =
                       let uu____7884 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____7893 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____7884, uu____7893) in
                     FStar_Pervasives_Native.Some uu____7875
                   else FStar_Pervasives_Native.None)
      | uu____7915 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____7948 =
          let uu____7957 =
            let uu____7962 =
              let uu____7963 =
                let uu____7966 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____7966 in
              ((ne.FStar_Syntax_Syntax.univs), uu____7963) in
            inst_tscheme uu____7962 in
          (uu____7957, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7948
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____7986,uu____7987) ->
        let uu____7992 =
          let uu____8001 =
            let uu____8006 =
              let uu____8007 =
                let uu____8010 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8010 in
              (us, uu____8007) in
            inst_tscheme uu____8006 in
          (uu____8001, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____7992
    | uu____8027 -> FStar_Pervasives_Native.None
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
      let mapper uu____8085 =
        match uu____8085 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8181,uvs,t,uu____8184,uu____8185,uu____8186);
                    FStar_Syntax_Syntax.sigrng = uu____8187;
                    FStar_Syntax_Syntax.sigquals = uu____8188;
                    FStar_Syntax_Syntax.sigmeta = uu____8189;
                    FStar_Syntax_Syntax.sigattrs = uu____8190;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8211 =
                   let uu____8220 = inst_tscheme (uvs, t) in
                   (uu____8220, rng) in
                 FStar_Pervasives_Native.Some uu____8211
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8240;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8242;
                    FStar_Syntax_Syntax.sigattrs = uu____8243;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8260 =
                   let uu____8261 = in_cur_mod env l in uu____8261 = Yes in
                 if uu____8260
                 then
                   let uu____8272 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8272
                    then
                      let uu____8285 =
                        let uu____8294 = inst_tscheme (uvs, t) in
                        (uu____8294, rng) in
                      FStar_Pervasives_Native.Some uu____8285
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8321 =
                      let uu____8330 = inst_tscheme (uvs, t) in
                      (uu____8330, rng) in
                    FStar_Pervasives_Native.Some uu____8321)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8351,uu____8352);
                    FStar_Syntax_Syntax.sigrng = uu____8353;
                    FStar_Syntax_Syntax.sigquals = uu____8354;
                    FStar_Syntax_Syntax.sigmeta = uu____8355;
                    FStar_Syntax_Syntax.sigattrs = uu____8356;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8395 =
                        let uu____8404 = inst_tscheme (uvs, k) in
                        (uu____8404, rng) in
                      FStar_Pervasives_Native.Some uu____8395
                  | uu____8421 ->
                      let uu____8422 =
                        let uu____8431 =
                          let uu____8436 =
                            let uu____8437 =
                              let uu____8440 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8440 in
                            (uvs, uu____8437) in
                          inst_tscheme uu____8436 in
                        (uu____8431, rng) in
                      FStar_Pervasives_Native.Some uu____8422)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8461,uu____8462);
                    FStar_Syntax_Syntax.sigrng = uu____8463;
                    FStar_Syntax_Syntax.sigquals = uu____8464;
                    FStar_Syntax_Syntax.sigmeta = uu____8465;
                    FStar_Syntax_Syntax.sigattrs = uu____8466;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8506 =
                        let uu____8515 = inst_tscheme_with (uvs, k) us in
                        (uu____8515, rng) in
                      FStar_Pervasives_Native.Some uu____8506
                  | uu____8532 ->
                      let uu____8533 =
                        let uu____8542 =
                          let uu____8547 =
                            let uu____8548 =
                              let uu____8551 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8551 in
                            (uvs, uu____8548) in
                          inst_tscheme_with uu____8547 us in
                        (uu____8542, rng) in
                      FStar_Pervasives_Native.Some uu____8533)
             | FStar_Util.Inr se ->
                 let uu____8585 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8606;
                        FStar_Syntax_Syntax.sigrng = uu____8607;
                        FStar_Syntax_Syntax.sigquals = uu____8608;
                        FStar_Syntax_Syntax.sigmeta = uu____8609;
                        FStar_Syntax_Syntax.sigattrs = uu____8610;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8625 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8585
                   (FStar_Util.map_option
                      (fun uu____8673  ->
                         match uu____8673 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8704 =
        let uu____8715 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8715 mapper in
      match uu____8704 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___270_8808 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___270_8808.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___270_8808.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____8833 = lookup_qname env l in
      match uu____8833 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____8872 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____8920 = try_lookup_bv env bv in
      match uu____8920 with
      | FStar_Pervasives_Native.None  ->
          let uu____8935 =
            let uu____8936 =
              let uu____8941 = variable_not_found bv in (uu____8941, bvr) in
            FStar_Errors.Error uu____8936 in
          FStar_Exn.raise uu____8935
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____8952 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____8953 =
            let uu____8954 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____8954 in
          (uu____8952, uu____8953)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____8971 = try_lookup_lid_aux env l in
      match uu____8971 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9037 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9037 in
          let uu____9038 =
            let uu____9047 =
              let uu____9052 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9052) in
            (uu____9047, r1) in
          FStar_Pervasives_Native.Some uu____9038
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9079 = try_lookup_lid env l in
      match uu____9079 with
      | FStar_Pervasives_Native.None  ->
          let uu____9106 =
            let uu____9107 =
              let uu____9112 = name_not_found l in
              (uu____9112, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9107 in
          FStar_Exn.raise uu____9106
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___252_9148  ->
              match uu___252_9148 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9150 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9165 = lookup_qname env lid in
      match uu____9165 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9194,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9197;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9199;
              FStar_Syntax_Syntax.sigattrs = uu____9200;_},FStar_Pervasives_Native.None
            ),uu____9201)
          ->
          let uu____9250 =
            let uu____9261 =
              let uu____9266 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9266) in
            (uu____9261, q) in
          FStar_Pervasives_Native.Some uu____9250
      | uu____9283 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9320 = lookup_qname env lid in
      match uu____9320 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9345,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9348;
              FStar_Syntax_Syntax.sigquals = uu____9349;
              FStar_Syntax_Syntax.sigmeta = uu____9350;
              FStar_Syntax_Syntax.sigattrs = uu____9351;_},FStar_Pervasives_Native.None
            ),uu____9352)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9401 ->
          let uu____9422 =
            let uu____9423 =
              let uu____9428 = name_not_found lid in
              (uu____9428, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9423 in
          FStar_Exn.raise uu____9422
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9443 = lookup_qname env lid in
      match uu____9443 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9468,uvs,t,uu____9471,uu____9472,uu____9473);
              FStar_Syntax_Syntax.sigrng = uu____9474;
              FStar_Syntax_Syntax.sigquals = uu____9475;
              FStar_Syntax_Syntax.sigmeta = uu____9476;
              FStar_Syntax_Syntax.sigattrs = uu____9477;_},FStar_Pervasives_Native.None
            ),uu____9478)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9531 ->
          let uu____9552 =
            let uu____9553 =
              let uu____9558 = name_not_found lid in
              (uu____9558, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9553 in
          FStar_Exn.raise uu____9552
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9575 = lookup_qname env lid in
      match uu____9575 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9602,uu____9603,uu____9604,uu____9605,uu____9606,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9608;
              FStar_Syntax_Syntax.sigquals = uu____9609;
              FStar_Syntax_Syntax.sigmeta = uu____9610;
              FStar_Syntax_Syntax.sigattrs = uu____9611;_},uu____9612),uu____9613)
          -> (true, dcs)
      | uu____9674 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9703 = lookup_qname env lid in
      match uu____9703 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9724,uu____9725,uu____9726,l,uu____9728,uu____9729);
              FStar_Syntax_Syntax.sigrng = uu____9730;
              FStar_Syntax_Syntax.sigquals = uu____9731;
              FStar_Syntax_Syntax.sigmeta = uu____9732;
              FStar_Syntax_Syntax.sigattrs = uu____9733;_},uu____9734),uu____9735)
          -> l
      | uu____9790 ->
          let uu____9811 =
            let uu____9812 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____9812 in
          failwith uu____9811
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
        let uu____9846 = lookup_qname env lid in
        match uu____9846 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____9874) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____9925,lbs),uu____9927) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____9955 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____9955
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____9987 -> FStar_Pervasives_Native.None)
        | uu____9992 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10027 = lookup_qname env ftv in
      match uu____10027 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10051) ->
          let uu____10096 = effect_signature se in
          (match uu____10096 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10117,t),r) ->
               let uu____10132 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10132)
      | uu____10133 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10160 = try_lookup_effect_lid env ftv in
      match uu____10160 with
      | FStar_Pervasives_Native.None  ->
          let uu____10163 =
            let uu____10164 =
              let uu____10169 = name_not_found ftv in
              (uu____10169, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10164 in
          FStar_Exn.raise uu____10163
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
        let uu____10186 = lookup_qname env lid0 in
        match uu____10186 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10217);
                FStar_Syntax_Syntax.sigrng = uu____10218;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10220;
                FStar_Syntax_Syntax.sigattrs = uu____10221;_},FStar_Pervasives_Native.None
              ),uu____10222)
            ->
            let lid1 =
              let uu____10276 =
                let uu____10277 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10277 in
              FStar_Ident.set_lid_range lid uu____10276 in
            let uu____10278 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___253_10282  ->
                      match uu___253_10282 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10283 -> false)) in
            if uu____10278
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10297 =
                      let uu____10298 =
                        let uu____10299 = get_range env in
                        FStar_Range.string_of_range uu____10299 in
                      let uu____10300 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10301 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10298 uu____10300 uu____10301 in
                    failwith uu____10297) in
               match (binders, univs1) with
               | ([],uu____10308) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10325,uu____10326::uu____10327::uu____10328) ->
                   let uu____10333 =
                     let uu____10334 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10335 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10334 uu____10335 in
                   failwith uu____10333
               | uu____10342 ->
                   let uu____10347 =
                     let uu____10352 =
                       let uu____10353 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10353) in
                     inst_tscheme_with uu____10352 insts in
                   (match uu____10347 with
                    | (uu____10364,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10367 =
                          let uu____10368 = FStar_Syntax_Subst.compress t1 in
                          uu____10368.FStar_Syntax_Syntax.n in
                        (match uu____10367 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10415 -> failwith "Impossible")))
        | uu____10422 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10462 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10462 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10475,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10482 = find1 l2 in
            (match uu____10482 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10489 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10489 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10493 = find1 l in
            (match uu____10493 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10507 = lookup_qname env l1 in
      match uu____10507 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10530;
              FStar_Syntax_Syntax.sigrng = uu____10531;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10533;
              FStar_Syntax_Syntax.sigattrs = uu____10534;_},uu____10535),uu____10536)
          -> q
      | uu____10587 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10620 =
          let uu____10621 =
            let uu____10622 = FStar_Util.string_of_int i in
            let uu____10623 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10622 uu____10623 in
          failwith uu____10621 in
        let uu____10624 = lookup_datacon env lid in
        match uu____10624 with
        | (uu____10629,t) ->
            let uu____10631 =
              let uu____10632 = FStar_Syntax_Subst.compress t in
              uu____10632.FStar_Syntax_Syntax.n in
            (match uu____10631 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10636) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10667 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10667
                      FStar_Pervasives_Native.fst)
             | uu____10676 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10683 = lookup_qname env l in
      match uu____10683 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10704,uu____10705,uu____10706);
              FStar_Syntax_Syntax.sigrng = uu____10707;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10709;
              FStar_Syntax_Syntax.sigattrs = uu____10710;_},uu____10711),uu____10712)
          ->
          FStar_Util.for_some
            (fun uu___254_10765  ->
               match uu___254_10765 with
               | FStar_Syntax_Syntax.Projector uu____10766 -> true
               | uu____10771 -> false) quals
      | uu____10772 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10799 = lookup_qname env lid in
      match uu____10799 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____10820,uu____10821,uu____10822,uu____10823,uu____10824,uu____10825);
              FStar_Syntax_Syntax.sigrng = uu____10826;
              FStar_Syntax_Syntax.sigquals = uu____10827;
              FStar_Syntax_Syntax.sigmeta = uu____10828;
              FStar_Syntax_Syntax.sigattrs = uu____10829;_},uu____10830),uu____10831)
          -> true
      | uu____10886 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____10913 = lookup_qname env lid in
      match uu____10913 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____10934,uu____10935,uu____10936,uu____10937,uu____10938,uu____10939);
              FStar_Syntax_Syntax.sigrng = uu____10940;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10942;
              FStar_Syntax_Syntax.sigattrs = uu____10943;_},uu____10944),uu____10945)
          ->
          FStar_Util.for_some
            (fun uu___255_11006  ->
               match uu___255_11006 with
               | FStar_Syntax_Syntax.RecordType uu____11007 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11016 -> true
               | uu____11025 -> false) quals
      | uu____11026 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11053 = lookup_qname env lid in
      match uu____11053 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11074,uu____11075);
              FStar_Syntax_Syntax.sigrng = uu____11076;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11078;
              FStar_Syntax_Syntax.sigattrs = uu____11079;_},uu____11080),uu____11081)
          ->
          FStar_Util.for_some
            (fun uu___256_11138  ->
               match uu___256_11138 with
               | FStar_Syntax_Syntax.Action uu____11139 -> true
               | uu____11140 -> false) quals
      | uu____11141 -> false
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
      let uu____11171 =
        let uu____11172 = FStar_Syntax_Util.un_uinst head1 in
        uu____11172.FStar_Syntax_Syntax.n in
      match uu____11171 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11176 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11241 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11257) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11274 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11281 ->
                 FStar_Pervasives_Native.Some true
             | uu____11298 -> FStar_Pervasives_Native.Some false) in
      let uu____11299 =
        let uu____11302 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11302 mapper in
      match uu____11299 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11348 = lookup_qname env lid in
      match uu____11348 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11369,uu____11370,tps,uu____11372,uu____11373,uu____11374);
              FStar_Syntax_Syntax.sigrng = uu____11375;
              FStar_Syntax_Syntax.sigquals = uu____11376;
              FStar_Syntax_Syntax.sigmeta = uu____11377;
              FStar_Syntax_Syntax.sigattrs = uu____11378;_},uu____11379),uu____11380)
          -> FStar_List.length tps
      | uu____11443 ->
          let uu____11464 =
            let uu____11465 =
              let uu____11470 = name_not_found lid in
              (uu____11470, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11465 in
          FStar_Exn.raise uu____11464
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
           (fun uu____11510  ->
              match uu____11510 with
              | (d,uu____11518) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11529 = effect_decl_opt env l in
      match uu____11529 with
      | FStar_Pervasives_Native.None  ->
          let uu____11544 =
            let uu____11545 =
              let uu____11550 = name_not_found l in
              (uu____11550, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11545 in
          FStar_Exn.raise uu____11544
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
            (let uu____11613 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11666  ->
                       match uu____11666 with
                       | (m1,m2,uu____11679,uu____11680,uu____11681) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11613 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11698 =
                   let uu____11699 =
                     let uu____11704 =
                       let uu____11705 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11706 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11705
                         uu____11706 in
                     (uu____11704, (env.range)) in
                   FStar_Errors.Error uu____11699 in
                 FStar_Exn.raise uu____11698
             | FStar_Pervasives_Native.Some
                 (uu____11713,uu____11714,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____11751 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____11751)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____11778 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____11804  ->
                match uu____11804 with
                | (d,uu____11810) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____11778 with
      | FStar_Pervasives_Native.None  ->
          let uu____11821 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____11821
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____11834 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____11834 with
           | (uu____11845,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____11855)::(wp,uu____11857)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____11893 -> failwith "Impossible"))
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
                 let uu____11936 = get_range env in
                 let uu____11937 =
                   let uu____11940 =
                     let uu____11941 =
                       let uu____11956 =
                         let uu____11959 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____11959] in
                       (null_wp, uu____11956) in
                     FStar_Syntax_Syntax.Tm_app uu____11941 in
                   FStar_Syntax_Syntax.mk uu____11940 in
                 uu____11937 FStar_Pervasives_Native.None uu____11936 in
               let uu____11965 =
                 let uu____11966 =
                   let uu____11975 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____11975] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____11966;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____11965)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___271_11984 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___271_11984.order);
              joins = (uu___271_11984.joins)
            } in
          let uu___272_11993 = env in
          {
            solver = (uu___272_11993.solver);
            range = (uu___272_11993.range);
            curmodule = (uu___272_11993.curmodule);
            gamma = (uu___272_11993.gamma);
            gamma_cache = (uu___272_11993.gamma_cache);
            modules = (uu___272_11993.modules);
            expected_typ = (uu___272_11993.expected_typ);
            sigtab = (uu___272_11993.sigtab);
            is_pattern = (uu___272_11993.is_pattern);
            instantiate_imp = (uu___272_11993.instantiate_imp);
            effects;
            generalize = (uu___272_11993.generalize);
            letrecs = (uu___272_11993.letrecs);
            top_level = (uu___272_11993.top_level);
            check_uvars = (uu___272_11993.check_uvars);
            use_eq = (uu___272_11993.use_eq);
            is_iface = (uu___272_11993.is_iface);
            admit = (uu___272_11993.admit);
            lax = (uu___272_11993.lax);
            lax_universes = (uu___272_11993.lax_universes);
            failhard = (uu___272_11993.failhard);
            nosynth = (uu___272_11993.nosynth);
            tc_term = (uu___272_11993.tc_term);
            type_of = (uu___272_11993.type_of);
            universe_of = (uu___272_11993.universe_of);
            use_bv_sorts = (uu___272_11993.use_bv_sorts);
            qname_and_index = (uu___272_11993.qname_and_index);
            proof_ns = (uu___272_11993.proof_ns);
            synth = (uu___272_11993.synth);
            is_native_tactic = (uu___272_11993.is_native_tactic);
            identifier_info = (uu___272_11993.identifier_info);
            tc_hooks = (uu___272_11993.tc_hooks);
            dsenv = (uu___272_11993.dsenv)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____12010 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____12010 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____12100 = (e1.mlift).mlift_wp t wp in
                              let uu____12101 = l1 t wp e in
                              l2 t uu____12100 uu____12101))
                | uu____12102 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____12141 = inst_tscheme lift_t in
            match uu____12141 with
            | (uu____12148,lift_t1) ->
                let uu____12150 =
                  let uu____12153 =
                    let uu____12154 =
                      let uu____12169 =
                        let uu____12172 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12173 =
                          let uu____12176 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12176] in
                        uu____12172 :: uu____12173 in
                      (lift_t1, uu____12169) in
                    FStar_Syntax_Syntax.Tm_app uu____12154 in
                  FStar_Syntax_Syntax.mk uu____12153 in
                uu____12150 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____12217 = inst_tscheme lift_t in
            match uu____12217 with
            | (uu____12224,lift_t1) ->
                let uu____12226 =
                  let uu____12229 =
                    let uu____12230 =
                      let uu____12245 =
                        let uu____12248 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12249 =
                          let uu____12252 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12253 =
                            let uu____12256 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12256] in
                          uu____12252 :: uu____12253 in
                        uu____12248 :: uu____12249 in
                      (lift_t1, uu____12245) in
                    FStar_Syntax_Syntax.Tm_app uu____12230 in
                  FStar_Syntax_Syntax.mk uu____12229 in
                uu____12226 FStar_Pervasives_Native.None
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
              let uu____12294 =
                let uu____12295 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12295
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12294 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12299 =
              let uu____12300 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____12300 in
            let uu____12301 =
              let uu____12302 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12320 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12320) in
              FStar_Util.dflt "none" uu____12302 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12299
              uu____12301 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12346  ->
                    match uu____12346 with
                    | (e,uu____12354) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12373 =
            match uu____12373 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____12411 =
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
                                    (let uu____12432 =
                                       let uu____12441 =
                                         find_edge order1 (i, k) in
                                       let uu____12444 =
                                         find_edge order1 (k, j) in
                                       (uu____12441, uu____12444) in
                                     match uu____12432 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12459 =
                                           compose_edges e1 e2 in
                                         [uu____12459]
                                     | uu____12460 -> []))))) in
              FStar_List.append order1 uu____12411 in
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
                   let uu____12489 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12491 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12491
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12489
                   then
                     let uu____12496 =
                       let uu____12497 =
                         let uu____12502 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12503 = get_range env in
                         (uu____12502, uu____12503) in
                       FStar_Errors.Error uu____12497 in
                     FStar_Exn.raise uu____12496
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
                                            let uu____12628 =
                                              let uu____12637 =
                                                find_edge order2 (i, k) in
                                              let uu____12640 =
                                                find_edge order2 (j, k) in
                                              (uu____12637, uu____12640) in
                                            match uu____12628 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12682,uu____12683)
                                                     ->
                                                     let uu____12690 =
                                                       let uu____12695 =
                                                         let uu____12696 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12696 in
                                                       let uu____12699 =
                                                         let uu____12700 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____12700 in
                                                       (uu____12695,
                                                         uu____12699) in
                                                     (match uu____12690 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate\n";
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
                                            | uu____12735 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___273_12808 = env.effects in
              { decls = (uu___273_12808.decls); order = order2; joins } in
            let uu___274_12809 = env in
            {
              solver = (uu___274_12809.solver);
              range = (uu___274_12809.range);
              curmodule = (uu___274_12809.curmodule);
              gamma = (uu___274_12809.gamma);
              gamma_cache = (uu___274_12809.gamma_cache);
              modules = (uu___274_12809.modules);
              expected_typ = (uu___274_12809.expected_typ);
              sigtab = (uu___274_12809.sigtab);
              is_pattern = (uu___274_12809.is_pattern);
              instantiate_imp = (uu___274_12809.instantiate_imp);
              effects;
              generalize = (uu___274_12809.generalize);
              letrecs = (uu___274_12809.letrecs);
              top_level = (uu___274_12809.top_level);
              check_uvars = (uu___274_12809.check_uvars);
              use_eq = (uu___274_12809.use_eq);
              is_iface = (uu___274_12809.is_iface);
              admit = (uu___274_12809.admit);
              lax = (uu___274_12809.lax);
              lax_universes = (uu___274_12809.lax_universes);
              failhard = (uu___274_12809.failhard);
              nosynth = (uu___274_12809.nosynth);
              tc_term = (uu___274_12809.tc_term);
              type_of = (uu___274_12809.type_of);
              universe_of = (uu___274_12809.universe_of);
              use_bv_sorts = (uu___274_12809.use_bv_sorts);
              qname_and_index = (uu___274_12809.qname_and_index);
              proof_ns = (uu___274_12809.proof_ns);
              synth = (uu___274_12809.synth);
              is_native_tactic = (uu___274_12809.is_native_tactic);
              identifier_info = (uu___274_12809.identifier_info);
              tc_hooks = (uu___274_12809.tc_hooks);
              dsenv = (uu___274_12809.dsenv)
            }))
      | uu____12810 -> env
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
        | uu____12834 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____12842 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____12842 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____12859 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____12859 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____12877 =
                     let uu____12878 =
                       let uu____12883 =
                         let uu____12884 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____12889 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____12896 =
                           let uu____12897 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____12897 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____12884 uu____12889 uu____12896 in
                       (uu____12883, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____12878 in
                   FStar_Exn.raise uu____12877)
                else ();
                (let inst1 =
                   let uu____12902 =
                     let uu____12911 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____12911 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____12928  ->
                        fun uu____12929  ->
                          match (uu____12928, uu____12929) with
                          | ((x,uu____12951),(t,uu____12953)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____12902 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____12972 =
                     let uu___275_12973 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___275_12973.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___275_12973.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___275_12973.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___275_12973.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____12972
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
          let uu____12995 = effect_decl_opt env effect_name in
          match uu____12995 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13028 =
                only_reifiable &&
                  (let uu____13030 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13030) in
              if uu____13028
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13046 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13065 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13094 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13094
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13095 =
                             let uu____13096 =
                               let uu____13101 = get_range env in
                               (message, uu____13101) in
                             FStar_Errors.Error uu____13096 in
                           FStar_Exn.raise uu____13095 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13111 =
                       let uu____13114 = get_range env in
                       let uu____13115 =
                         let uu____13118 =
                           let uu____13119 =
                             let uu____13134 =
                               let uu____13137 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13137; wp] in
                             (repr, uu____13134) in
                           FStar_Syntax_Syntax.Tm_app uu____13119 in
                         FStar_Syntax_Syntax.mk uu____13118 in
                       uu____13115 FStar_Pervasives_Native.None uu____13114 in
                     FStar_Pervasives_Native.Some uu____13111)
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
          let uu____13183 =
            let uu____13184 =
              let uu____13189 =
                let uu____13190 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13190 in
              let uu____13191 = get_range env in (uu____13189, uu____13191) in
            FStar_Errors.Error uu____13184 in
          FStar_Exn.raise uu____13183 in
        let uu____13192 = effect_repr_aux true env c u_c in
        match uu____13192 with
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
      | uu____13226 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13233 =
        let uu____13234 = FStar_Syntax_Subst.compress t in
        uu____13234.FStar_Syntax_Syntax.n in
      match uu____13233 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13237,c) ->
          is_reifiable_comp env c
      | uu____13255 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13277)::uu____13278 -> x :: rest
        | (Binding_sig_inst uu____13287)::uu____13288 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13303 = push1 x rest1 in local :: uu____13303 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___276_13307 = env in
       let uu____13308 = push1 s env.gamma in
       {
         solver = (uu___276_13307.solver);
         range = (uu___276_13307.range);
         curmodule = (uu___276_13307.curmodule);
         gamma = uu____13308;
         gamma_cache = (uu___276_13307.gamma_cache);
         modules = (uu___276_13307.modules);
         expected_typ = (uu___276_13307.expected_typ);
         sigtab = (uu___276_13307.sigtab);
         is_pattern = (uu___276_13307.is_pattern);
         instantiate_imp = (uu___276_13307.instantiate_imp);
         effects = (uu___276_13307.effects);
         generalize = (uu___276_13307.generalize);
         letrecs = (uu___276_13307.letrecs);
         top_level = (uu___276_13307.top_level);
         check_uvars = (uu___276_13307.check_uvars);
         use_eq = (uu___276_13307.use_eq);
         is_iface = (uu___276_13307.is_iface);
         admit = (uu___276_13307.admit);
         lax = (uu___276_13307.lax);
         lax_universes = (uu___276_13307.lax_universes);
         failhard = (uu___276_13307.failhard);
         nosynth = (uu___276_13307.nosynth);
         tc_term = (uu___276_13307.tc_term);
         type_of = (uu___276_13307.type_of);
         universe_of = (uu___276_13307.universe_of);
         use_bv_sorts = (uu___276_13307.use_bv_sorts);
         qname_and_index = (uu___276_13307.qname_and_index);
         proof_ns = (uu___276_13307.proof_ns);
         synth = (uu___276_13307.synth);
         is_native_tactic = (uu___276_13307.is_native_tactic);
         identifier_info = (uu___276_13307.identifier_info);
         tc_hooks = (uu___276_13307.tc_hooks);
         dsenv = (uu___276_13307.dsenv)
       })
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
      let uu___277_13338 = env in
      {
        solver = (uu___277_13338.solver);
        range = (uu___277_13338.range);
        curmodule = (uu___277_13338.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___277_13338.gamma_cache);
        modules = (uu___277_13338.modules);
        expected_typ = (uu___277_13338.expected_typ);
        sigtab = (uu___277_13338.sigtab);
        is_pattern = (uu___277_13338.is_pattern);
        instantiate_imp = (uu___277_13338.instantiate_imp);
        effects = (uu___277_13338.effects);
        generalize = (uu___277_13338.generalize);
        letrecs = (uu___277_13338.letrecs);
        top_level = (uu___277_13338.top_level);
        check_uvars = (uu___277_13338.check_uvars);
        use_eq = (uu___277_13338.use_eq);
        is_iface = (uu___277_13338.is_iface);
        admit = (uu___277_13338.admit);
        lax = (uu___277_13338.lax);
        lax_universes = (uu___277_13338.lax_universes);
        failhard = (uu___277_13338.failhard);
        nosynth = (uu___277_13338.nosynth);
        tc_term = (uu___277_13338.tc_term);
        type_of = (uu___277_13338.type_of);
        universe_of = (uu___277_13338.universe_of);
        use_bv_sorts = (uu___277_13338.use_bv_sorts);
        qname_and_index = (uu___277_13338.qname_and_index);
        proof_ns = (uu___277_13338.proof_ns);
        synth = (uu___277_13338.synth);
        is_native_tactic = (uu___277_13338.is_native_tactic);
        identifier_info = (uu___277_13338.identifier_info);
        tc_hooks = (uu___277_13338.tc_hooks);
        dsenv = (uu___277_13338.dsenv)
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
            (let uu___278_13369 = env in
             {
               solver = (uu___278_13369.solver);
               range = (uu___278_13369.range);
               curmodule = (uu___278_13369.curmodule);
               gamma = rest;
               gamma_cache = (uu___278_13369.gamma_cache);
               modules = (uu___278_13369.modules);
               expected_typ = (uu___278_13369.expected_typ);
               sigtab = (uu___278_13369.sigtab);
               is_pattern = (uu___278_13369.is_pattern);
               instantiate_imp = (uu___278_13369.instantiate_imp);
               effects = (uu___278_13369.effects);
               generalize = (uu___278_13369.generalize);
               letrecs = (uu___278_13369.letrecs);
               top_level = (uu___278_13369.top_level);
               check_uvars = (uu___278_13369.check_uvars);
               use_eq = (uu___278_13369.use_eq);
               is_iface = (uu___278_13369.is_iface);
               admit = (uu___278_13369.admit);
               lax = (uu___278_13369.lax);
               lax_universes = (uu___278_13369.lax_universes);
               failhard = (uu___278_13369.failhard);
               nosynth = (uu___278_13369.nosynth);
               tc_term = (uu___278_13369.tc_term);
               type_of = (uu___278_13369.type_of);
               universe_of = (uu___278_13369.universe_of);
               use_bv_sorts = (uu___278_13369.use_bv_sorts);
               qname_and_index = (uu___278_13369.qname_and_index);
               proof_ns = (uu___278_13369.proof_ns);
               synth = (uu___278_13369.synth);
               is_native_tactic = (uu___278_13369.is_native_tactic);
               identifier_info = (uu___278_13369.identifier_info);
               tc_hooks = (uu___278_13369.tc_hooks);
               dsenv = (uu___278_13369.dsenv)
             }))
    | uu____13370 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13392  ->
             match uu____13392 with | (x,uu____13398) -> push_bv env1 x) env
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
            let uu___279_13426 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___279_13426.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___279_13426.FStar_Syntax_Syntax.index);
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
      (let uu___280_13456 = env in
       {
         solver = (uu___280_13456.solver);
         range = (uu___280_13456.range);
         curmodule = (uu___280_13456.curmodule);
         gamma = [];
         gamma_cache = (uu___280_13456.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___280_13456.sigtab);
         is_pattern = (uu___280_13456.is_pattern);
         instantiate_imp = (uu___280_13456.instantiate_imp);
         effects = (uu___280_13456.effects);
         generalize = (uu___280_13456.generalize);
         letrecs = (uu___280_13456.letrecs);
         top_level = (uu___280_13456.top_level);
         check_uvars = (uu___280_13456.check_uvars);
         use_eq = (uu___280_13456.use_eq);
         is_iface = (uu___280_13456.is_iface);
         admit = (uu___280_13456.admit);
         lax = (uu___280_13456.lax);
         lax_universes = (uu___280_13456.lax_universes);
         failhard = (uu___280_13456.failhard);
         nosynth = (uu___280_13456.nosynth);
         tc_term = (uu___280_13456.tc_term);
         type_of = (uu___280_13456.type_of);
         universe_of = (uu___280_13456.universe_of);
         use_bv_sorts = (uu___280_13456.use_bv_sorts);
         qname_and_index = (uu___280_13456.qname_and_index);
         proof_ns = (uu___280_13456.proof_ns);
         synth = (uu___280_13456.synth);
         is_native_tactic = (uu___280_13456.is_native_tactic);
         identifier_info = (uu___280_13456.identifier_info);
         tc_hooks = (uu___280_13456.tc_hooks);
         dsenv = (uu___280_13456.dsenv)
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
        let uu____13488 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13488 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13516 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13516)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___281_13529 = env in
      {
        solver = (uu___281_13529.solver);
        range = (uu___281_13529.range);
        curmodule = (uu___281_13529.curmodule);
        gamma = (uu___281_13529.gamma);
        gamma_cache = (uu___281_13529.gamma_cache);
        modules = (uu___281_13529.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___281_13529.sigtab);
        is_pattern = (uu___281_13529.is_pattern);
        instantiate_imp = (uu___281_13529.instantiate_imp);
        effects = (uu___281_13529.effects);
        generalize = (uu___281_13529.generalize);
        letrecs = (uu___281_13529.letrecs);
        top_level = (uu___281_13529.top_level);
        check_uvars = (uu___281_13529.check_uvars);
        use_eq = false;
        is_iface = (uu___281_13529.is_iface);
        admit = (uu___281_13529.admit);
        lax = (uu___281_13529.lax);
        lax_universes = (uu___281_13529.lax_universes);
        failhard = (uu___281_13529.failhard);
        nosynth = (uu___281_13529.nosynth);
        tc_term = (uu___281_13529.tc_term);
        type_of = (uu___281_13529.type_of);
        universe_of = (uu___281_13529.universe_of);
        use_bv_sorts = (uu___281_13529.use_bv_sorts);
        qname_and_index = (uu___281_13529.qname_and_index);
        proof_ns = (uu___281_13529.proof_ns);
        synth = (uu___281_13529.synth);
        is_native_tactic = (uu___281_13529.is_native_tactic);
        identifier_info = (uu___281_13529.identifier_info);
        tc_hooks = (uu___281_13529.tc_hooks);
        dsenv = (uu___281_13529.dsenv)
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
    let uu____13553 = expected_typ env_ in
    ((let uu___282_13559 = env_ in
      {
        solver = (uu___282_13559.solver);
        range = (uu___282_13559.range);
        curmodule = (uu___282_13559.curmodule);
        gamma = (uu___282_13559.gamma);
        gamma_cache = (uu___282_13559.gamma_cache);
        modules = (uu___282_13559.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___282_13559.sigtab);
        is_pattern = (uu___282_13559.is_pattern);
        instantiate_imp = (uu___282_13559.instantiate_imp);
        effects = (uu___282_13559.effects);
        generalize = (uu___282_13559.generalize);
        letrecs = (uu___282_13559.letrecs);
        top_level = (uu___282_13559.top_level);
        check_uvars = (uu___282_13559.check_uvars);
        use_eq = false;
        is_iface = (uu___282_13559.is_iface);
        admit = (uu___282_13559.admit);
        lax = (uu___282_13559.lax);
        lax_universes = (uu___282_13559.lax_universes);
        failhard = (uu___282_13559.failhard);
        nosynth = (uu___282_13559.nosynth);
        tc_term = (uu___282_13559.tc_term);
        type_of = (uu___282_13559.type_of);
        universe_of = (uu___282_13559.universe_of);
        use_bv_sorts = (uu___282_13559.use_bv_sorts);
        qname_and_index = (uu___282_13559.qname_and_index);
        proof_ns = (uu___282_13559.proof_ns);
        synth = (uu___282_13559.synth);
        is_native_tactic = (uu___282_13559.is_native_tactic);
        identifier_info = (uu___282_13559.identifier_info);
        tc_hooks = (uu___282_13559.tc_hooks);
        dsenv = (uu___282_13559.dsenv)
      }), uu____13553)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13572 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___257_13582  ->
                    match uu___257_13582 with
                    | Binding_sig (uu____13585,se) -> [se]
                    | uu____13591 -> [])) in
          FStar_All.pipe_right uu____13572 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___283_13598 = env in
       {
         solver = (uu___283_13598.solver);
         range = (uu___283_13598.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___283_13598.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___283_13598.expected_typ);
         sigtab = (uu___283_13598.sigtab);
         is_pattern = (uu___283_13598.is_pattern);
         instantiate_imp = (uu___283_13598.instantiate_imp);
         effects = (uu___283_13598.effects);
         generalize = (uu___283_13598.generalize);
         letrecs = (uu___283_13598.letrecs);
         top_level = (uu___283_13598.top_level);
         check_uvars = (uu___283_13598.check_uvars);
         use_eq = (uu___283_13598.use_eq);
         is_iface = (uu___283_13598.is_iface);
         admit = (uu___283_13598.admit);
         lax = (uu___283_13598.lax);
         lax_universes = (uu___283_13598.lax_universes);
         failhard = (uu___283_13598.failhard);
         nosynth = (uu___283_13598.nosynth);
         tc_term = (uu___283_13598.tc_term);
         type_of = (uu___283_13598.type_of);
         universe_of = (uu___283_13598.universe_of);
         use_bv_sorts = (uu___283_13598.use_bv_sorts);
         qname_and_index = (uu___283_13598.qname_and_index);
         proof_ns = (uu___283_13598.proof_ns);
         synth = (uu___283_13598.synth);
         is_native_tactic = (uu___283_13598.is_native_tactic);
         identifier_info = (uu___283_13598.identifier_info);
         tc_hooks = (uu___283_13598.tc_hooks);
         dsenv = (uu___283_13598.dsenv)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13679)::tl1 -> aux out tl1
      | (Binding_lid (uu____13683,(uu____13684,t)))::tl1 ->
          let uu____13699 =
            let uu____13706 = FStar_Syntax_Free.uvars t in
            ext out uu____13706 in
          aux uu____13699 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13713;
            FStar_Syntax_Syntax.index = uu____13714;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13721 =
            let uu____13728 = FStar_Syntax_Free.uvars t in
            ext out uu____13728 in
          aux uu____13721 tl1
      | (Binding_sig uu____13735)::uu____13736 -> out
      | (Binding_sig_inst uu____13745)::uu____13746 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13801)::tl1 -> aux out tl1
      | (Binding_univ uu____13813)::tl1 -> aux out tl1
      | (Binding_lid (uu____13817,(uu____13818,t)))::tl1 ->
          let uu____13833 =
            let uu____13836 = FStar_Syntax_Free.univs t in
            ext out uu____13836 in
          aux uu____13833 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13839;
            FStar_Syntax_Syntax.index = uu____13840;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13847 =
            let uu____13850 = FStar_Syntax_Free.univs t in
            ext out uu____13850 in
          aux uu____13847 tl1
      | (Binding_sig uu____13853)::uu____13854 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____13907)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____13923 = FStar_Util.fifo_set_add uname out in
          aux uu____13923 tl1
      | (Binding_lid (uu____13926,(uu____13927,t)))::tl1 ->
          let uu____13942 =
            let uu____13945 = FStar_Syntax_Free.univnames t in
            ext out uu____13945 in
          aux uu____13942 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____13948;
            FStar_Syntax_Syntax.index = uu____13949;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____13956 =
            let uu____13959 = FStar_Syntax_Free.univnames t in
            ext out uu____13959 in
          aux uu____13956 tl1
      | (Binding_sig uu____13962)::uu____13963 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___258_13987  ->
            match uu___258_13987 with
            | Binding_var x -> [x]
            | Binding_lid uu____13991 -> []
            | Binding_sig uu____13996 -> []
            | Binding_univ uu____14003 -> []
            | Binding_sig_inst uu____14004 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14020 =
      let uu____14023 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14023
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14020 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14045 =
      let uu____14046 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___259_14056  ->
                match uu___259_14056 with
                | Binding_var x ->
                    let uu____14058 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14058
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14061) ->
                    let uu____14062 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14062
                | Binding_sig (ls,uu____14064) ->
                    let uu____14069 =
                      let uu____14070 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14070
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14069
                | Binding_sig_inst (ls,uu____14080,uu____14081) ->
                    let uu____14086 =
                      let uu____14087 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14087
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14086)) in
      FStar_All.pipe_right uu____14046 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14045 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14104 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14104
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14132  ->
                 fun uu____14133  ->
                   match (uu____14132, uu____14133) with
                   | ((b1,uu____14151),(b2,uu____14153)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___260_14195  ->
    match uu___260_14195 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14196 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___261_14214  ->
             match uu___261_14214 with
             | Binding_sig (lids,uu____14220) -> FStar_List.append lids keys
             | uu____14225 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14231  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14265) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14284,uu____14285) -> false in
      let uu____14294 =
        FStar_List.tryFind
          (fun uu____14312  ->
             match uu____14312 with | (p,uu____14320) -> list_prefix p path)
          env.proof_ns in
      match uu____14294 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14331,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14349 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14349
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___284_14361 = e in
        {
          solver = (uu___284_14361.solver);
          range = (uu___284_14361.range);
          curmodule = (uu___284_14361.curmodule);
          gamma = (uu___284_14361.gamma);
          gamma_cache = (uu___284_14361.gamma_cache);
          modules = (uu___284_14361.modules);
          expected_typ = (uu___284_14361.expected_typ);
          sigtab = (uu___284_14361.sigtab);
          is_pattern = (uu___284_14361.is_pattern);
          instantiate_imp = (uu___284_14361.instantiate_imp);
          effects = (uu___284_14361.effects);
          generalize = (uu___284_14361.generalize);
          letrecs = (uu___284_14361.letrecs);
          top_level = (uu___284_14361.top_level);
          check_uvars = (uu___284_14361.check_uvars);
          use_eq = (uu___284_14361.use_eq);
          is_iface = (uu___284_14361.is_iface);
          admit = (uu___284_14361.admit);
          lax = (uu___284_14361.lax);
          lax_universes = (uu___284_14361.lax_universes);
          failhard = (uu___284_14361.failhard);
          nosynth = (uu___284_14361.nosynth);
          tc_term = (uu___284_14361.tc_term);
          type_of = (uu___284_14361.type_of);
          universe_of = (uu___284_14361.universe_of);
          use_bv_sorts = (uu___284_14361.use_bv_sorts);
          qname_and_index = (uu___284_14361.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___284_14361.synth);
          is_native_tactic = (uu___284_14361.is_native_tactic);
          identifier_info = (uu___284_14361.identifier_info);
          tc_hooks = (uu___284_14361.tc_hooks);
          dsenv = (uu___284_14361.dsenv)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___285_14387 = e in
      {
        solver = (uu___285_14387.solver);
        range = (uu___285_14387.range);
        curmodule = (uu___285_14387.curmodule);
        gamma = (uu___285_14387.gamma);
        gamma_cache = (uu___285_14387.gamma_cache);
        modules = (uu___285_14387.modules);
        expected_typ = (uu___285_14387.expected_typ);
        sigtab = (uu___285_14387.sigtab);
        is_pattern = (uu___285_14387.is_pattern);
        instantiate_imp = (uu___285_14387.instantiate_imp);
        effects = (uu___285_14387.effects);
        generalize = (uu___285_14387.generalize);
        letrecs = (uu___285_14387.letrecs);
        top_level = (uu___285_14387.top_level);
        check_uvars = (uu___285_14387.check_uvars);
        use_eq = (uu___285_14387.use_eq);
        is_iface = (uu___285_14387.is_iface);
        admit = (uu___285_14387.admit);
        lax = (uu___285_14387.lax);
        lax_universes = (uu___285_14387.lax_universes);
        failhard = (uu___285_14387.failhard);
        nosynth = (uu___285_14387.nosynth);
        tc_term = (uu___285_14387.tc_term);
        type_of = (uu___285_14387.type_of);
        universe_of = (uu___285_14387.universe_of);
        use_bv_sorts = (uu___285_14387.use_bv_sorts);
        qname_and_index = (uu___285_14387.qname_and_index);
        proof_ns = ns;
        synth = (uu___285_14387.synth);
        is_native_tactic = (uu___285_14387.is_native_tactic);
        identifier_info = (uu___285_14387.identifier_info);
        tc_hooks = (uu___285_14387.tc_hooks);
        dsenv = (uu___285_14387.dsenv)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14398 = FStar_Syntax_Free.names t in
      let uu____14401 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14398 uu____14401
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14418 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14418
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14424 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14424
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14439 =
      match uu____14439 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14455 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14455) in
    let uu____14457 =
      let uu____14460 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14460 FStar_List.rev in
    FStar_All.pipe_right uu____14457 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14477  -> ());
    push = (fun uu____14479  -> ());
    pop = (fun uu____14481  -> ());
    encode_modul = (fun uu____14484  -> fun uu____14485  -> ());
    encode_sig = (fun uu____14488  -> fun uu____14489  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14495 =
             let uu____14502 = FStar_Options.peek () in (e, g, uu____14502) in
           [uu____14495]);
    solve = (fun uu____14518  -> fun uu____14519  -> fun uu____14520  -> ());
    finish = (fun uu____14526  -> ());
    refresh = (fun uu____14528  -> ())
  }