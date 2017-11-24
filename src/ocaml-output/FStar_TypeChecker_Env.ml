
open Prims
open FStar_Pervasives
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
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkmlift__item__mlift_wp:
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let __proj__Mkmlift__item__mlift_term:
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
  =
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}


let __proj__Mkedge__item__msource : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__msource
end))


let __proj__Mkedge__item__mtarget : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__mtarget
end))


let __proj__Mkedge__item__mlift : edge  ->  mlift = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__mlift
end))

type effects =
{decls : (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let __proj__Mkeffects__item__decls : effects  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__decls
end))


let __proj__Mkeffects__item__order : effects  ->  edge Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__order
end))


let __proj__Mkeffects__item__joins : effects  ->  (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__joins
end))


type name_prefix =
Prims.string Prims.list


type proof_namespace =
(name_prefix * Prims.bool) Prims.list


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list;
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
  dsenv: FStar_ToSyntax_Env.env;
  dep_graph: FStar_Parser_Dep.deps;}[@@deriving show]
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__solver
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__range
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma_cache
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__modules
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__expected_typ
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__sigtab
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_pattern
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__instantiate_imp
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__effects
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__generalize
let __proj__Mkenv__item__letrecs:
  env ->
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__letrecs
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__top_level
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_uvars
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_eq
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_iface
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__admit
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax_universes
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__failhard
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__nosynth
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_term
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__type_of
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__universe_of
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_bv_sorts
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qname_and_index
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__proof_ns
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_native_tactic
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__identifier_info
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dsenv
let __proj__Mkenv__item__dep_graph: env -> FStar_Parser_Dep.deps =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
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
           (fun uu___171_5059  ->
              match uu___171_5059 with
              | Binding_var x ->
                  let y =
                    let uu____5062 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____5062 in
                  let uu____5063 =
                    let uu____5064 = FStar_Syntax_Subst.compress y in
                    uu____5064.FStar_Syntax_Syntax.n in
                  (match uu____5063 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____5068 =
                         let uu___185_5069 = y1 in
                         let uu____5070 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___185_5069.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___185_5069.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____5070
                         } in
                       Binding_var uu____5068
                   | uu____5073 -> failwith "Not a renaming")
              | b -> b))
let rename_env: FStar_Syntax_Syntax.subst_t -> env -> env =
  fun subst1  ->
    fun env  ->
      let uu___186_5081 = env in
      let uu____5082 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___186_5081.solver);
        range = (uu___186_5081.range);
        curmodule = (uu___186_5081.curmodule);
        gamma = uu____5082;
        gamma_cache = (uu___186_5081.gamma_cache);
        modules = (uu___186_5081.modules);
        expected_typ = (uu___186_5081.expected_typ);
        sigtab = (uu___186_5081.sigtab);
        is_pattern = (uu___186_5081.is_pattern);
        instantiate_imp = (uu___186_5081.instantiate_imp);
        effects = (uu___186_5081.effects);
        generalize = (uu___186_5081.generalize);
        letrecs = (uu___186_5081.letrecs);
        top_level = (uu___186_5081.top_level);
        check_uvars = (uu___186_5081.check_uvars);
        use_eq = (uu___186_5081.use_eq);
        is_iface = (uu___186_5081.is_iface);
        admit = (uu___186_5081.admit);
        lax = (uu___186_5081.lax);
        lax_universes = (uu___186_5081.lax_universes);
        failhard = (uu___186_5081.failhard);
        nosynth = (uu___186_5081.nosynth);
        tc_term = (uu___186_5081.tc_term);
        type_of = (uu___186_5081.type_of);
        universe_of = (uu___186_5081.universe_of);
        use_bv_sorts = (uu___186_5081.use_bv_sorts);
        qname_and_index = (uu___186_5081.qname_and_index);
        proof_ns = (uu___186_5081.proof_ns);
        synth = (uu___186_5081.synth);
        is_native_tactic = (uu___186_5081.is_native_tactic);
        identifier_info = (uu___186_5081.identifier_info);
        tc_hooks = (uu___186_5081.tc_hooks);
        dsenv = (uu___186_5081.dsenv);
        dep_graph = (uu___186_5081.dep_graph)
      }
let default_tc_hooks: tcenv_hooks =
  { tc_push_in_gamma_hook = (fun uu____5089  -> fun uu____5090  -> ()) }
let tc_hooks: env -> tcenv_hooks = fun env  -> env.tc_hooks
let set_tc_hooks: env -> tcenv_hooks -> env =
  fun env  ->
    fun hooks  ->
      let uu___187_5100 = env in
      {
        solver = (uu___187_5100.solver);
        range = (uu___187_5100.range);
        curmodule = (uu___187_5100.curmodule);
        gamma = (uu___187_5100.gamma);
        gamma_cache = (uu___187_5100.gamma_cache);
        modules = (uu___187_5100.modules);
        expected_typ = (uu___187_5100.expected_typ);
        sigtab = (uu___187_5100.sigtab);
        is_pattern = (uu___187_5100.is_pattern);
        instantiate_imp = (uu___187_5100.instantiate_imp);
        effects = (uu___187_5100.effects);
        generalize = (uu___187_5100.generalize);
        letrecs = (uu___187_5100.letrecs);
        top_level = (uu___187_5100.top_level);
        check_uvars = (uu___187_5100.check_uvars);
        use_eq = (uu___187_5100.use_eq);
        is_iface = (uu___187_5100.is_iface);
        admit = (uu___187_5100.admit);
        lax = (uu___187_5100.lax);
        lax_universes = (uu___187_5100.lax_universes);
        failhard = (uu___187_5100.failhard);
        nosynth = (uu___187_5100.nosynth);
        tc_term = (uu___187_5100.tc_term);
        type_of = (uu___187_5100.type_of);
        universe_of = (uu___187_5100.universe_of);
        use_bv_sorts = (uu___187_5100.use_bv_sorts);
        qname_and_index = (uu___187_5100.qname_and_index);
        proof_ns = (uu___187_5100.proof_ns);
        synth = (uu___187_5100.synth);
        is_native_tactic = (uu___187_5100.is_native_tactic);
        identifier_info = (uu___187_5100.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___187_5100.dsenv);
        dep_graph = (uu___187_5100.dep_graph)
      }
let set_dep_graph: env -> FStar_Parser_Dep.deps -> env =
  fun e  ->
    fun g  ->
      let uu___188_5107 = e in
      {
        solver = (uu___188_5107.solver);
        range = (uu___188_5107.range);
        curmodule = (uu___188_5107.curmodule);
        gamma = (uu___188_5107.gamma);
        gamma_cache = (uu___188_5107.gamma_cache);
        modules = (uu___188_5107.modules);
        expected_typ = (uu___188_5107.expected_typ);
        sigtab = (uu___188_5107.sigtab);
        is_pattern = (uu___188_5107.is_pattern);
        instantiate_imp = (uu___188_5107.instantiate_imp);
        effects = (uu___188_5107.effects);
        generalize = (uu___188_5107.generalize);
        letrecs = (uu___188_5107.letrecs);
        top_level = (uu___188_5107.top_level);
        check_uvars = (uu___188_5107.check_uvars);
        use_eq = (uu___188_5107.use_eq);
        is_iface = (uu___188_5107.is_iface);
        admit = (uu___188_5107.admit);
        lax = (uu___188_5107.lax);
        lax_universes = (uu___188_5107.lax_universes);
        failhard = (uu___188_5107.failhard);
        nosynth = (uu___188_5107.nosynth);
        tc_term = (uu___188_5107.tc_term);
        type_of = (uu___188_5107.type_of);
        universe_of = (uu___188_5107.universe_of);
        use_bv_sorts = (uu___188_5107.use_bv_sorts);
        qname_and_index = (uu___188_5107.qname_and_index);
        proof_ns = (uu___188_5107.proof_ns);
        synth = (uu___188_5107.synth);
        is_native_tactic = (uu___188_5107.is_native_tactic);
        identifier_info = (uu___188_5107.identifier_info);
        tc_hooks = (uu___188_5107.tc_hooks);
        dsenv = (uu___188_5107.dsenv);
        dep_graph = g
      }
let dep_graph: env -> FStar_Parser_Dep.deps = fun e  -> e.dep_graph
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
      | (NoDelta ,uu____5122) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____5123,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____5124,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____5125 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab: 'Auu____5132 . Prims.unit -> 'Auu____5132 FStar_Util.smap =
  fun uu____5138  -> FStar_Util.smap_create default_table_size
let new_gamma_cache:
  'Auu____5141 . Prims.unit -> 'Auu____5141 FStar_Util.smap =
  fun uu____5147  -> FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  FStar_Parser_Dep.deps ->
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
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun solver  ->
            fun module_lid  ->
              let uu____5220 = new_gamma_cache () in
              let uu____5223 = new_sigtab () in
              let uu____5226 = FStar_Options.using_facts_from () in
              let uu____5227 =
                FStar_Util.mk_ref
                  FStar_TypeChecker_Common.id_info_table_empty in
              let uu____5230 = FStar_ToSyntax_Env.empty_env () in
              {
                solver;
                range = FStar_Range.dummyRange;
                curmodule = module_lid;
                gamma = [];
                gamma_cache = uu____5220;
                modules = [];
                expected_typ = FStar_Pervasives_Native.None;
                sigtab = uu____5223;
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
                proof_ns = uu____5226;
                synth =
                  (fun e  ->
                     fun g  ->
                       fun tau  -> failwith "no synthesizer available");
                is_native_tactic = (fun uu____5264  -> false);
                identifier_info = uu____5227;
                tc_hooks = default_tc_hooks;
                dsenv = uu____5230;
                dep_graph = deps
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
  fun uu____5332  ->
    let uu____5333 = FStar_ST.op_Bang query_indices in
    match uu____5333 with
    | [] -> failwith "Empty query indices!"
    | uu____5410 ->
        let uu____5419 =
          let uu____5428 =
            let uu____5435 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____5435 in
          let uu____5512 = FStar_ST.op_Bang query_indices in uu____5428 ::
            uu____5512 in
        FStar_ST.op_Colon_Equals query_indices uu____5419
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____5653  ->
    let uu____5654 = FStar_ST.op_Bang query_indices in
    match uu____5654 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____5821  ->
    match uu____5821 with
    | (l,n1) ->
        let uu____5828 = FStar_ST.op_Bang query_indices in
        (match uu____5828 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____5993 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____6010  ->
    let uu____6011 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____6011
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____6105 =
       let uu____6108 = FStar_ST.op_Bang stack in env :: uu____6108 in
     FStar_ST.op_Colon_Equals stack uu____6105);
    (let uu___189_6211 = env in
     let uu____6212 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____6215 = FStar_Util.smap_copy (sigtab env) in
     let uu____6218 =
       let uu____6221 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____6221 in
     {
       solver = (uu___189_6211.solver);
       range = (uu___189_6211.range);
       curmodule = (uu___189_6211.curmodule);
       gamma = (uu___189_6211.gamma);
       gamma_cache = uu____6212;
       modules = (uu___189_6211.modules);
       expected_typ = (uu___189_6211.expected_typ);
       sigtab = uu____6215;
       is_pattern = (uu___189_6211.is_pattern);
       instantiate_imp = (uu___189_6211.instantiate_imp);
       effects = (uu___189_6211.effects);
       generalize = (uu___189_6211.generalize);
       letrecs = (uu___189_6211.letrecs);
       top_level = (uu___189_6211.top_level);
       check_uvars = (uu___189_6211.check_uvars);
       use_eq = (uu___189_6211.use_eq);
       is_iface = (uu___189_6211.is_iface);
       admit = (uu___189_6211.admit);
       lax = (uu___189_6211.lax);
       lax_universes = (uu___189_6211.lax_universes);
       failhard = (uu___189_6211.failhard);
       nosynth = (uu___189_6211.nosynth);
       tc_term = (uu___189_6211.tc_term);
       type_of = (uu___189_6211.type_of);
       universe_of = (uu___189_6211.universe_of);
       use_bv_sorts = (uu___189_6211.use_bv_sorts);
       qname_and_index = (uu___189_6211.qname_and_index);
       proof_ns = (uu___189_6211.proof_ns);
       synth = (uu___189_6211.synth);
       is_native_tactic = (uu___189_6211.is_native_tactic);
       identifier_info = uu____6218;
       tc_hooks = (uu___189_6211.tc_hooks);
       dsenv = (uu___189_6211.dsenv);
       dep_graph = (uu___189_6211.dep_graph)
     })
let pop_stack: Prims.unit -> env =
  fun uu____6284  ->
    let uu____6285 = FStar_ST.op_Bang stack in
    match uu____6285 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____6393 -> failwith "Impossible: Too many pops"
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
        let uu____6432 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____6458  ->
                  match uu____6458 with
                  | (m,uu____6464) -> FStar_Ident.lid_equals l m)) in
        (match uu____6432 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___190_6471 = env in
               {
                 solver = (uu___190_6471.solver);
                 range = (uu___190_6471.range);
                 curmodule = (uu___190_6471.curmodule);
                 gamma = (uu___190_6471.gamma);
                 gamma_cache = (uu___190_6471.gamma_cache);
                 modules = (uu___190_6471.modules);
                 expected_typ = (uu___190_6471.expected_typ);
                 sigtab = (uu___190_6471.sigtab);
                 is_pattern = (uu___190_6471.is_pattern);
                 instantiate_imp = (uu___190_6471.instantiate_imp);
                 effects = (uu___190_6471.effects);
                 generalize = (uu___190_6471.generalize);
                 letrecs = (uu___190_6471.letrecs);
                 top_level = (uu___190_6471.top_level);
                 check_uvars = (uu___190_6471.check_uvars);
                 use_eq = (uu___190_6471.use_eq);
                 is_iface = (uu___190_6471.is_iface);
                 admit = (uu___190_6471.admit);
                 lax = (uu___190_6471.lax);
                 lax_universes = (uu___190_6471.lax_universes);
                 failhard = (uu___190_6471.failhard);
                 nosynth = (uu___190_6471.nosynth);
                 tc_term = (uu___190_6471.tc_term);
                 type_of = (uu___190_6471.type_of);
                 universe_of = (uu___190_6471.universe_of);
                 use_bv_sorts = (uu___190_6471.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___190_6471.proof_ns);
                 synth = (uu___190_6471.synth);
                 is_native_tactic = (uu___190_6471.is_native_tactic);
                 identifier_info = (uu___190_6471.identifier_info);
                 tc_hooks = (uu___190_6471.tc_hooks);
                 dsenv = (uu___190_6471.dsenv);
                 dep_graph = (uu___190_6471.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____6476,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___191_6484 = env in
               {
                 solver = (uu___191_6484.solver);
                 range = (uu___191_6484.range);
                 curmodule = (uu___191_6484.curmodule);
                 gamma = (uu___191_6484.gamma);
                 gamma_cache = (uu___191_6484.gamma_cache);
                 modules = (uu___191_6484.modules);
                 expected_typ = (uu___191_6484.expected_typ);
                 sigtab = (uu___191_6484.sigtab);
                 is_pattern = (uu___191_6484.is_pattern);
                 instantiate_imp = (uu___191_6484.instantiate_imp);
                 effects = (uu___191_6484.effects);
                 generalize = (uu___191_6484.generalize);
                 letrecs = (uu___191_6484.letrecs);
                 top_level = (uu___191_6484.top_level);
                 check_uvars = (uu___191_6484.check_uvars);
                 use_eq = (uu___191_6484.use_eq);
                 is_iface = (uu___191_6484.is_iface);
                 admit = (uu___191_6484.admit);
                 lax = (uu___191_6484.lax);
                 lax_universes = (uu___191_6484.lax_universes);
                 failhard = (uu___191_6484.failhard);
                 nosynth = (uu___191_6484.nosynth);
                 tc_term = (uu___191_6484.tc_term);
                 type_of = (uu___191_6484.type_of);
                 universe_of = (uu___191_6484.universe_of);
                 use_bv_sorts = (uu___191_6484.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next));
                 proof_ns = (uu___191_6484.proof_ns);
                 synth = (uu___191_6484.synth);
                 is_native_tactic = (uu___191_6484.is_native_tactic);
                 identifier_info = (uu___191_6484.identifier_info);
                 tc_hooks = (uu___191_6484.tc_hooks);
                 dsenv = (uu___191_6484.dsenv);
                 dep_graph = (uu___191_6484.dep_graph)
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
        (let uu___192_6502 = e in
         {
           solver = (uu___192_6502.solver);
           range = r;
           curmodule = (uu___192_6502.curmodule);
           gamma = (uu___192_6502.gamma);
           gamma_cache = (uu___192_6502.gamma_cache);
           modules = (uu___192_6502.modules);
           expected_typ = (uu___192_6502.expected_typ);
           sigtab = (uu___192_6502.sigtab);
           is_pattern = (uu___192_6502.is_pattern);
           instantiate_imp = (uu___192_6502.instantiate_imp);
           effects = (uu___192_6502.effects);
           generalize = (uu___192_6502.generalize);
           letrecs = (uu___192_6502.letrecs);
           top_level = (uu___192_6502.top_level);
           check_uvars = (uu___192_6502.check_uvars);
           use_eq = (uu___192_6502.use_eq);
           is_iface = (uu___192_6502.is_iface);
           admit = (uu___192_6502.admit);
           lax = (uu___192_6502.lax);
           lax_universes = (uu___192_6502.lax_universes);
           failhard = (uu___192_6502.failhard);
           nosynth = (uu___192_6502.nosynth);
           tc_term = (uu___192_6502.tc_term);
           type_of = (uu___192_6502.type_of);
           universe_of = (uu___192_6502.universe_of);
           use_bv_sorts = (uu___192_6502.use_bv_sorts);
           qname_and_index = (uu___192_6502.qname_and_index);
           proof_ns = (uu___192_6502.proof_ns);
           synth = (uu___192_6502.synth);
           is_native_tactic = (uu___192_6502.is_native_tactic);
           identifier_info = (uu___192_6502.identifier_info);
           tc_hooks = (uu___192_6502.tc_hooks);
           dsenv = (uu___192_6502.dsenv);
           dep_graph = (uu___192_6502.dep_graph)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let toggle_id_info: env -> Prims.bool -> Prims.unit =
  fun env  ->
    fun enabled  ->
      let uu____6512 =
        let uu____6513 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____6513 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6512
let insert_bv_info:
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____6615 =
          let uu____6616 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____6616 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6615
let insert_fv_info:
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> Prims.unit =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____6718 =
          let uu____6719 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____6719 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____6718
let promote_id_info:
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> Prims.unit =
  fun env  ->
    fun ty_map  ->
      let uu____6823 =
        let uu____6824 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____6824 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____6823
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___193_6931 = env in
      {
        solver = (uu___193_6931.solver);
        range = (uu___193_6931.range);
        curmodule = lid;
        gamma = (uu___193_6931.gamma);
        gamma_cache = (uu___193_6931.gamma_cache);
        modules = (uu___193_6931.modules);
        expected_typ = (uu___193_6931.expected_typ);
        sigtab = (uu___193_6931.sigtab);
        is_pattern = (uu___193_6931.is_pattern);
        instantiate_imp = (uu___193_6931.instantiate_imp);
        effects = (uu___193_6931.effects);
        generalize = (uu___193_6931.generalize);
        letrecs = (uu___193_6931.letrecs);
        top_level = (uu___193_6931.top_level);
        check_uvars = (uu___193_6931.check_uvars);
        use_eq = (uu___193_6931.use_eq);
        is_iface = (uu___193_6931.is_iface);
        admit = (uu___193_6931.admit);
        lax = (uu___193_6931.lax);
        lax_universes = (uu___193_6931.lax_universes);
        failhard = (uu___193_6931.failhard);
        nosynth = (uu___193_6931.nosynth);
        tc_term = (uu___193_6931.tc_term);
        type_of = (uu___193_6931.type_of);
        universe_of = (uu___193_6931.universe_of);
        use_bv_sorts = (uu___193_6931.use_bv_sorts);
        qname_and_index = (uu___193_6931.qname_and_index);
        proof_ns = (uu___193_6931.proof_ns);
        synth = (uu___193_6931.synth);
        is_native_tactic = (uu___193_6931.is_native_tactic);
        identifier_info = (uu___193_6931.identifier_info);
        tc_hooks = (uu___193_6931.tc_hooks);
        dsenv = (uu___193_6931.dsenv);
        dep_graph = (uu___193_6931.dep_graph)
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
    let uu____6956 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____6956
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____6959  ->
    let uu____6960 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____6960
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
      | ((formals,t),uu____6998) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____7022 = FStar_Syntax_Subst.subst vs t in (us, uu____7022)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___172_7035  ->
    match uu___172_7035 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____7059  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____7072 = inst_tscheme t in
      match uu____7072 with
      | (us,t1) ->
          let uu____7083 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____7083)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____7095  ->
          match uu____7095 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____7110 =
                         let uu____7111 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____7112 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____7113 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____7114 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____7111 uu____7112 uu____7113 uu____7114 in
                       failwith uu____7110)
                    else ();
                    (let uu____7116 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____7116))
               | uu____7123 ->
                   let uu____7124 =
                     let uu____7125 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____7125 in
                   failwith uu____7124)
type tri =
  | Yes
  | No
  | Maybe[@@deriving show]
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____7129 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____7133 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____7137 -> false
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
             | ([],uu____7171) -> Maybe
             | (uu____7178,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____7197 -> No in
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
          let uu____7302 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____7302 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___173_7347  ->
                   match uu___173_7347 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____7390 =
                           let uu____7409 =
                             let uu____7424 = inst_tscheme t in
                             FStar_Util.Inl uu____7424 in
                           (uu____7409, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____7390
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____7490,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____7492);
                                     FStar_Syntax_Syntax.sigrng = uu____7493;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____7494;
                                     FStar_Syntax_Syntax.sigmeta = uu____7495;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____7496;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____7516 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____7516
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____7562 ->
                             FStar_Pervasives_Native.Some t
                         | uu____7569 -> cache t in
                       let uu____7570 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7570 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____7645 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____7645 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____7731 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____7811 = find_in_sigtab env lid in
         match uu____7811 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____7910) ->
          add_sigelts env ses
      | uu____7919 ->
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
            | uu____7933 -> ()))
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
        (fun uu___174_7960  ->
           match uu___174_7960 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____7978 -> FStar_Pervasives_Native.None)
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
      | FStar_Syntax_Syntax.Sig_let ((uu____8011,lb::[]),uu____8013) ->
          let uu____8026 =
            let uu____8035 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____8044 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____8035, uu____8044) in
          FStar_Pervasives_Native.Some uu____8026
      | FStar_Syntax_Syntax.Sig_let ((uu____8057,lbs),uu____8059) ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____8095 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____8107 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____8107
                   then
                     let uu____8118 =
                       let uu____8127 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____8136 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____8127, uu____8136) in
                     FStar_Pervasives_Native.Some uu____8118
                   else FStar_Pervasives_Native.None)
      | uu____8158 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____8191 =
          let uu____8200 =
            let uu____8205 =
              let uu____8206 =
                let uu____8209 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____8209 in
              ((ne.FStar_Syntax_Syntax.univs), uu____8206) in
            inst_tscheme uu____8205 in
          (uu____8200, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8191
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____8229,uu____8230) ->
        let uu____8235 =
          let uu____8244 =
            let uu____8249 =
              let uu____8250 =
                let uu____8253 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____8253 in
              (us, uu____8250) in
            inst_tscheme uu____8249 in
          (uu____8244, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____8235
    | uu____8270 -> FStar_Pervasives_Native.None
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
      let mapper uu____8328 =
        match uu____8328 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____8424,uvs,t,uu____8427,uu____8428,uu____8429);
                    FStar_Syntax_Syntax.sigrng = uu____8430;
                    FStar_Syntax_Syntax.sigquals = uu____8431;
                    FStar_Syntax_Syntax.sigmeta = uu____8432;
                    FStar_Syntax_Syntax.sigattrs = uu____8433;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8454 =
                   let uu____8463 = inst_tscheme (uvs, t) in
                   (uu____8463, rng) in
                 FStar_Pervasives_Native.Some uu____8454
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____8483;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____8485;
                    FStar_Syntax_Syntax.sigattrs = uu____8486;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____8503 =
                   let uu____8504 = in_cur_mod env l in uu____8504 = Yes in
                 if uu____8503
                 then
                   let uu____8515 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____8515
                    then
                      let uu____8528 =
                        let uu____8537 = inst_tscheme (uvs, t) in
                        (uu____8537, rng) in
                      FStar_Pervasives_Native.Some uu____8528
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____8564 =
                      let uu____8573 = inst_tscheme (uvs, t) in
                      (uu____8573, rng) in
                    FStar_Pervasives_Native.Some uu____8564)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8594,uu____8595);
                    FStar_Syntax_Syntax.sigrng = uu____8596;
                    FStar_Syntax_Syntax.sigquals = uu____8597;
                    FStar_Syntax_Syntax.sigmeta = uu____8598;
                    FStar_Syntax_Syntax.sigattrs = uu____8599;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____8638 =
                        let uu____8647 = inst_tscheme (uvs, k) in
                        (uu____8647, rng) in
                      FStar_Pervasives_Native.Some uu____8638
                  | uu____8664 ->
                      let uu____8665 =
                        let uu____8674 =
                          let uu____8679 =
                            let uu____8680 =
                              let uu____8683 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8683 in
                            (uvs, uu____8680) in
                          inst_tscheme uu____8679 in
                        (uu____8674, rng) in
                      FStar_Pervasives_Native.Some uu____8665)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____8704,uu____8705);
                    FStar_Syntax_Syntax.sigrng = uu____8706;
                    FStar_Syntax_Syntax.sigquals = uu____8707;
                    FStar_Syntax_Syntax.sigmeta = uu____8708;
                    FStar_Syntax_Syntax.sigattrs = uu____8709;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____8749 =
                        let uu____8758 = inst_tscheme_with (uvs, k) us in
                        (uu____8758, rng) in
                      FStar_Pervasives_Native.Some uu____8749
                  | uu____8775 ->
                      let uu____8776 =
                        let uu____8785 =
                          let uu____8790 =
                            let uu____8791 =
                              let uu____8794 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____8794 in
                            (uvs, uu____8791) in
                          inst_tscheme_with uu____8790 us in
                        (uu____8785, rng) in
                      FStar_Pervasives_Native.Some uu____8776)
             | FStar_Util.Inr se ->
                 let uu____8828 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____8849;
                        FStar_Syntax_Syntax.sigrng = uu____8850;
                        FStar_Syntax_Syntax.sigquals = uu____8851;
                        FStar_Syntax_Syntax.sigmeta = uu____8852;
                        FStar_Syntax_Syntax.sigattrs = uu____8853;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____8868 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____8828
                   (FStar_Util.map_option
                      (fun uu____8916  ->
                         match uu____8916 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____8947 =
        let uu____8958 = lookup_qname env lid in
        FStar_Util.bind_opt uu____8958 mapper in
      match uu____8947 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___194_9051 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___194_9051.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___194_9051.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____9076 = lookup_qname env l in
      match uu____9076 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____9115 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____9163 = try_lookup_bv env bv in
      match uu____9163 with
      | FStar_Pervasives_Native.None  ->
          let uu____9178 =
            let uu____9179 =
              let uu____9184 = variable_not_found bv in (uu____9184, bvr) in
            FStar_Errors.Error uu____9179 in
          FStar_Exn.raise uu____9178
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____9195 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____9196 =
            let uu____9197 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____9197 in
          (uu____9195, uu____9196)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____9214 = try_lookup_lid_aux env l in
      match uu____9214 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____9280 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____9280 in
          let uu____9281 =
            let uu____9290 =
              let uu____9295 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____9295) in
            (uu____9290, r1) in
          FStar_Pervasives_Native.Some uu____9281
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____9322 = try_lookup_lid env l in
      match uu____9322 with
      | FStar_Pervasives_Native.None  ->
          let uu____9349 =
            let uu____9350 =
              let uu____9355 = name_not_found l in
              (uu____9355, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____9350 in
          FStar_Exn.raise uu____9349
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___175_9391  ->
              match uu___175_9391 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____9393 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____9408 = lookup_qname env lid in
      match uu____9408 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9437,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9440;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____9442;
              FStar_Syntax_Syntax.sigattrs = uu____9443;_},FStar_Pervasives_Native.None
            ),uu____9444)
          ->
          let uu____9493 =
            let uu____9504 =
              let uu____9509 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____9509) in
            (uu____9504, q) in
          FStar_Pervasives_Native.Some uu____9493
      | uu____9526 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9563 = lookup_qname env lid in
      match uu____9563 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____9588,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____9591;
              FStar_Syntax_Syntax.sigquals = uu____9592;
              FStar_Syntax_Syntax.sigmeta = uu____9593;
              FStar_Syntax_Syntax.sigattrs = uu____9594;_},FStar_Pervasives_Native.None
            ),uu____9595)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9644 ->
          let uu____9665 =
            let uu____9666 =
              let uu____9671 = name_not_found lid in
              (uu____9671, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9666 in
          FStar_Exn.raise uu____9665
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9686 = lookup_qname env lid in
      match uu____9686 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9711,uvs,t,uu____9714,uu____9715,uu____9716);
              FStar_Syntax_Syntax.sigrng = uu____9717;
              FStar_Syntax_Syntax.sigquals = uu____9718;
              FStar_Syntax_Syntax.sigmeta = uu____9719;
              FStar_Syntax_Syntax.sigattrs = uu____9720;_},FStar_Pervasives_Native.None
            ),uu____9721)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____9774 ->
          let uu____9795 =
            let uu____9796 =
              let uu____9801 = name_not_found lid in
              (uu____9801, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____9796 in
          FStar_Exn.raise uu____9795
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____9818 = lookup_qname env lid in
      match uu____9818 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____9845,uu____9846,uu____9847,uu____9848,uu____9849,dcs);
              FStar_Syntax_Syntax.sigrng = uu____9851;
              FStar_Syntax_Syntax.sigquals = uu____9852;
              FStar_Syntax_Syntax.sigmeta = uu____9853;
              FStar_Syntax_Syntax.sigattrs = uu____9854;_},uu____9855),uu____9856)
          -> (true, dcs)
      | uu____9917 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____9946 = lookup_qname env lid in
      match uu____9946 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____9967,uu____9968,uu____9969,l,uu____9971,uu____9972);
              FStar_Syntax_Syntax.sigrng = uu____9973;
              FStar_Syntax_Syntax.sigquals = uu____9974;
              FStar_Syntax_Syntax.sigmeta = uu____9975;
              FStar_Syntax_Syntax.sigattrs = uu____9976;_},uu____9977),uu____9978)
          -> l
      | uu____10033 ->
          let uu____10054 =
            let uu____10055 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____10055 in
          failwith uu____10054
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
        let uu____10089 = lookup_qname env lid in
        match uu____10089 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10117)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____10168,lbs),uu____10170)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____10198 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____10198
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____10230 -> FStar_Pervasives_Native.None)
        | uu____10235 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____10270 = lookup_qname env ftv in
      match uu____10270 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____10294) ->
          let uu____10339 = effect_signature se in
          (match uu____10339 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____10360,t),r) ->
               let uu____10375 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____10375)
      | uu____10376 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ftv  ->
      let uu____10403 = try_lookup_effect_lid env ftv in
      match uu____10403 with
      | FStar_Pervasives_Native.None  ->
          let uu____10406 =
            let uu____10407 =
              let uu____10412 = name_not_found ftv in
              (uu____10412, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____10407 in
          FStar_Exn.raise uu____10406
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
        let uu____10429 = lookup_qname env lid0 in
        match uu____10429 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____10460);
                FStar_Syntax_Syntax.sigrng = uu____10461;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____10463;
                FStar_Syntax_Syntax.sigattrs = uu____10464;_},FStar_Pervasives_Native.None
              ),uu____10465)
            ->
            let lid1 =
              let uu____10519 =
                let uu____10520 =
                  FStar_Range.use_range (FStar_Ident.range_of_lid lid0) in
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  uu____10520 in
              FStar_Ident.set_lid_range lid uu____10519 in
            let uu____10521 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___176_10525  ->
                      match uu___176_10525 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____10526 -> false)) in
            if uu____10521
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____10540 =
                      let uu____10541 =
                        let uu____10542 = get_range env in
                        FStar_Range.string_of_range uu____10542 in
                      let uu____10543 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____10544 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____10541 uu____10543 uu____10544 in
                    failwith uu____10540) in
               match (binders, univs1) with
               | ([],uu____10551) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____10568,uu____10569::uu____10570::uu____10571) ->
                   let uu____10576 =
                     let uu____10577 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____10578 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____10577 uu____10578 in
                   failwith uu____10576
               | uu____10585 ->
                   let uu____10590 =
                     let uu____10595 =
                       let uu____10596 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____10596) in
                     inst_tscheme_with uu____10595 insts in
                   (match uu____10590 with
                    | (uu____10607,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____10610 =
                          let uu____10611 = FStar_Syntax_Subst.compress t1 in
                          uu____10611.FStar_Syntax_Syntax.n in
                        (match uu____10610 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____10658 -> failwith "Impossible")))
        | uu____10665 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____10705 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____10705 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____10718,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____10725 = find1 l2 in
            (match uu____10725 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____10732 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____10732 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____10736 = find1 l in
            (match uu____10736 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____10750 = lookup_qname env l1 in
      match uu____10750 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____10773;
              FStar_Syntax_Syntax.sigrng = uu____10774;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____10776;
              FStar_Syntax_Syntax.sigattrs = uu____10777;_},uu____10778),uu____10779)
          -> q
      | uu____10830 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____10863 =
          let uu____10864 =
            let uu____10865 = FStar_Util.string_of_int i in
            let uu____10866 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____10865 uu____10866 in
          failwith uu____10864 in
        let uu____10867 = lookup_datacon env lid in
        match uu____10867 with
        | (uu____10872,t) ->
            let uu____10874 =
              let uu____10875 = FStar_Syntax_Subst.compress t in
              uu____10875.FStar_Syntax_Syntax.n in
            (match uu____10874 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10879) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____10910 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____10910
                      FStar_Pervasives_Native.fst)
             | uu____10919 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____10926 = lookup_qname env l in
      match uu____10926 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____10947,uu____10948,uu____10949);
              FStar_Syntax_Syntax.sigrng = uu____10950;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____10952;
              FStar_Syntax_Syntax.sigattrs = uu____10953;_},uu____10954),uu____10955)
          ->
          FStar_Util.for_some
            (fun uu___177_11008  ->
               match uu___177_11008 with
               | FStar_Syntax_Syntax.Projector uu____11009 -> true
               | uu____11014 -> false) quals
      | uu____11015 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11042 = lookup_qname env lid in
      match uu____11042 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11063,uu____11064,uu____11065,uu____11066,uu____11067,uu____11068);
              FStar_Syntax_Syntax.sigrng = uu____11069;
              FStar_Syntax_Syntax.sigquals = uu____11070;
              FStar_Syntax_Syntax.sigmeta = uu____11071;
              FStar_Syntax_Syntax.sigattrs = uu____11072;_},uu____11073),uu____11074)
          -> true
      | uu____11129 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11156 = lookup_qname env lid in
      match uu____11156 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11177,uu____11178,uu____11179,uu____11180,uu____11181,uu____11182);
              FStar_Syntax_Syntax.sigrng = uu____11183;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11185;
              FStar_Syntax_Syntax.sigattrs = uu____11186;_},uu____11187),uu____11188)
          ->
          FStar_Util.for_some
            (fun uu___178_11249  ->
               match uu___178_11249 with
               | FStar_Syntax_Syntax.RecordType uu____11250 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____11259 -> true
               | uu____11268 -> false) quals
      | uu____11269 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____11296 = lookup_qname env lid in
      match uu____11296 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____11317,uu____11318);
              FStar_Syntax_Syntax.sigrng = uu____11319;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____11321;
              FStar_Syntax_Syntax.sigattrs = uu____11322;_},uu____11323),uu____11324)
          ->
          FStar_Util.for_some
            (fun uu___179_11381  ->
               match uu___179_11381 with
               | FStar_Syntax_Syntax.Action uu____11382 -> true
               | uu____11383 -> false) quals
      | uu____11384 -> false
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
      let uu____11414 =
        let uu____11415 = FStar_Syntax_Util.un_uinst head1 in
        uu____11415.FStar_Syntax_Syntax.n in
      match uu____11414 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____11419 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____11484 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____11500) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____11517 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____11524 ->
                 FStar_Pervasives_Native.Some true
             | uu____11541 -> FStar_Pervasives_Native.Some false) in
      let uu____11542 =
        let uu____11545 = lookup_qname env lid in
        FStar_Util.bind_opt uu____11545 mapper in
      match uu____11542 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____11591 = lookup_qname env lid in
      match uu____11591 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____11612,uu____11613,tps,uu____11615,uu____11616,uu____11617);
              FStar_Syntax_Syntax.sigrng = uu____11618;
              FStar_Syntax_Syntax.sigquals = uu____11619;
              FStar_Syntax_Syntax.sigmeta = uu____11620;
              FStar_Syntax_Syntax.sigattrs = uu____11621;_},uu____11622),uu____11623)
          -> FStar_List.length tps
      | uu____11686 ->
          let uu____11707 =
            let uu____11708 =
              let uu____11713 = name_not_found lid in
              (uu____11713, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____11708 in
          FStar_Exn.raise uu____11707
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
           (fun uu____11753  ->
              match uu____11753 with
              | (d,uu____11761) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____11772 = effect_decl_opt env l in
      match uu____11772 with
      | FStar_Pervasives_Native.None  ->
          let uu____11787 =
            let uu____11788 =
              let uu____11793 = name_not_found l in
              (uu____11793, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____11788 in
          FStar_Exn.raise uu____11787
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun uu____11815  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____11830  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
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
            (let uu____11863 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____11916  ->
                       match uu____11916 with
                       | (m1,m2,uu____11929,uu____11930,uu____11931) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____11863 with
             | FStar_Pervasives_Native.None  ->
                 let uu____11948 =
                   let uu____11949 =
                     let uu____11954 =
                       let uu____11955 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____11956 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____11955
                         uu____11956 in
                     (uu____11954, (env.range)) in
                   FStar_Errors.Error uu____11949 in
                 FStar_Exn.raise uu____11948
             | FStar_Pervasives_Native.Some
                 (uu____11963,uu____11964,m3,j1,j2) -> (m3, j1, j2))
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
  'Auu____12001 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____12001)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____12028 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____12054  ->
                match uu____12054 with
                | (d,uu____12060) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____12028 with
      | FStar_Pervasives_Native.None  ->
          let uu____12071 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____12071
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____12084 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____12084 with
           | (uu____12095,s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____12105)::(wp,uu____12107)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____12143 -> failwith "Impossible"))
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
                 let uu____12186 = get_range env in
                 let uu____12187 =
                   let uu____12190 =
                     let uu____12191 =
                       let uu____12206 =
                         let uu____12209 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____12209] in
                       (null_wp, uu____12206) in
                     FStar_Syntax_Syntax.Tm_app uu____12191 in
                   FStar_Syntax_Syntax.mk uu____12190 in
                 uu____12187 FStar_Pervasives_Native.None uu____12186 in
               let uu____12215 =
                 let uu____12216 =
                   let uu____12225 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____12225] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____12216;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____12215)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___195_12234 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___195_12234.order);
              joins = (uu___195_12234.joins)
            } in
          let uu___196_12243 = env in
          {
            solver = (uu___196_12243.solver);
            range = (uu___196_12243.range);
            curmodule = (uu___196_12243.curmodule);
            gamma = (uu___196_12243.gamma);
            gamma_cache = (uu___196_12243.gamma_cache);
            modules = (uu___196_12243.modules);
            expected_typ = (uu___196_12243.expected_typ);
            sigtab = (uu___196_12243.sigtab);
            is_pattern = (uu___196_12243.is_pattern);
            instantiate_imp = (uu___196_12243.instantiate_imp);
            effects;
            generalize = (uu___196_12243.generalize);
            letrecs = (uu___196_12243.letrecs);
            top_level = (uu___196_12243.top_level);
            check_uvars = (uu___196_12243.check_uvars);
            use_eq = (uu___196_12243.use_eq);
            is_iface = (uu___196_12243.is_iface);
            admit = (uu___196_12243.admit);
            lax = (uu___196_12243.lax);
            lax_universes = (uu___196_12243.lax_universes);
            failhard = (uu___196_12243.failhard);
            nosynth = (uu___196_12243.nosynth);
            tc_term = (uu___196_12243.tc_term);
            type_of = (uu___196_12243.type_of);
            universe_of = (uu___196_12243.universe_of);
            use_bv_sorts = (uu___196_12243.use_bv_sorts);
            qname_and_index = (uu___196_12243.qname_and_index);
            proof_ns = (uu___196_12243.proof_ns);
            synth = (uu___196_12243.synth);
            is_native_tactic = (uu___196_12243.is_native_tactic);
            identifier_info = (uu___196_12243.identifier_info);
            tc_hooks = (uu___196_12243.tc_hooks);
            dsenv = (uu___196_12243.dsenv);
            dep_graph = (uu___196_12243.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____12263 = (e1.mlift).mlift_wp u r wp1 in
                (e2.mlift).mlift_wp u r uu____12263 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____12377 = (e1.mlift).mlift_wp u t wp in
                                let uu____12378 = l1 u t wp e in
                                l2 u t uu____12377 uu____12378))
                | uu____12379 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____12427 = inst_tscheme_with lift_t [u] in
            match uu____12427 with
            | (uu____12434,lift_t1) ->
                let uu____12436 =
                  let uu____12439 =
                    let uu____12440 =
                      let uu____12455 =
                        let uu____12458 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12459 =
                          let uu____12462 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____12462] in
                        uu____12458 :: uu____12459 in
                      (lift_t1, uu____12455) in
                    FStar_Syntax_Syntax.Tm_app uu____12440 in
                  FStar_Syntax_Syntax.mk uu____12439 in
                uu____12436 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____12512 = inst_tscheme_with lift_t [u] in
            match uu____12512 with
            | (uu____12519,lift_t1) ->
                let uu____12521 =
                  let uu____12524 =
                    let uu____12525 =
                      let uu____12540 =
                        let uu____12543 = FStar_Syntax_Syntax.as_arg r in
                        let uu____12544 =
                          let uu____12547 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____12548 =
                            let uu____12551 = FStar_Syntax_Syntax.as_arg e in
                            [uu____12551] in
                          uu____12547 :: uu____12548 in
                        uu____12543 :: uu____12544 in
                      (lift_t1, uu____12540) in
                    FStar_Syntax_Syntax.Tm_app uu____12525 in
                  FStar_Syntax_Syntax.mk uu____12524 in
                uu____12521 FStar_Pervasives_Native.None
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
              let uu____12593 =
                let uu____12594 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____12594
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____12593 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____12598 =
              let uu____12599 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp in
              FStar_Syntax_Print.term_to_string uu____12599 in
            let uu____12600 =
              let uu____12601 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____12623 = l1 FStar_Syntax_Syntax.U_zero arg wp e in
                     FStar_Syntax_Print.term_to_string uu____12623) in
              FStar_Util.dflt "none" uu____12601 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12598
              uu____12600 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____12649  ->
                    match uu____12649 with
                    | (e,uu____12657) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____12676 =
            match uu____12676 with
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
              let uu____12714 =
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
                                    (let uu____12735 =
                                       let uu____12744 =
                                         find_edge order1 (i, k) in
                                       let uu____12747 =
                                         find_edge order1 (k, j) in
                                       (uu____12744, uu____12747) in
                                     match uu____12735 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____12762 =
                                           compose_edges e1 e2 in
                                         [uu____12762]
                                     | uu____12763 -> []))))) in
              FStar_List.append order1 uu____12714 in
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
                   let uu____12792 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____12794 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____12794
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____12792
                   then
                     let uu____12799 =
                       let uu____12800 =
                         let uu____12805 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____12806 = get_range env in
                         (uu____12805, uu____12806) in
                       FStar_Errors.Error uu____12800 in
                     FStar_Exn.raise uu____12799
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
                                            let uu____12931 =
                                              let uu____12940 =
                                                find_edge order2 (i, k) in
                                              let uu____12943 =
                                                find_edge order2 (j, k) in
                                              (uu____12940, uu____12943) in
                                            match uu____12931 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____12985,uu____12986)
                                                     ->
                                                     let uu____12993 =
                                                       let uu____12998 =
                                                         let uu____12999 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____12999 in
                                                       let uu____13002 =
                                                         let uu____13003 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____13003 in
                                                       (uu____12998,
                                                         uu____13002) in
                                                     (match uu____12993 with
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
                                            | uu____13038 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___197_13111 = env.effects in
              { decls = (uu___197_13111.decls); order = order2; joins } in
            let uu___198_13112 = env in
            {
              solver = (uu___198_13112.solver);
              range = (uu___198_13112.range);
              curmodule = (uu___198_13112.curmodule);
              gamma = (uu___198_13112.gamma);
              gamma_cache = (uu___198_13112.gamma_cache);
              modules = (uu___198_13112.modules);
              expected_typ = (uu___198_13112.expected_typ);
              sigtab = (uu___198_13112.sigtab);
              is_pattern = (uu___198_13112.is_pattern);
              instantiate_imp = (uu___198_13112.instantiate_imp);
              effects;
              generalize = (uu___198_13112.generalize);
              letrecs = (uu___198_13112.letrecs);
              top_level = (uu___198_13112.top_level);
              check_uvars = (uu___198_13112.check_uvars);
              use_eq = (uu___198_13112.use_eq);
              is_iface = (uu___198_13112.is_iface);
              admit = (uu___198_13112.admit);
              lax = (uu___198_13112.lax);
              lax_universes = (uu___198_13112.lax_universes);
              failhard = (uu___198_13112.failhard);
              nosynth = (uu___198_13112.nosynth);
              tc_term = (uu___198_13112.tc_term);
              type_of = (uu___198_13112.type_of);
              universe_of = (uu___198_13112.universe_of);
              use_bv_sorts = (uu___198_13112.use_bv_sorts);
              qname_and_index = (uu___198_13112.qname_and_index);
              proof_ns = (uu___198_13112.proof_ns);
              synth = (uu___198_13112.synth);
              is_native_tactic = (uu___198_13112.is_native_tactic);
              identifier_info = (uu___198_13112.identifier_info);
              tc_hooks = (uu___198_13112.tc_hooks);
              dsenv = (uu___198_13112.dsenv);
              dep_graph = (uu___198_13112.dep_graph)
            }))
      | uu____13113 -> env
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
        | uu____13137 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____13145 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____13145 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____13162 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____13162 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____13180 =
                     let uu____13181 =
                       let uu____13186 =
                         let uu____13187 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____13192 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____13199 =
                           let uu____13200 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____13200 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____13187 uu____13192 uu____13199 in
                       (uu____13186, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____13181 in
                   FStar_Exn.raise uu____13180)
                else ();
                (let inst1 =
                   let uu____13205 =
                     let uu____13214 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____13214 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____13231  ->
                        fun uu____13232  ->
                          match (uu____13231, uu____13232) with
                          | ((x,uu____13254),(t,uu____13256)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____13205 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____13275 =
                     let uu___199_13276 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___199_13276.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___199_13276.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___199_13276.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___199_13276.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____13275
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
          let uu____13298 = effect_decl_opt env effect_name in
          match uu____13298 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____13331 =
                only_reifiable &&
                  (let uu____13333 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____13333) in
              if uu____13331
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____13349 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____13368 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____13397 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____13397
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____13398 =
                             let uu____13399 =
                               let uu____13404 = get_range env in
                               (message, uu____13404) in
                             FStar_Errors.Error uu____13399 in
                           FStar_Exn.raise uu____13398 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____13414 =
                       let uu____13417 = get_range env in
                       let uu____13418 =
                         let uu____13421 =
                           let uu____13422 =
                             let uu____13437 =
                               let uu____13440 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____13440; wp] in
                             (repr, uu____13437) in
                           FStar_Syntax_Syntax.Tm_app uu____13422 in
                         FStar_Syntax_Syntax.mk uu____13421 in
                       uu____13418 FStar_Pervasives_Native.None uu____13417 in
                     FStar_Pervasives_Native.Some uu____13414)
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
          let uu____13486 =
            let uu____13487 =
              let uu____13492 =
                let uu____13493 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____13493 in
              let uu____13494 = get_range env in (uu____13492, uu____13494) in
            FStar_Errors.Error uu____13487 in
          FStar_Exn.raise uu____13486 in
        let uu____13495 = effect_repr_aux true env c u_c in
        match uu____13495 with
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
      | uu____13529 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____13536 =
        let uu____13537 = FStar_Syntax_Subst.compress t in
        uu____13537.FStar_Syntax_Syntax.n in
      match uu____13536 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____13540,c) ->
          is_reifiable_comp env c
      | uu____13558 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____13580)::uu____13581 -> x :: rest
        | (Binding_sig_inst uu____13590)::uu____13591 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____13606 = push1 x rest1 in local :: uu____13606 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___200_13610 = env in
       let uu____13611 = push1 s env.gamma in
       {
         solver = (uu___200_13610.solver);
         range = (uu___200_13610.range);
         curmodule = (uu___200_13610.curmodule);
         gamma = uu____13611;
         gamma_cache = (uu___200_13610.gamma_cache);
         modules = (uu___200_13610.modules);
         expected_typ = (uu___200_13610.expected_typ);
         sigtab = (uu___200_13610.sigtab);
         is_pattern = (uu___200_13610.is_pattern);
         instantiate_imp = (uu___200_13610.instantiate_imp);
         effects = (uu___200_13610.effects);
         generalize = (uu___200_13610.generalize);
         letrecs = (uu___200_13610.letrecs);
         top_level = (uu___200_13610.top_level);
         check_uvars = (uu___200_13610.check_uvars);
         use_eq = (uu___200_13610.use_eq);
         is_iface = (uu___200_13610.is_iface);
         admit = (uu___200_13610.admit);
         lax = (uu___200_13610.lax);
         lax_universes = (uu___200_13610.lax_universes);
         failhard = (uu___200_13610.failhard);
         nosynth = (uu___200_13610.nosynth);
         tc_term = (uu___200_13610.tc_term);
         type_of = (uu___200_13610.type_of);
         universe_of = (uu___200_13610.universe_of);
         use_bv_sorts = (uu___200_13610.use_bv_sorts);
         qname_and_index = (uu___200_13610.qname_and_index);
         proof_ns = (uu___200_13610.proof_ns);
         synth = (uu___200_13610.synth);
         is_native_tactic = (uu___200_13610.is_native_tactic);
         identifier_info = (uu___200_13610.identifier_info);
         tc_hooks = (uu___200_13610.tc_hooks);
         dsenv = (uu___200_13610.dsenv);
         dep_graph = (uu___200_13610.dep_graph)
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
      let uu___201_13641 = env in
      {
        solver = (uu___201_13641.solver);
        range = (uu___201_13641.range);
        curmodule = (uu___201_13641.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___201_13641.gamma_cache);
        modules = (uu___201_13641.modules);
        expected_typ = (uu___201_13641.expected_typ);
        sigtab = (uu___201_13641.sigtab);
        is_pattern = (uu___201_13641.is_pattern);
        instantiate_imp = (uu___201_13641.instantiate_imp);
        effects = (uu___201_13641.effects);
        generalize = (uu___201_13641.generalize);
        letrecs = (uu___201_13641.letrecs);
        top_level = (uu___201_13641.top_level);
        check_uvars = (uu___201_13641.check_uvars);
        use_eq = (uu___201_13641.use_eq);
        is_iface = (uu___201_13641.is_iface);
        admit = (uu___201_13641.admit);
        lax = (uu___201_13641.lax);
        lax_universes = (uu___201_13641.lax_universes);
        failhard = (uu___201_13641.failhard);
        nosynth = (uu___201_13641.nosynth);
        tc_term = (uu___201_13641.tc_term);
        type_of = (uu___201_13641.type_of);
        universe_of = (uu___201_13641.universe_of);
        use_bv_sorts = (uu___201_13641.use_bv_sorts);
        qname_and_index = (uu___201_13641.qname_and_index);
        proof_ns = (uu___201_13641.proof_ns);
        synth = (uu___201_13641.synth);
        is_native_tactic = (uu___201_13641.is_native_tactic);
        identifier_info = (uu___201_13641.identifier_info);
        tc_hooks = (uu___201_13641.tc_hooks);
        dsenv = (uu___201_13641.dsenv);
        dep_graph = (uu___201_13641.dep_graph)
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
            (let uu___202_13672 = env in
             {
               solver = (uu___202_13672.solver);
               range = (uu___202_13672.range);
               curmodule = (uu___202_13672.curmodule);
               gamma = rest;
               gamma_cache = (uu___202_13672.gamma_cache);
               modules = (uu___202_13672.modules);
               expected_typ = (uu___202_13672.expected_typ);
               sigtab = (uu___202_13672.sigtab);
               is_pattern = (uu___202_13672.is_pattern);
               instantiate_imp = (uu___202_13672.instantiate_imp);
               effects = (uu___202_13672.effects);
               generalize = (uu___202_13672.generalize);
               letrecs = (uu___202_13672.letrecs);
               top_level = (uu___202_13672.top_level);
               check_uvars = (uu___202_13672.check_uvars);
               use_eq = (uu___202_13672.use_eq);
               is_iface = (uu___202_13672.is_iface);
               admit = (uu___202_13672.admit);
               lax = (uu___202_13672.lax);
               lax_universes = (uu___202_13672.lax_universes);
               failhard = (uu___202_13672.failhard);
               nosynth = (uu___202_13672.nosynth);
               tc_term = (uu___202_13672.tc_term);
               type_of = (uu___202_13672.type_of);
               universe_of = (uu___202_13672.universe_of);
               use_bv_sorts = (uu___202_13672.use_bv_sorts);
               qname_and_index = (uu___202_13672.qname_and_index);
               proof_ns = (uu___202_13672.proof_ns);
               synth = (uu___202_13672.synth);
               is_native_tactic = (uu___202_13672.is_native_tactic);
               identifier_info = (uu___202_13672.identifier_info);
               tc_hooks = (uu___202_13672.tc_hooks);
               dsenv = (uu___202_13672.dsenv);
               dep_graph = (uu___202_13672.dep_graph)
             }))
    | uu____13673 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____13695  ->
             match uu____13695 with | (x,uu____13701) -> push_bv env1 x) env
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
            let uu___203_13729 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___203_13729.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___203_13729.FStar_Syntax_Syntax.index);
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
      (let uu___204_13759 = env in
       {
         solver = (uu___204_13759.solver);
         range = (uu___204_13759.range);
         curmodule = (uu___204_13759.curmodule);
         gamma = [];
         gamma_cache = (uu___204_13759.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___204_13759.sigtab);
         is_pattern = (uu___204_13759.is_pattern);
         instantiate_imp = (uu___204_13759.instantiate_imp);
         effects = (uu___204_13759.effects);
         generalize = (uu___204_13759.generalize);
         letrecs = (uu___204_13759.letrecs);
         top_level = (uu___204_13759.top_level);
         check_uvars = (uu___204_13759.check_uvars);
         use_eq = (uu___204_13759.use_eq);
         is_iface = (uu___204_13759.is_iface);
         admit = (uu___204_13759.admit);
         lax = (uu___204_13759.lax);
         lax_universes = (uu___204_13759.lax_universes);
         failhard = (uu___204_13759.failhard);
         nosynth = (uu___204_13759.nosynth);
         tc_term = (uu___204_13759.tc_term);
         type_of = (uu___204_13759.type_of);
         universe_of = (uu___204_13759.universe_of);
         use_bv_sorts = (uu___204_13759.use_bv_sorts);
         qname_and_index = (uu___204_13759.qname_and_index);
         proof_ns = (uu___204_13759.proof_ns);
         synth = (uu___204_13759.synth);
         is_native_tactic = (uu___204_13759.is_native_tactic);
         identifier_info = (uu___204_13759.identifier_info);
         tc_hooks = (uu___204_13759.tc_hooks);
         dsenv = (uu___204_13759.dsenv);
         dep_graph = (uu___204_13759.dep_graph)
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
        let uu____13791 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____13791 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____13819 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____13819)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___205_13832 = env in
      {
        solver = (uu___205_13832.solver);
        range = (uu___205_13832.range);
        curmodule = (uu___205_13832.curmodule);
        gamma = (uu___205_13832.gamma);
        gamma_cache = (uu___205_13832.gamma_cache);
        modules = (uu___205_13832.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___205_13832.sigtab);
        is_pattern = (uu___205_13832.is_pattern);
        instantiate_imp = (uu___205_13832.instantiate_imp);
        effects = (uu___205_13832.effects);
        generalize = (uu___205_13832.generalize);
        letrecs = (uu___205_13832.letrecs);
        top_level = (uu___205_13832.top_level);
        check_uvars = (uu___205_13832.check_uvars);
        use_eq = false;
        is_iface = (uu___205_13832.is_iface);
        admit = (uu___205_13832.admit);
        lax = (uu___205_13832.lax);
        lax_universes = (uu___205_13832.lax_universes);
        failhard = (uu___205_13832.failhard);
        nosynth = (uu___205_13832.nosynth);
        tc_term = (uu___205_13832.tc_term);
        type_of = (uu___205_13832.type_of);
        universe_of = (uu___205_13832.universe_of);
        use_bv_sorts = (uu___205_13832.use_bv_sorts);
        qname_and_index = (uu___205_13832.qname_and_index);
        proof_ns = (uu___205_13832.proof_ns);
        synth = (uu___205_13832.synth);
        is_native_tactic = (uu___205_13832.is_native_tactic);
        identifier_info = (uu___205_13832.identifier_info);
        tc_hooks = (uu___205_13832.tc_hooks);
        dsenv = (uu___205_13832.dsenv);
        dep_graph = (uu___205_13832.dep_graph)
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
    let uu____13856 = expected_typ env_ in
    ((let uu___206_13862 = env_ in
      {
        solver = (uu___206_13862.solver);
        range = (uu___206_13862.range);
        curmodule = (uu___206_13862.curmodule);
        gamma = (uu___206_13862.gamma);
        gamma_cache = (uu___206_13862.gamma_cache);
        modules = (uu___206_13862.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___206_13862.sigtab);
        is_pattern = (uu___206_13862.is_pattern);
        instantiate_imp = (uu___206_13862.instantiate_imp);
        effects = (uu___206_13862.effects);
        generalize = (uu___206_13862.generalize);
        letrecs = (uu___206_13862.letrecs);
        top_level = (uu___206_13862.top_level);
        check_uvars = (uu___206_13862.check_uvars);
        use_eq = false;
        is_iface = (uu___206_13862.is_iface);
        admit = (uu___206_13862.admit);
        lax = (uu___206_13862.lax);
        lax_universes = (uu___206_13862.lax_universes);
        failhard = (uu___206_13862.failhard);
        nosynth = (uu___206_13862.nosynth);
        tc_term = (uu___206_13862.tc_term);
        type_of = (uu___206_13862.type_of);
        universe_of = (uu___206_13862.universe_of);
        use_bv_sorts = (uu___206_13862.use_bv_sorts);
        qname_and_index = (uu___206_13862.qname_and_index);
        proof_ns = (uu___206_13862.proof_ns);
        synth = (uu___206_13862.synth);
        is_native_tactic = (uu___206_13862.is_native_tactic);
        identifier_info = (uu___206_13862.identifier_info);
        tc_hooks = (uu___206_13862.tc_hooks);
        dsenv = (uu___206_13862.dsenv);
        dep_graph = (uu___206_13862.dep_graph)
      }), uu____13856)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____13875 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___180_13885  ->
                    match uu___180_13885 with
                    | Binding_sig (uu____13888,se) -> [se]
                    | uu____13894 -> [])) in
          FStar_All.pipe_right uu____13875 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___207_13901 = env in
       {
         solver = (uu___207_13901.solver);
         range = (uu___207_13901.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___207_13901.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___207_13901.expected_typ);
         sigtab = (uu___207_13901.sigtab);
         is_pattern = (uu___207_13901.is_pattern);
         instantiate_imp = (uu___207_13901.instantiate_imp);
         effects = (uu___207_13901.effects);
         generalize = (uu___207_13901.generalize);
         letrecs = (uu___207_13901.letrecs);
         top_level = (uu___207_13901.top_level);
         check_uvars = (uu___207_13901.check_uvars);
         use_eq = (uu___207_13901.use_eq);
         is_iface = (uu___207_13901.is_iface);
         admit = (uu___207_13901.admit);
         lax = (uu___207_13901.lax);
         lax_universes = (uu___207_13901.lax_universes);
         failhard = (uu___207_13901.failhard);
         nosynth = (uu___207_13901.nosynth);
         tc_term = (uu___207_13901.tc_term);
         type_of = (uu___207_13901.type_of);
         universe_of = (uu___207_13901.universe_of);
         use_bv_sorts = (uu___207_13901.use_bv_sorts);
         qname_and_index = (uu___207_13901.qname_and_index);
         proof_ns = (uu___207_13901.proof_ns);
         synth = (uu___207_13901.synth);
         is_native_tactic = (uu___207_13901.is_native_tactic);
         identifier_info = (uu___207_13901.identifier_info);
         tc_hooks = (uu___207_13901.tc_hooks);
         dsenv = (uu___207_13901.dsenv);
         dep_graph = (uu___207_13901.dep_graph)
       })
let uvars_in_env: env -> FStar_Syntax_Syntax.uvars =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____13982)::tl1 -> aux out tl1
      | (Binding_lid (uu____13986,(uu____13987,t)))::tl1 ->
          let uu____14002 =
            let uu____14009 = FStar_Syntax_Free.uvars t in
            ext out uu____14009 in
          aux uu____14002 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14016;
            FStar_Syntax_Syntax.index = uu____14017;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14024 =
            let uu____14031 = FStar_Syntax_Free.uvars t in
            ext out uu____14031 in
          aux uu____14024 tl1
      | (Binding_sig uu____14038)::uu____14039 -> out
      | (Binding_sig_inst uu____14048)::uu____14049 -> out in
    aux no_uvs env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14104)::tl1 -> aux out tl1
      | (Binding_univ uu____14116)::tl1 -> aux out tl1
      | (Binding_lid (uu____14120,(uu____14121,t)))::tl1 ->
          let uu____14136 =
            let uu____14139 = FStar_Syntax_Free.univs t in
            ext out uu____14139 in
          aux uu____14136 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14142;
            FStar_Syntax_Syntax.index = uu____14143;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14150 =
            let uu____14153 = FStar_Syntax_Free.univs t in
            ext out uu____14153 in
          aux uu____14150 tl1
      | (Binding_sig uu____14156)::uu____14157 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.fifo_set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____14210)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____14226 = FStar_Util.fifo_set_add uname out in
          aux uu____14226 tl1
      | (Binding_lid (uu____14229,(uu____14230,t)))::tl1 ->
          let uu____14245 =
            let uu____14248 = FStar_Syntax_Free.univnames t in
            ext out uu____14248 in
          aux uu____14245 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____14251;
            FStar_Syntax_Syntax.index = uu____14252;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____14259 =
            let uu____14262 = FStar_Syntax_Free.univnames t in
            ext out uu____14262 in
          aux uu____14259 tl1
      | (Binding_sig uu____14265)::uu____14266 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___181_14290  ->
            match uu___181_14290 with
            | Binding_var x -> [x]
            | Binding_lid uu____14294 -> []
            | Binding_sig uu____14299 -> []
            | Binding_univ uu____14306 -> []
            | Binding_sig_inst uu____14307 -> []))
let binders_of_bindings: binding Prims.list -> FStar_Syntax_Syntax.binders =
  fun bs  ->
    let uu____14323 =
      let uu____14326 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____14326
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____14323 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____14348 =
      let uu____14349 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___182_14359  ->
                match uu___182_14359 with
                | Binding_var x ->
                    let uu____14361 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____14361
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____14364) ->
                    let uu____14365 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____14365
                | Binding_sig (ls,uu____14367) ->
                    let uu____14372 =
                      let uu____14373 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14373
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____14372
                | Binding_sig_inst (ls,uu____14383,uu____14384) ->
                    let uu____14389 =
                      let uu____14390 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____14390
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____14389)) in
      FStar_All.pipe_right uu____14349 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____14348 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____14407 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____14407
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____14435  ->
                 fun uu____14436  ->
                   match (uu____14435, uu____14436) with
                   | ((b1,uu____14454),(b2,uu____14456)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env: 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let string_of_delta_level: delta_level -> Prims.string =
  fun uu___183_14498  ->
    match uu___183_14498 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____14499 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___184_14517  ->
             match uu___184_14517 with
             | Binding_sig (lids,uu____14523) -> FStar_List.append lids keys
             | uu____14528 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____14534  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let should_enc_path: env -> Prims.string Prims.list -> Prims.bool =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____14568) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____14587,uu____14588) -> false in
      let uu____14597 =
        FStar_List.tryFind
          (fun uu____14615  ->
             match uu____14615 with | (p,uu____14623) -> list_prefix p path)
          env.proof_ns in
      match uu____14597 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____14634,b) -> b
let should_enc_lid: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____14652 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____14652
let cons_proof_ns: Prims.bool -> env -> name_prefix -> env =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___208_14664 = e in
        {
          solver = (uu___208_14664.solver);
          range = (uu___208_14664.range);
          curmodule = (uu___208_14664.curmodule);
          gamma = (uu___208_14664.gamma);
          gamma_cache = (uu___208_14664.gamma_cache);
          modules = (uu___208_14664.modules);
          expected_typ = (uu___208_14664.expected_typ);
          sigtab = (uu___208_14664.sigtab);
          is_pattern = (uu___208_14664.is_pattern);
          instantiate_imp = (uu___208_14664.instantiate_imp);
          effects = (uu___208_14664.effects);
          generalize = (uu___208_14664.generalize);
          letrecs = (uu___208_14664.letrecs);
          top_level = (uu___208_14664.top_level);
          check_uvars = (uu___208_14664.check_uvars);
          use_eq = (uu___208_14664.use_eq);
          is_iface = (uu___208_14664.is_iface);
          admit = (uu___208_14664.admit);
          lax = (uu___208_14664.lax);
          lax_universes = (uu___208_14664.lax_universes);
          failhard = (uu___208_14664.failhard);
          nosynth = (uu___208_14664.nosynth);
          tc_term = (uu___208_14664.tc_term);
          type_of = (uu___208_14664.type_of);
          universe_of = (uu___208_14664.universe_of);
          use_bv_sorts = (uu___208_14664.use_bv_sorts);
          qname_and_index = (uu___208_14664.qname_and_index);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth = (uu___208_14664.synth);
          is_native_tactic = (uu___208_14664.is_native_tactic);
          identifier_info = (uu___208_14664.identifier_info);
          tc_hooks = (uu___208_14664.tc_hooks);
          dsenv = (uu___208_14664.dsenv);
          dep_graph = (uu___208_14664.dep_graph)
        }
let add_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns true e path
let rem_proof_ns: env -> name_prefix -> env =
  fun e  -> fun path  -> cons_proof_ns false e path
let get_proof_ns: env -> proof_namespace = fun e  -> e.proof_ns
let set_proof_ns: proof_namespace -> env -> env =
  fun ns  ->
    fun e  ->
      let uu___209_14690 = e in
      {
        solver = (uu___209_14690.solver);
        range = (uu___209_14690.range);
        curmodule = (uu___209_14690.curmodule);
        gamma = (uu___209_14690.gamma);
        gamma_cache = (uu___209_14690.gamma_cache);
        modules = (uu___209_14690.modules);
        expected_typ = (uu___209_14690.expected_typ);
        sigtab = (uu___209_14690.sigtab);
        is_pattern = (uu___209_14690.is_pattern);
        instantiate_imp = (uu___209_14690.instantiate_imp);
        effects = (uu___209_14690.effects);
        generalize = (uu___209_14690.generalize);
        letrecs = (uu___209_14690.letrecs);
        top_level = (uu___209_14690.top_level);
        check_uvars = (uu___209_14690.check_uvars);
        use_eq = (uu___209_14690.use_eq);
        is_iface = (uu___209_14690.is_iface);
        admit = (uu___209_14690.admit);
        lax = (uu___209_14690.lax);
        lax_universes = (uu___209_14690.lax_universes);
        failhard = (uu___209_14690.failhard);
        nosynth = (uu___209_14690.nosynth);
        tc_term = (uu___209_14690.tc_term);
        type_of = (uu___209_14690.type_of);
        universe_of = (uu___209_14690.universe_of);
        use_bv_sorts = (uu___209_14690.use_bv_sorts);
        qname_and_index = (uu___209_14690.qname_and_index);
        proof_ns = ns;
        synth = (uu___209_14690.synth);
        is_native_tactic = (uu___209_14690.is_native_tactic);
        identifier_info = (uu___209_14690.identifier_info);
        tc_hooks = (uu___209_14690.tc_hooks);
        dsenv = (uu___209_14690.dsenv);
        dep_graph = (uu___209_14690.dep_graph)
      }
let unbound_vars:
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun e  ->
    fun t  ->
      let uu____14701 = FStar_Syntax_Free.names t in
      let uu____14704 = bound_vars e in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____14701 uu____14704
let closed: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    fun t  ->
      let uu____14721 = unbound_vars e t in
      FStar_Util.set_is_empty uu____14721
let closed': FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____14727 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____14727
let string_of_proof_ns: env -> Prims.string =
  fun env  ->
    let aux uu____14742 =
      match uu____14742 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____14758 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____14758) in
    let uu____14760 =
      let uu____14763 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____14763 FStar_List.rev in
    FStar_All.pipe_right uu____14760 (FStar_String.concat " ")
let dummy_solver: solver_t =
  {
    init = (fun uu____14780  -> ());
    push = (fun uu____14782  -> ());
    pop = (fun uu____14784  -> ());
    encode_modul = (fun uu____14787  -> fun uu____14788  -> ());
    encode_sig = (fun uu____14791  -> fun uu____14792  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____14798 =
             let uu____14805 = FStar_Options.peek () in (e, g, uu____14805) in
           [uu____14798]);
    solve = (fun uu____14821  -> fun uu____14822  -> fun uu____14823  -> ());
    finish = (fun uu____14829  -> ());
    refresh = (fun uu____14831  -> ())
  }