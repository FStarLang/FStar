open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv 
  | Binding_lid of (FStar_Ident.lident, FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2 
  | Binding_sig of (FStar_Ident.lident Prims.list,
  FStar_Syntax_Syntax.sigelt) FStar_Pervasives_Native.tuple2 
  | Binding_univ of FStar_Syntax_Syntax.univ_name 
  | Binding_sig_inst of (FStar_Ident.lident Prims.list,
  FStar_Syntax_Syntax.sigelt, FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_var _0 -> true | uu____50 -> false
let (__proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Binding_var _0 -> _0
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_lid _0 -> true | uu____68 -> false
let (__proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident, FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Binding_lid _0 -> _0
let (uu___is_Binding_sig : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_sig _0 -> true | uu____100 -> false
let (__proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list, FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | Binding_sig _0 -> _0
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_univ _0 -> true | uu____132 -> false
let (__proj__Binding_univ__item___0 :
  binding -> FStar_Syntax_Syntax.univ_name) =
  fun projectee -> match projectee with | Binding_univ _0 -> _0
let (uu___is_Binding_sig_inst : binding -> Prims.bool) =
  fun projectee ->
    match projectee with | Binding_sig_inst _0 -> true | uu____154 -> false
let (__proj__Binding_sig_inst__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list, FStar_Syntax_Syntax.sigelt,
      FStar_Syntax_Syntax.universes) FStar_Pervasives_Native.tuple3)
  = fun projectee -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac [@@deriving show]
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | NoDelta -> true | uu____196 -> false
let (uu___is_Inlining : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Inlining -> true | uu____202 -> false
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Eager_unfolding_only -> true | uu____208 -> false
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | Unfold _0 -> true | uu____215 -> false
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee -> match projectee with | Unfold _0 -> _0
let (uu___is_UnfoldTac : delta_level -> Prims.bool) =
  fun projectee ->
    match projectee with | UnfoldTac -> true | uu____228 -> false
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
    ;
  mlift_term:
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option
    }[@@deriving show]
let (__proj__Mkmlift__item__mlift_wp :
  mlift ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun projectee ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_wp
let (__proj__Mkmlift__item__mlift_term :
  mlift ->
    (FStar_Syntax_Syntax.universe ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.typ ->
           FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }[@@deriving show]
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl, FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident, FStar_Ident.lident, FStar_Ident.lident, mlift,
      mlift) FStar_Pervasives_Native.tuple5 Prims.list
    }[@@deriving show]
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl, FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident, FStar_Ident.lident, FStar_Ident.lident, mlift,
      mlift) FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__joins
type name_prefix = Prims.string Prims.list[@@deriving show]
type proof_namespace =
  (name_prefix, Prims.bool) FStar_Pervasives_Native.tuple2 Prims.list
[@@deriving show]
type cached_elt =
  (((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,
     (FStar_Syntax_Syntax.sigelt,
       FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,
    FStar_Range.range) FStar_Pervasives_Native.tuple2[@@deriving show]
type goal = FStar_Syntax_Syntax.term[@@deriving show]
type env =
  {
  solver: solver_t ;
  range: FStar_Range.range ;
  curmodule: FStar_Ident.lident ;
  gamma: binding Prims.list ;
  gamma_cache: cached_elt FStar_Util.smap ;
  modules: FStar_Syntax_Syntax.modul Prims.list ;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap ;
  is_pattern: Prims.bool ;
  instantiate_imp: Prims.bool ;
  effects: effects ;
  generalize: Prims.bool ;
  letrecs:
    (FStar_Syntax_Syntax.lbname, FStar_Syntax_Syntax.typ,
      FStar_Syntax_Syntax.univ_names) FStar_Pervasives_Native.tuple3
      Prims.list
    ;
  top_level: Prims.bool ;
  check_uvars: Prims.bool ;
  use_eq: Prims.bool ;
  is_iface: Prims.bool ;
  admit: Prims.bool ;
  lax: Prims.bool ;
  lax_universes: Prims.bool ;
  failhard: Prims.bool ;
  nosynth: Prims.bool ;
  tc_term:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp, guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ, guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe ;
  check_type_of:
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t
    ;
  use_bv_sorts: Prims.bool ;
  qtbl_name_and_index:
    (Prims.int FStar_Util.smap,
      (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
    ;
  normalized_eff_names: FStar_Ident.lident FStar_Util.smap ;
  proof_ns: proof_namespace ;
  synth_hook:
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
    ;
  splice:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list ;
  is_native_tactic: FStar_Ident.lid -> Prims.bool ;
  identifier_info: FStar_TypeChecker_Common.id_info_table FStar_ST.ref ;
  tc_hooks: tcenv_hooks ;
  dsenv: FStar_Syntax_DsEnv.env ;
  dep_graph: FStar_Parser_Dep.deps }[@@deriving show]
and solver_t =
  {
  init: env -> unit ;
  push: Prims.string -> unit ;
  pop: Prims.string -> unit ;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> unit ;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> unit ;
  preprocess:
    env ->
      goal ->
        (env, goal, FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list
    ;
  solve:
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit
    ;
  finish: unit -> unit ;
  refresh: unit -> unit }[@@deriving show]
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula ;
  deferred: FStar_TypeChecker_Common.deferred ;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,
      FStar_TypeChecker_Common.univ_ineq Prims.list)
      FStar_Pervasives_Native.tuple2
    ;
  implicits:
    (Prims.string, env, FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ, FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
    }[@@deriving show]
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> unit }[@@deriving show]
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__solver
let (__proj__Mkenv__item__range : env -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__range
let (__proj__Mkenv__item__curmodule : env -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__curmodule
let (__proj__Mkenv__item__gamma : env -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma
let (__proj__Mkenv__item__gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__gamma_cache
let (__proj__Mkenv__item__modules :
  env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__modules
let (__proj__Mkenv__item__expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__expected_typ
let (__proj__Mkenv__item__sigtab :
  env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__sigtab
let (__proj__Mkenv__item__is_pattern : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_pattern
let (__proj__Mkenv__item__instantiate_imp : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__instantiate_imp
let (__proj__Mkenv__item__effects : env -> effects) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__effects
let (__proj__Mkenv__item__generalize : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__generalize
let (__proj__Mkenv__item__letrecs :
  env ->
    (FStar_Syntax_Syntax.lbname, FStar_Syntax_Syntax.typ,
      FStar_Syntax_Syntax.univ_names) FStar_Pervasives_Native.tuple3
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__letrecs
let (__proj__Mkenv__item__top_level : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__top_level
let (__proj__Mkenv__item__check_uvars : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_uvars
let (__proj__Mkenv__item__use_eq : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_eq
let (__proj__Mkenv__item__is_iface : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_iface
let (__proj__Mkenv__item__admit : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__admit
let (__proj__Mkenv__item__lax : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax
let (__proj__Mkenv__item__lax_universes : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__lax_universes
let (__proj__Mkenv__item__failhard : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__failhard
let (__proj__Mkenv__item__nosynth : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__nosynth
let (__proj__Mkenv__item__tc_term :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp, guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_term
let (__proj__Mkenv__item__type_of :
  env ->
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ, guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__type_of
let (__proj__Mkenv__item__universe_of :
  env -> env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__universe_of
let (__proj__Mkenv__item__check_type_of :
  env ->
    Prims.bool ->
      env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__check_type_of
let (__proj__Mkenv__item__use_bv_sorts : env -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__use_bv_sorts
let (__proj__Mkenv__item__qtbl_name_and_index :
  env ->
    (Prims.int FStar_Util.smap,
      (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__qtbl_name_and_index
let (__proj__Mkenv__item__normalized_eff_names :
  env -> FStar_Ident.lident FStar_Util.smap) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__normalized_eff_names
let (__proj__Mkenv__item__proof_ns : env -> proof_namespace) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__proof_ns
let (__proj__Mkenv__item__synth_hook :
  env ->
    env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__synth_hook
let (__proj__Mkenv__item__splice :
  env ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__splice
let (__proj__Mkenv__item__is_native_tactic :
  env -> FStar_Ident.lid -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__is_native_tactic
let (__proj__Mkenv__item__identifier_info :
  env -> FStar_TypeChecker_Common.id_info_table FStar_ST.ref) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__identifier_info
let (__proj__Mkenv__item__tc_hooks : env -> tcenv_hooks) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__tc_hooks
let (__proj__Mkenv__item__dsenv : env -> FStar_Syntax_DsEnv.env) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dsenv
let (__proj__Mkenv__item__dep_graph : env -> FStar_Parser_Dep.deps) =
  fun projectee ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        check_type_of = __fname__check_type_of;
        use_bv_sorts = __fname__use_bv_sorts;
        qtbl_name_and_index = __fname__qtbl_name_and_index;
        normalized_eff_names = __fname__normalized_eff_names;
        proof_ns = __fname__proof_ns; synth_hook = __fname__synth_hook;
        splice = __fname__splice;
        is_native_tactic = __fname__is_native_tactic;
        identifier_info = __fname__identifier_info;
        tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv;
        dep_graph = __fname__dep_graph;_} -> __fname__dep_graph
let (__proj__Mksolver_t__item__init : solver_t -> env -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_sig
let (__proj__Mksolver_t__item__preprocess :
  solver_t ->
    env ->
      goal ->
        (env, goal, FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list)
  =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__preprocess
let (__proj__Mksolver_t__item__solve :
  solver_t ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,
      FStar_TypeChecker_Common.univ_ineq Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
let (__proj__Mkguard_t__item__implicits :
  guard_t ->
    (Prims.string, env, FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ, FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks -> env -> binding -> unit) =
  fun projectee ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
type implicits =
  (Prims.string, env, FStar_Syntax_Syntax.uvar, FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ, FStar_Range.range)
    FStar_Pervasives_Native.tuple6 Prims.list[@@deriving show]
let (rename_gamma :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list)
  =
  fun subst1 ->
    fun gamma ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___76_7587 ->
              match uu___76_7587 with
              | Binding_var x ->
                  let y =
                    let uu____7590 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Subst.subst subst1 uu____7590 in
                  let uu____7591 =
                    let uu____7592 = FStar_Syntax_Subst.compress y in
                    uu____7592.FStar_Syntax_Syntax.n in
                  (match uu____7591 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____7596 =
                         let uu___91_7597 = y1 in
                         let uu____7598 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___91_7597.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___91_7597.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____7598
                         } in
                       Binding_var uu____7596
                   | uu____7601 -> failwith "Not a renaming")
              | b -> b))
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1 ->
    fun env ->
      let uu___92_7613 = env in
      let uu____7614 = rename_gamma subst1 env.gamma in
      {
        solver = (uu___92_7613.solver);
        range = (uu___92_7613.range);
        curmodule = (uu___92_7613.curmodule);
        gamma = uu____7614;
        gamma_cache = (uu___92_7613.gamma_cache);
        modules = (uu___92_7613.modules);
        expected_typ = (uu___92_7613.expected_typ);
        sigtab = (uu___92_7613.sigtab);
        is_pattern = (uu___92_7613.is_pattern);
        instantiate_imp = (uu___92_7613.instantiate_imp);
        effects = (uu___92_7613.effects);
        generalize = (uu___92_7613.generalize);
        letrecs = (uu___92_7613.letrecs);
        top_level = (uu___92_7613.top_level);
        check_uvars = (uu___92_7613.check_uvars);
        use_eq = (uu___92_7613.use_eq);
        is_iface = (uu___92_7613.is_iface);
        admit = (uu___92_7613.admit);
        lax = (uu___92_7613.lax);
        lax_universes = (uu___92_7613.lax_universes);
        failhard = (uu___92_7613.failhard);
        nosynth = (uu___92_7613.nosynth);
        tc_term = (uu___92_7613.tc_term);
        type_of = (uu___92_7613.type_of);
        universe_of = (uu___92_7613.universe_of);
        check_type_of = (uu___92_7613.check_type_of);
        use_bv_sorts = (uu___92_7613.use_bv_sorts);
        qtbl_name_and_index = (uu___92_7613.qtbl_name_and_index);
        normalized_eff_names = (uu___92_7613.normalized_eff_names);
        proof_ns = (uu___92_7613.proof_ns);
        synth_hook = (uu___92_7613.synth_hook);
        splice = (uu___92_7613.splice);
        is_native_tactic = (uu___92_7613.is_native_tactic);
        identifier_info = (uu___92_7613.identifier_info);
        tc_hooks = (uu___92_7613.tc_hooks);
        dsenv = (uu___92_7613.dsenv);
        dep_graph = (uu___92_7613.dep_graph)
      }
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____7621 -> fun uu____7622 -> ()) }
let (tc_hooks : env -> tcenv_hooks) = fun env -> env.tc_hooks
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env ->
    fun hooks ->
      let uu___93_7638 = env in
      {
        solver = (uu___93_7638.solver);
        range = (uu___93_7638.range);
        curmodule = (uu___93_7638.curmodule);
        gamma = (uu___93_7638.gamma);
        gamma_cache = (uu___93_7638.gamma_cache);
        modules = (uu___93_7638.modules);
        expected_typ = (uu___93_7638.expected_typ);
        sigtab = (uu___93_7638.sigtab);
        is_pattern = (uu___93_7638.is_pattern);
        instantiate_imp = (uu___93_7638.instantiate_imp);
        effects = (uu___93_7638.effects);
        generalize = (uu___93_7638.generalize);
        letrecs = (uu___93_7638.letrecs);
        top_level = (uu___93_7638.top_level);
        check_uvars = (uu___93_7638.check_uvars);
        use_eq = (uu___93_7638.use_eq);
        is_iface = (uu___93_7638.is_iface);
        admit = (uu___93_7638.admit);
        lax = (uu___93_7638.lax);
        lax_universes = (uu___93_7638.lax_universes);
        failhard = (uu___93_7638.failhard);
        nosynth = (uu___93_7638.nosynth);
        tc_term = (uu___93_7638.tc_term);
        type_of = (uu___93_7638.type_of);
        universe_of = (uu___93_7638.universe_of);
        check_type_of = (uu___93_7638.check_type_of);
        use_bv_sorts = (uu___93_7638.use_bv_sorts);
        qtbl_name_and_index = (uu___93_7638.qtbl_name_and_index);
        normalized_eff_names = (uu___93_7638.normalized_eff_names);
        proof_ns = (uu___93_7638.proof_ns);
        synth_hook = (uu___93_7638.synth_hook);
        splice = (uu___93_7638.splice);
        is_native_tactic = (uu___93_7638.is_native_tactic);
        identifier_info = (uu___93_7638.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___93_7638.dsenv);
        dep_graph = (uu___93_7638.dep_graph)
      }
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e ->
    fun g ->
      let uu___94_7649 = e in
      {
        solver = (uu___94_7649.solver);
        range = (uu___94_7649.range);
        curmodule = (uu___94_7649.curmodule);
        gamma = (uu___94_7649.gamma);
        gamma_cache = (uu___94_7649.gamma_cache);
        modules = (uu___94_7649.modules);
        expected_typ = (uu___94_7649.expected_typ);
        sigtab = (uu___94_7649.sigtab);
        is_pattern = (uu___94_7649.is_pattern);
        instantiate_imp = (uu___94_7649.instantiate_imp);
        effects = (uu___94_7649.effects);
        generalize = (uu___94_7649.generalize);
        letrecs = (uu___94_7649.letrecs);
        top_level = (uu___94_7649.top_level);
        check_uvars = (uu___94_7649.check_uvars);
        use_eq = (uu___94_7649.use_eq);
        is_iface = (uu___94_7649.is_iface);
        admit = (uu___94_7649.admit);
        lax = (uu___94_7649.lax);
        lax_universes = (uu___94_7649.lax_universes);
        failhard = (uu___94_7649.failhard);
        nosynth = (uu___94_7649.nosynth);
        tc_term = (uu___94_7649.tc_term);
        type_of = (uu___94_7649.type_of);
        universe_of = (uu___94_7649.universe_of);
        check_type_of = (uu___94_7649.check_type_of);
        use_bv_sorts = (uu___94_7649.use_bv_sorts);
        qtbl_name_and_index = (uu___94_7649.qtbl_name_and_index);
        normalized_eff_names = (uu___94_7649.normalized_eff_names);
        proof_ns = (uu___94_7649.proof_ns);
        synth_hook = (uu___94_7649.synth_hook);
        splice = (uu___94_7649.splice);
        is_native_tactic = (uu___94_7649.is_native_tactic);
        identifier_info = (uu___94_7649.identifier_info);
        tc_hooks = (uu___94_7649.tc_hooks);
        dsenv = (uu___94_7649.dsenv);
        dep_graph = g
      }
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun e -> e.dep_graph
type env_t = env[@@deriving show]
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap[@@deriving show]
let (should_verify : env -> Prims.bool) =
  fun env ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d ->
    fun q ->
      match (d, q) with
      | (NoDelta, uu____7672) -> true
      | (Eager_unfolding_only,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____7673,
         FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> true
      | (Unfold uu____7674, FStar_Syntax_Syntax.Visible_default) -> true
      | (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> true
      | uu____7675 -> false
let (default_table_size : Prims.int) = (Prims.parse_int "200")
let new_sigtab : 'Auu____7684 . unit -> 'Auu____7684 FStar_Util.smap =
  fun uu____7691 -> FStar_Util.smap_create default_table_size
let new_gamma_cache : 'Auu____7696 . unit -> 'Auu____7696 FStar_Util.smap =
  fun uu____7703 -> FStar_Util.smap_create (Prims.parse_int "100")
let (initial_env :
  FStar_Parser_Dep.deps ->
    (env ->
       FStar_Syntax_Syntax.term ->
         (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.lcomp, guard_t)
           FStar_Pervasives_Native.tuple3)
      ->
      (env ->
         FStar_Syntax_Syntax.term ->
           (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.typ, guard_t)
             FStar_Pervasives_Native.tuple3)
        ->
        (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
            -> solver_t -> FStar_Ident.lident -> env)
  =
  fun deps ->
    fun tc_term ->
      fun type_of ->
        fun universe_of ->
          fun check_type_of ->
            fun solver ->
              fun module_lid ->
                let uu____7813 = new_gamma_cache () in
                let uu____7816 = new_sigtab () in
                let uu____7819 =
                  let uu____7832 =
                    FStar_Util.smap_create (Prims.parse_int "10") in
                  (uu____7832, FStar_Pervasives_Native.None) in
                let uu____7847 =
                  FStar_Util.smap_create (Prims.parse_int "20") in
                let uu____7850 = FStar_Options.using_facts_from () in
                let uu____7851 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty in
                let uu____7854 = FStar_Syntax_DsEnv.empty_env () in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____7813;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____7816;
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
                  check_type_of;
                  use_bv_sorts = false;
                  qtbl_name_and_index = uu____7819;
                  normalized_eff_names = uu____7847;
                  proof_ns = uu____7850;
                  synth_hook =
                    (fun e ->
                       fun g ->
                         fun tau -> failwith "no synthesizer available");
                  splice =
                    (fun e -> fun tau -> failwith "no splicer available");
                  is_native_tactic = (fun uu____7890 -> false);
                  identifier_info = uu____7851;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____7854;
                  dep_graph = deps
                }
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env -> env.dsenv
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env -> env.sigtab
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env -> env.gamma_cache
let (query_indices :
  (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]]
let (push_query_indices : unit -> unit) =
  fun uu____8053 ->
    let uu____8054 = FStar_ST.op_Bang query_indices in
    match uu____8054 with
    | [] -> failwith "Empty query indices!"
    | uu____8114 ->
        let uu____8123 =
          let uu____8132 =
            let uu____8139 = FStar_ST.op_Bang query_indices in
            FStar_List.hd uu____8139 in
          let uu____8199 = FStar_ST.op_Bang query_indices in uu____8132 ::
            uu____8199 in
        FStar_ST.op_Colon_Equals query_indices uu____8123
let (pop_query_indices : unit -> unit) =
  fun uu____8308 ->
    let uu____8309 = FStar_ST.op_Bang query_indices in
    match uu____8309 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
let (add_query_index :
  (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8444 ->
    match uu____8444 with
    | (l, n1) ->
        let uu____8451 = FStar_ST.op_Bang query_indices in
        (match uu____8451 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____8582 -> failwith "Empty query indices")
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident, Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____8601 ->
    let uu____8602 = FStar_ST.op_Bang query_indices in
    FStar_List.hd uu____8602
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (push_stack : env -> env) =
  fun env ->
    (let uu____8709 =
       let uu____8712 = FStar_ST.op_Bang stack in env :: uu____8712 in
     FStar_ST.op_Colon_Equals stack uu____8709);
    (let uu___95_8781 = env in
     let uu____8782 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____8785 = FStar_Util.smap_copy (sigtab env) in
     let uu____8788 =
       let uu____8801 =
         let uu____8804 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst in
         FStar_Util.smap_copy uu____8804 in
       let uu____8829 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd in
       (uu____8801, uu____8829) in
     let uu____8870 = FStar_Util.smap_copy env.normalized_eff_names in
     let uu____8873 =
       let uu____8876 = FStar_ST.op_Bang env.identifier_info in
       FStar_Util.mk_ref uu____8876 in
     {
       solver = (uu___95_8781.solver);
       range = (uu___95_8781.range);
       curmodule = (uu___95_8781.curmodule);
       gamma = (uu___95_8781.gamma);
       gamma_cache = uu____8782;
       modules = (uu___95_8781.modules);
       expected_typ = (uu___95_8781.expected_typ);
       sigtab = uu____8785;
       is_pattern = (uu___95_8781.is_pattern);
       instantiate_imp = (uu___95_8781.instantiate_imp);
       effects = (uu___95_8781.effects);
       generalize = (uu___95_8781.generalize);
       letrecs = (uu___95_8781.letrecs);
       top_level = (uu___95_8781.top_level);
       check_uvars = (uu___95_8781.check_uvars);
       use_eq = (uu___95_8781.use_eq);
       is_iface = (uu___95_8781.is_iface);
       admit = (uu___95_8781.admit);
       lax = (uu___95_8781.lax);
       lax_universes = (uu___95_8781.lax_universes);
       failhard = (uu___95_8781.failhard);
       nosynth = (uu___95_8781.nosynth);
       tc_term = (uu___95_8781.tc_term);
       type_of = (uu___95_8781.type_of);
       universe_of = (uu___95_8781.universe_of);
       check_type_of = (uu___95_8781.check_type_of);
       use_bv_sorts = (uu___95_8781.use_bv_sorts);
       qtbl_name_and_index = uu____8788;
       normalized_eff_names = uu____8870;
       proof_ns = (uu___95_8781.proof_ns);
       synth_hook = (uu___95_8781.synth_hook);
       splice = (uu___95_8781.splice);
       is_native_tactic = (uu___95_8781.is_native_tactic);
       identifier_info = uu____8873;
       tc_hooks = (uu___95_8781.tc_hooks);
       dsenv = (uu___95_8781.dsenv);
       dep_graph = (uu___95_8781.dep_graph)
     })
let (pop_stack : unit -> env) =
  fun uu____8980 ->
    let uu____8981 = FStar_ST.op_Bang stack in
    match uu____8981 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9055 -> failwith "Impossible: Too many pops"
let (push : env -> Prims.string -> env) =
  fun env ->
    fun msg -> push_query_indices (); (env.solver).push msg; push_stack env
let (pop : env -> Prims.string -> env) =
  fun env ->
    fun msg -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let (incr_query_index : env -> env) =
  fun env ->
    let qix = peek_query_indices () in
    match env.qtbl_name_and_index with
    | (uu____9094, FStar_Pervasives_Native.None) -> env
    | (tbl, FStar_Pervasives_Native.Some (l, n1)) ->
        let uu____9126 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9152 ->
                  match uu____9152 with
                  | (m, uu____9158) -> FStar_Ident.lid_equals l m)) in
        (match uu____9126 with
         | FStar_Pervasives_Native.None ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___96_9166 = env in
               {
                 solver = (uu___96_9166.solver);
                 range = (uu___96_9166.range);
                 curmodule = (uu___96_9166.curmodule);
                 gamma = (uu___96_9166.gamma);
                 gamma_cache = (uu___96_9166.gamma_cache);
                 modules = (uu___96_9166.modules);
                 expected_typ = (uu___96_9166.expected_typ);
                 sigtab = (uu___96_9166.sigtab);
                 is_pattern = (uu___96_9166.is_pattern);
                 instantiate_imp = (uu___96_9166.instantiate_imp);
                 effects = (uu___96_9166.effects);
                 generalize = (uu___96_9166.generalize);
                 letrecs = (uu___96_9166.letrecs);
                 top_level = (uu___96_9166.top_level);
                 check_uvars = (uu___96_9166.check_uvars);
                 use_eq = (uu___96_9166.use_eq);
                 is_iface = (uu___96_9166.is_iface);
                 admit = (uu___96_9166.admit);
                 lax = (uu___96_9166.lax);
                 lax_universes = (uu___96_9166.lax_universes);
                 failhard = (uu___96_9166.failhard);
                 nosynth = (uu___96_9166.nosynth);
                 tc_term = (uu___96_9166.tc_term);
                 type_of = (uu___96_9166.type_of);
                 universe_of = (uu___96_9166.universe_of);
                 check_type_of = (uu___96_9166.check_type_of);
                 use_bv_sorts = (uu___96_9166.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___96_9166.normalized_eff_names);
                 proof_ns = (uu___96_9166.proof_ns);
                 synth_hook = (uu___96_9166.synth_hook);
                 splice = (uu___96_9166.splice);
                 is_native_tactic = (uu___96_9166.is_native_tactic);
                 identifier_info = (uu___96_9166.identifier_info);
                 tc_hooks = (uu___96_9166.tc_hooks);
                 dsenv = (uu___96_9166.dsenv);
                 dep_graph = (uu___96_9166.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9179, m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___97_9188 = env in
               {
                 solver = (uu___97_9188.solver);
                 range = (uu___97_9188.range);
                 curmodule = (uu___97_9188.curmodule);
                 gamma = (uu___97_9188.gamma);
                 gamma_cache = (uu___97_9188.gamma_cache);
                 modules = (uu___97_9188.modules);
                 expected_typ = (uu___97_9188.expected_typ);
                 sigtab = (uu___97_9188.sigtab);
                 is_pattern = (uu___97_9188.is_pattern);
                 instantiate_imp = (uu___97_9188.instantiate_imp);
                 effects = (uu___97_9188.effects);
                 generalize = (uu___97_9188.generalize);
                 letrecs = (uu___97_9188.letrecs);
                 top_level = (uu___97_9188.top_level);
                 check_uvars = (uu___97_9188.check_uvars);
                 use_eq = (uu___97_9188.use_eq);
                 is_iface = (uu___97_9188.is_iface);
                 admit = (uu___97_9188.admit);
                 lax = (uu___97_9188.lax);
                 lax_universes = (uu___97_9188.lax_universes);
                 failhard = (uu___97_9188.failhard);
                 nosynth = (uu___97_9188.nosynth);
                 tc_term = (uu___97_9188.tc_term);
                 type_of = (uu___97_9188.type_of);
                 universe_of = (uu___97_9188.universe_of);
                 check_type_of = (uu___97_9188.check_type_of);
                 use_bv_sorts = (uu___97_9188.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___97_9188.normalized_eff_names);
                 proof_ns = (uu___97_9188.proof_ns);
                 synth_hook = (uu___97_9188.synth_hook);
                 splice = (uu___97_9188.splice);
                 is_native_tactic = (uu___97_9188.is_native_tactic);
                 identifier_info = (uu___97_9188.identifier_info);
                 tc_hooks = (uu___97_9188.tc_hooks);
                 dsenv = (uu___97_9188.dsenv);
                 dep_graph = (uu___97_9188.dep_graph)
               })))
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env ->
    fun l -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let (set_range : env -> FStar_Range.range -> env) =
  fun e ->
    fun r ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___98_9222 = e in
         {
           solver = (uu___98_9222.solver);
           range = r;
           curmodule = (uu___98_9222.curmodule);
           gamma = (uu___98_9222.gamma);
           gamma_cache = (uu___98_9222.gamma_cache);
           modules = (uu___98_9222.modules);
           expected_typ = (uu___98_9222.expected_typ);
           sigtab = (uu___98_9222.sigtab);
           is_pattern = (uu___98_9222.is_pattern);
           instantiate_imp = (uu___98_9222.instantiate_imp);
           effects = (uu___98_9222.effects);
           generalize = (uu___98_9222.generalize);
           letrecs = (uu___98_9222.letrecs);
           top_level = (uu___98_9222.top_level);
           check_uvars = (uu___98_9222.check_uvars);
           use_eq = (uu___98_9222.use_eq);
           is_iface = (uu___98_9222.is_iface);
           admit = (uu___98_9222.admit);
           lax = (uu___98_9222.lax);
           lax_universes = (uu___98_9222.lax_universes);
           failhard = (uu___98_9222.failhard);
           nosynth = (uu___98_9222.nosynth);
           tc_term = (uu___98_9222.tc_term);
           type_of = (uu___98_9222.type_of);
           universe_of = (uu___98_9222.universe_of);
           check_type_of = (uu___98_9222.check_type_of);
           use_bv_sorts = (uu___98_9222.use_bv_sorts);
           qtbl_name_and_index = (uu___98_9222.qtbl_name_and_index);
           normalized_eff_names = (uu___98_9222.normalized_eff_names);
           proof_ns = (uu___98_9222.proof_ns);
           synth_hook = (uu___98_9222.synth_hook);
           splice = (uu___98_9222.splice);
           is_native_tactic = (uu___98_9222.is_native_tactic);
           identifier_info = (uu___98_9222.identifier_info);
           tc_hooks = (uu___98_9222.tc_hooks);
           dsenv = (uu___98_9222.dsenv);
           dep_graph = (uu___98_9222.dep_graph)
         })
let (get_range : env -> FStar_Range.range) = fun e -> e.range
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env ->
    fun enabled ->
      let uu____9238 =
        let uu____9239 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_toggle uu____9239 enabled in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9238
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env ->
    fun bv ->
      fun ty ->
        let uu____9313 =
          let uu____9314 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_bv uu____9314 bv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9313
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env ->
    fun fv ->
      fun ty ->
        let uu____9388 =
          let uu____9389 = FStar_ST.op_Bang env.identifier_info in
          FStar_TypeChecker_Common.id_info_insert_fv uu____9389 fv ty in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9388
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env ->
    fun ty_map ->
      let uu____9463 =
        let uu____9464 = FStar_ST.op_Bang env.identifier_info in
        FStar_TypeChecker_Common.id_info_promote uu____9464 ty_map in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9463
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env -> env.modules
let (current_module : env -> FStar_Ident.lident) = fun env -> env.curmodule
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env ->
    fun lid ->
      let uu___99_9545 = env in
      {
        solver = (uu___99_9545.solver);
        range = (uu___99_9545.range);
        curmodule = lid;
        gamma = (uu___99_9545.gamma);
        gamma_cache = (uu___99_9545.gamma_cache);
        modules = (uu___99_9545.modules);
        expected_typ = (uu___99_9545.expected_typ);
        sigtab = (uu___99_9545.sigtab);
        is_pattern = (uu___99_9545.is_pattern);
        instantiate_imp = (uu___99_9545.instantiate_imp);
        effects = (uu___99_9545.effects);
        generalize = (uu___99_9545.generalize);
        letrecs = (uu___99_9545.letrecs);
        top_level = (uu___99_9545.top_level);
        check_uvars = (uu___99_9545.check_uvars);
        use_eq = (uu___99_9545.use_eq);
        is_iface = (uu___99_9545.is_iface);
        admit = (uu___99_9545.admit);
        lax = (uu___99_9545.lax);
        lax_universes = (uu___99_9545.lax_universes);
        failhard = (uu___99_9545.failhard);
        nosynth = (uu___99_9545.nosynth);
        tc_term = (uu___99_9545.tc_term);
        type_of = (uu___99_9545.type_of);
        universe_of = (uu___99_9545.universe_of);
        check_type_of = (uu___99_9545.check_type_of);
        use_bv_sorts = (uu___99_9545.use_bv_sorts);
        qtbl_name_and_index = (uu___99_9545.qtbl_name_and_index);
        normalized_eff_names = (uu___99_9545.normalized_eff_names);
        proof_ns = (uu___99_9545.proof_ns);
        synth_hook = (uu___99_9545.synth_hook);
        splice = (uu___99_9545.splice);
        is_native_tactic = (uu___99_9545.is_native_tactic);
        identifier_info = (uu___99_9545.identifier_info);
        tc_hooks = (uu___99_9545.tc_hooks);
        dsenv = (uu___99_9545.dsenv);
        dep_graph = (uu___99_9545.dep_graph)
      }
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____9572 = FStar_Ident.text_of_lid lid in
      FStar_Util.smap_try_find (sigtab env) uu____9572
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    let uu____9582 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str in
    (FStar_Errors.Fatal_NameNotFound, uu____9582)
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1 ->
    let uu____9592 =
      let uu____9593 = FStar_Syntax_Print.bv_to_string v1 in
      FStar_Util.format1 "Variable \"%s\" not found" uu____9593 in
    (FStar_Errors.Fatal_VariableNotFound, uu____9592)
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____9598 ->
    let uu____9599 = FStar_Syntax_Unionfind.univ_fresh () in
    FStar_Syntax_Syntax.U_unif uu____9599
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun ts ->
    fun us ->
      match (ts, us) with
      | (([], t), []) -> ([], t)
      | ((formals, t), uu____9641) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i -> fun u -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____9663 = FStar_Syntax_Subst.subst vs t in (us, uu____9663)
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___77_9679 ->
    match uu___77_9679 with
    | ([], t) -> ([], t)
    | (us, t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____9703 -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r ->
    fun t ->
      let uu____9720 = inst_tscheme t in
      match uu____9720 with
      | (us, t1) ->
          let uu____9731 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____9731)
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts ->
    fun env ->
      fun ed ->
        fun uu____9751 ->
          match uu____9751 with
          | (us, t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____9766 =
                         let uu____9767 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____9768 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____9769 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____9770 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____9767 uu____9768 uu____9769 uu____9770 in
                       failwith uu____9766)
                    else ();
                    (let uu____9772 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____9772))
               | uu____9779 ->
                   let uu____9780 =
                     let uu____9781 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____9781 in
                   failwith uu____9780)
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee -> match projectee with | Yes -> true | uu____9787 -> false
let (uu___is_No : tri -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu____9793 -> false
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee -> match projectee with | Maybe -> true | uu____9799 -> false
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env ->
    fun l ->
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
             | ([], uu____9841) -> Maybe
             | (uu____9848, []) -> No
             | (hd1::tl1, hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____9867 -> No in
           aux cur1 lns)
        else No
type qninfo =
  (((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,
     (FStar_Syntax_Syntax.sigelt,
       FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,
    FStar_Range.range) FStar_Pervasives_Native.tuple2
    FStar_Pervasives_Native.option[@@deriving show]
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env ->
    fun lid ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____9958 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____9958 with
          | FStar_Pervasives_Native.None ->
              FStar_Util.find_map env.gamma
                (fun uu___78_10004 ->
                   match uu___78_10004 with
                   | Binding_lid (l, t) ->
                       let uu____10027 = FStar_Ident.lid_equals lid l in
                       if uu____10027
                       then
                         let uu____10048 =
                           let uu____10067 =
                             let uu____10082 = inst_tscheme t in
                             FStar_Util.Inl uu____10082 in
                           let uu____10097 = FStar_Ident.range_of_lid l in
                           (uu____10067, uu____10097) in
                         FStar_Pervasives_Native.Some uu____10048
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____10149,
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_bundle (ses, uu____10151);
                          FStar_Syntax_Syntax.sigrng = uu____10152;
                          FStar_Syntax_Syntax.sigquals = uu____10153;
                          FStar_Syntax_Syntax.sigmeta = uu____10154;
                          FStar_Syntax_Syntax.sigattrs = uu____10155;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se ->
                            let uu____10175 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____10175
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids, s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____10223 ->
                             FStar_Pervasives_Native.Some t
                         | uu____10230 -> cache t in
                       let uu____10231 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____10231 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____10273 =
                              let uu____10274 = FStar_Ident.range_of_lid l in
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                uu____10274) in
                            maybe_cache uu____10273)
                   | Binding_sig_inst (lids, s, us) ->
                       let uu____10308 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____10308 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____10350 =
                              let uu____10369 = FStar_Ident.range_of_lid l in
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                uu____10369) in
                            FStar_Pervasives_Native.Some uu____10350)
                   | uu____10414 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____10474 = find_in_sigtab env lid in
         match uu____10474 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____10561) ->
          add_sigelts env ses
      | uu____10570 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____10584 -> ()))
and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env ->
    fun ses -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ, FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun bv ->
      FStar_Util.find_map env.gamma
        (fun uu___79_10615 ->
           match uu___79_10615 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____10633 -> FStar_Pervasives_Native.None)
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,
          FStar_Range.range) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____10694, lb::[]), uu____10696) ->
            let uu____10709 =
              let uu____10718 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp)) in
              let uu____10727 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname in
              (uu____10718, uu____10727) in
            FStar_Pervasives_Native.Some uu____10709
        | FStar_Syntax_Syntax.Sig_let ((uu____10740, lbs), uu____10742) ->
            FStar_Util.find_map lbs
              (fun lb ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____10778 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____10790 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                     if uu____10790
                     then
                       let uu____10801 =
                         let uu____10810 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp)) in
                         let uu____10819 = FStar_Syntax_Syntax.range_of_fv fv in
                         (uu____10810, uu____10819) in
                       FStar_Pervasives_Native.Some uu____10801
                     else FStar_Pervasives_Native.None)
        | uu____10841 -> FStar_Pervasives_Native.None
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun se ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____10900 =
            let uu____10909 =
              let uu____10914 =
                let uu____10915 =
                  let uu____10918 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____10918 in
                ((ne.FStar_Syntax_Syntax.univs), uu____10915) in
              inst_tscheme1 uu____10914 in
            (uu____10909, (se.FStar_Syntax_Syntax.sigrng)) in
          FStar_Pervasives_Native.Some uu____10900
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, us, binders, uu____10938, uu____10939) ->
          let uu____10944 =
            let uu____10953 =
              let uu____10958 =
                let uu____10959 =
                  let uu____10962 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                  FStar_Syntax_Util.arrow binders uu____10962 in
                (us, uu____10959) in
              inst_tscheme1 uu____10958 in
            (uu____10953, (se.FStar_Syntax_Syntax.sigrng)) in
          FStar_Pervasives_Native.Some uu____10944
      | uu____10979 -> FStar_Pervasives_Native.None
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,
           FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,
          FStar_Range.range) FStar_Pervasives_Native.tuple2
          FStar_Pervasives_Native.option)
  =
  fun us_opt ->
    fun env ->
      fun lid ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us in
        let mapper uu____11067 =
          match uu____11067 with
          | (lr, rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11163, uvs, t, uu____11166, uu____11167,
                         uu____11168);
                      FStar_Syntax_Syntax.sigrng = uu____11169;
                      FStar_Syntax_Syntax.sigquals = uu____11170;
                      FStar_Syntax_Syntax.sigmeta = uu____11171;
                      FStar_Syntax_Syntax.sigattrs = uu____11172;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____11193 =
                     let uu____11202 = inst_tscheme1 (uvs, t) in
                     (uu____11202, rng) in
                   FStar_Pervasives_Native.Some uu____11193
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t);
                      FStar_Syntax_Syntax.sigrng = uu____11222;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11224;
                      FStar_Syntax_Syntax.sigattrs = uu____11225;_},
                    FStar_Pervasives_Native.None)
                   ->
                   let uu____11242 =
                     let uu____11243 = in_cur_mod env l in uu____11243 = Yes in
                   if uu____11242
                   then
                     let uu____11254 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface in
                     (if uu____11254
                      then
                        let uu____11267 =
                          let uu____11276 = inst_tscheme1 (uvs, t) in
                          (uu____11276, rng) in
                        FStar_Pervasives_Native.Some uu____11267
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____11303 =
                        let uu____11312 = inst_tscheme1 (uvs, t) in
                        (uu____11312, rng) in
                      FStar_Pervasives_Native.Some uu____11303)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____11333, uu____11334);
                      FStar_Syntax_Syntax.sigrng = uu____11335;
                      FStar_Syntax_Syntax.sigquals = uu____11336;
                      FStar_Syntax_Syntax.sigmeta = uu____11337;
                      FStar_Syntax_Syntax.sigattrs = uu____11338;_},
                    FStar_Pervasives_Native.None)
                   ->
                   (match tps with
                    | [] ->
                        let uu____11377 =
                          let uu____11386 = inst_tscheme1 (uvs, k) in
                          (uu____11386, rng) in
                        FStar_Pervasives_Native.Some uu____11377
                    | uu____11403 ->
                        let uu____11404 =
                          let uu____11413 =
                            let uu____11418 =
                              let uu____11419 =
                                let uu____11422 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____11422 in
                              (uvs, uu____11419) in
                            inst_tscheme1 uu____11418 in
                          (uu____11413, rng) in
                        FStar_Pervasives_Native.Some uu____11404)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1, uvs, tps, k, uu____11443, uu____11444);
                      FStar_Syntax_Syntax.sigrng = uu____11445;
                      FStar_Syntax_Syntax.sigquals = uu____11446;
                      FStar_Syntax_Syntax.sigmeta = uu____11447;
                      FStar_Syntax_Syntax.sigattrs = uu____11448;_},
                    FStar_Pervasives_Native.Some us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____11488 =
                          let uu____11497 = inst_tscheme_with (uvs, k) us in
                          (uu____11497, rng) in
                        FStar_Pervasives_Native.Some uu____11488
                    | uu____11514 ->
                        let uu____11515 =
                          let uu____11524 =
                            let uu____11529 =
                              let uu____11530 =
                                let uu____11533 =
                                  FStar_Syntax_Syntax.mk_Total k in
                                FStar_Syntax_Util.flat_arrow tps uu____11533 in
                              (uvs, uu____11530) in
                            inst_tscheme_with uu____11529 us in
                          (uu____11524, rng) in
                        FStar_Pervasives_Native.Some uu____11515)
               | FStar_Util.Inr se ->
                   let uu____11567 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____11588;
                          FStar_Syntax_Syntax.sigrng = uu____11589;
                          FStar_Syntax_Syntax.sigquals = uu____11590;
                          FStar_Syntax_Syntax.sigmeta = uu____11591;
                          FStar_Syntax_Syntax.sigattrs = uu____11592;_},
                        FStar_Pervasives_Native.None) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____11607 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se) in
                   FStar_All.pipe_right uu____11567
                     (FStar_Util.map_option
                        (fun uu____11655 ->
                           match uu____11655 with
                           | (us_t, rng1) -> (us_t, rng1)))) in
        let uu____11686 =
          let uu____11697 = lookup_qname env lid in
          FStar_Util.bind_opt uu____11697 mapper in
        match uu____11686 with
        | FStar_Pervasives_Native.Some ((us, t), r) ->
            let uu____11771 =
              let uu____11782 =
                let uu____11789 =
                  let uu___100_11792 = t in
                  let uu____11793 = FStar_Ident.range_of_lid lid in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___100_11792.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____11793;
                    FStar_Syntax_Syntax.vars =
                      (uu___100_11792.FStar_Syntax_Syntax.vars)
                  } in
                (us, uu____11789) in
              (uu____11782, r) in
            FStar_Pervasives_Native.Some uu____11771
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____11840 = lookup_qname env l in
      match uu____11840 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some uu____11859 -> true
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ, FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bv ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____11911 = try_lookup_bv env bv in
      match uu____11911 with
      | FStar_Pervasives_Native.None ->
          let uu____11926 = variable_not_found bv in
          FStar_Errors.raise_error uu____11926 bvr
      | FStar_Pervasives_Native.Some (t, r) ->
          let uu____11941 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____11942 =
            let uu____11943 = FStar_Range.use_range bvr in
            FStar_Range.set_use_range r uu____11943 in
          (uu____11941, uu____11942)
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      let uu____11964 = try_lookup_lid_aux FStar_Pervasives_Native.None env l in
      match uu____11964 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us, t), r) ->
          let use_range1 = FStar_Ident.range_of_lid l in
          let r1 =
            let uu____12030 = FStar_Range.use_range use_range1 in
            FStar_Range.set_use_range r uu____12030 in
          let uu____12031 =
            let uu____12040 =
              let uu____12045 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (us, uu____12045) in
            (uu____12040, r1) in
          FStar_Pervasives_Native.Some uu____12031
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ, FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun us ->
      fun l ->
        let uu____12079 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l in
        match uu____12079 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12112, t), r) ->
            let use_range1 = FStar_Ident.range_of_lid l in
            let r1 =
              let uu____12137 = FStar_Range.use_range use_range1 in
              FStar_Range.set_use_range r uu____12137 in
            let uu____12138 =
              let uu____12143 = FStar_Syntax_Subst.set_use_range use_range1 t in
              (uu____12143, r1) in
            FStar_Pervasives_Native.Some uu____12138
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,
        FStar_Range.range) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun l ->
      let uu____12166 = try_lookup_lid env l in
      match uu____12166 with
      | FStar_Pervasives_Native.None ->
          let uu____12193 = name_not_found l in
          let uu____12198 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____12193 uu____12198
      | FStar_Pervasives_Native.Some v1 -> v1
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env ->
    fun x ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___80_12238 ->
              match uu___80_12238 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12240 -> false) env.gamma) FStar_Option.isSome
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme, FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____12259 = lookup_qname env lid in
      match uu____12259 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12268, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____12271;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12273;
              FStar_Syntax_Syntax.sigattrs = uu____12274;_},
            FStar_Pervasives_Native.None),
           uu____12275)
          ->
          let uu____12324 =
            let uu____12335 =
              let uu____12340 =
                let uu____12341 = FStar_Ident.range_of_lid lid in
                FStar_Syntax_Subst.set_use_range uu____12341 t in
              (uvs, uu____12340) in
            (uu____12335, q) in
          FStar_Pervasives_Native.Some uu____12324
      | uu____12358 -> FStar_Pervasives_Native.None
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____12379 = lookup_qname env lid in
      match uu____12379 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12384, uvs, t);
              FStar_Syntax_Syntax.sigrng = uu____12387;
              FStar_Syntax_Syntax.sigquals = uu____12388;
              FStar_Syntax_Syntax.sigmeta = uu____12389;
              FStar_Syntax_Syntax.sigattrs = uu____12390;_},
            FStar_Pervasives_Native.None),
           uu____12391)
          ->
          let uu____12440 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____12440 (uvs, t)
      | uu____12441 ->
          let uu____12442 = name_not_found lid in
          let uu____12447 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____12442 uu____12447
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes, FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____12466 = lookup_qname env lid in
      match uu____12466 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12471, uvs, t, uu____12474, uu____12475, uu____12476);
              FStar_Syntax_Syntax.sigrng = uu____12477;
              FStar_Syntax_Syntax.sigquals = uu____12478;
              FStar_Syntax_Syntax.sigmeta = uu____12479;
              FStar_Syntax_Syntax.sigattrs = uu____12480;_},
            FStar_Pervasives_Native.None),
           uu____12481)
          ->
          let uu____12534 = FStar_Ident.range_of_lid lid in
          inst_tscheme_with_range uu____12534 (uvs, t)
      | uu____12535 ->
          let uu____12536 = name_not_found lid in
          let uu____12541 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____12536 uu____12541
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool, FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun lid ->
      let uu____12562 = lookup_qname env lid in
      match uu____12562 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12569, uu____12570, uu____12571, uu____12572,
                 uu____12573, dcs);
              FStar_Syntax_Syntax.sigrng = uu____12575;
              FStar_Syntax_Syntax.sigquals = uu____12576;
              FStar_Syntax_Syntax.sigmeta = uu____12577;
              FStar_Syntax_Syntax.sigattrs = uu____12578;_},
            uu____12579),
           uu____12580)
          -> (true, dcs)
      | uu____12641 -> (false, [])
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      let uu____12654 = lookup_qname env lid in
      match uu____12654 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12655, uu____12656, uu____12657, l, uu____12659,
                 uu____12660);
              FStar_Syntax_Syntax.sigrng = uu____12661;
              FStar_Syntax_Syntax.sigquals = uu____12662;
              FStar_Syntax_Syntax.sigmeta = uu____12663;
              FStar_Syntax_Syntax.sigattrs = uu____12664;_},
            uu____12665),
           uu____12666)
          -> l
      | uu____12721 ->
          let uu____12722 =
            let uu____12723 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____12723 in
          failwith uu____12722
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun lid ->
      fun qninfo ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        match qninfo with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____12772)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____12823, lbs), uu____12825)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____12853 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____12853
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____12885 -> FStar_Pervasives_Native.None)
        | uu____12890 -> FStar_Pervasives_Native.None
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names, FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels ->
    fun env ->
      fun lid ->
        let uu____12920 = lookup_qname env lid in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____12920
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se, uu____12945), uu____12946) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____12995 -> FStar_Pervasives_Native.None
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env ->
    fun lid ->
      let uu____13016 = lookup_qname env lid in
      FStar_All.pipe_left attrs_of_qninfo uu____13016
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ftv ->
      let uu____13035 = lookup_qname env ftv in
      match uu____13035 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____13039) ->
          let uu____13084 = effect_signature FStar_Pervasives_Native.None se in
          (match uu____13084 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13105, t), r) ->
               let uu____13120 =
                 let uu____13121 = FStar_Ident.range_of_lid ftv in
                 FStar_Syntax_Subst.set_use_range uu____13121 t in
               FStar_Pervasives_Native.Some uu____13120)
      | uu____13122 -> FStar_Pervasives_Native.None
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun ftv ->
      let uu____13133 = try_lookup_effect_lid env ftv in
      match uu____13133 with
      | FStar_Pervasives_Native.None ->
          let uu____13136 = name_not_found ftv in
          let uu____13141 = FStar_Ident.range_of_lid ftv in
          FStar_Errors.raise_error uu____13136 uu____13141
      | FStar_Pervasives_Native.Some k -> k
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders, FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun univ_insts ->
      fun lid0 ->
        let uu____13164 = lookup_qname env lid0 in
        match uu____13164 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid, univs1, binders, c, uu____13175);
                FStar_Syntax_Syntax.sigrng = uu____13176;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13178;
                FStar_Syntax_Syntax.sigattrs = uu____13179;_},
              FStar_Pervasives_Native.None),
             uu____13180)
            ->
            let lid1 =
              let uu____13234 =
                let uu____13235 = FStar_Ident.range_of_lid lid in
                let uu____13236 =
                  let uu____13237 = FStar_Ident.range_of_lid lid0 in
                  FStar_Range.use_range uu____13237 in
                FStar_Range.set_use_range uu____13235 uu____13236 in
              FStar_Ident.set_lid_range lid uu____13234 in
            let uu____13238 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___81_13242 ->
                      match uu___81_13242 with
                      | FStar_Syntax_Syntax.Irreducible -> true
                      | uu____13243 -> false)) in
            if uu____13238
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13257 =
                      let uu____13258 =
                        let uu____13259 = get_range env in
                        FStar_Range.string_of_range uu____13259 in
                      let uu____13260 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____13261 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13258 uu____13260 uu____13261 in
                    failwith uu____13257) in
               match (binders, univs1) with
               | ([], uu____13268) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____13285, uu____13286::uu____13287::uu____13288) ->
                   let uu____13293 =
                     let uu____13294 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____13295 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____13294 uu____13295 in
                   failwith uu____13293
               | uu____13302 ->
                   let uu____13307 =
                     let uu____13312 =
                       let uu____13313 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____13313) in
                     inst_tscheme_with uu____13312 insts in
                   (match uu____13307 with
                    | (uu____13324, t) ->
                        let t1 =
                          let uu____13327 = FStar_Ident.range_of_lid lid1 in
                          FStar_Syntax_Subst.set_use_range uu____13327 t in
                        let uu____13328 =
                          let uu____13329 = FStar_Syntax_Subst.compress t1 in
                          uu____13329.FStar_Syntax_Syntax.n in
                        (match uu____13328 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____13376 -> failwith "Impossible")))
        | uu____13383 -> FStar_Pervasives_Native.None
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env ->
    fun l ->
      let rec find1 l1 =
        let uu____13406 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____13406 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____13419, c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____13426 = find1 l2 in
            (match uu____13426 with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____13433 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str in
        match uu____13433 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None ->
            let uu____13437 = find1 l in
            (match uu____13437 with
             | FStar_Pervasives_Native.None -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m)) in
      let uu____13442 = FStar_Ident.range_of_lid l in
      FStar_Ident.set_lid_range res uu____13442
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env ->
    fun l ->
      let l1 = norm_eff_name env l in
      let uu____13456 = lookup_qname env l1 in
      match uu____13456 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____13459;
              FStar_Syntax_Syntax.sigrng = uu____13460;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13462;
              FStar_Syntax_Syntax.sigattrs = uu____13463;_},
            uu____13464),
           uu____13465)
          -> q
      | uu____13516 -> []
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env ->
    fun lid ->
      fun i ->
        let fail1 uu____13537 =
          let uu____13538 =
            let uu____13539 = FStar_Util.string_of_int i in
            let uu____13540 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____13539 uu____13540 in
          failwith uu____13538 in
        let uu____13541 = lookup_datacon env lid in
        match uu____13541 with
        | (uu____13546, t) ->
            let uu____13548 =
              let uu____13549 = FStar_Syntax_Subst.compress t in
              uu____13549.FStar_Syntax_Syntax.n in
            (match uu____13548 with
             | FStar_Syntax_Syntax.Tm_arrow (binders, uu____13553) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____13584 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____13584
                      FStar_Pervasives_Native.fst)
             | uu____13593 -> fail1 ())
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____13604 = lookup_qname env l in
      match uu____13604 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13605, uu____13606, uu____13607);
              FStar_Syntax_Syntax.sigrng = uu____13608;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13610;
              FStar_Syntax_Syntax.sigattrs = uu____13611;_},
            uu____13612),
           uu____13613)
          ->
          FStar_Util.for_some
            (fun uu___82_13666 ->
               match uu___82_13666 with
               | FStar_Syntax_Syntax.Projector uu____13667 -> true
               | uu____13672 -> false) quals
      | uu____13673 -> false
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____13684 = lookup_qname env lid in
      match uu____13684 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13685, uu____13686, uu____13687, uu____13688,
                 uu____13689, uu____13690);
              FStar_Syntax_Syntax.sigrng = uu____13691;
              FStar_Syntax_Syntax.sigquals = uu____13692;
              FStar_Syntax_Syntax.sigmeta = uu____13693;
              FStar_Syntax_Syntax.sigattrs = uu____13694;_},
            uu____13695),
           uu____13696)
          -> true
      | uu____13751 -> false
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____13762 = lookup_qname env lid in
      match uu____13762 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13763, uu____13764, uu____13765, uu____13766,
                 uu____13767, uu____13768);
              FStar_Syntax_Syntax.sigrng = uu____13769;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13771;
              FStar_Syntax_Syntax.sigattrs = uu____13772;_},
            uu____13773),
           uu____13774)
          ->
          FStar_Util.for_some
            (fun uu___83_13835 ->
               match uu___83_13835 with
               | FStar_Syntax_Syntax.RecordType uu____13836 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____13845 -> true
               | uu____13854 -> false) quals
      | uu____13855 -> false
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____13861, uu____13862);
            FStar_Syntax_Syntax.sigrng = uu____13863;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____13865;
            FStar_Syntax_Syntax.sigattrs = uu____13866;_},
          uu____13867),
         uu____13868)
        ->
        FStar_Util.for_some
          (fun uu___84_13925 ->
             match uu___84_13925 with
             | FStar_Syntax_Syntax.Action uu____13926 -> true
             | uu____13927 -> false) quals
    | uu____13928 -> false
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____13939 = lookup_qname env lid in
      FStar_All.pipe_left qninfo_is_action uu____13939
let (is_interpreted : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
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
  fun env ->
    fun head1 ->
      let uu____13953 =
        let uu____13954 = FStar_Syntax_Util.un_uinst head1 in
        uu____13954.FStar_Syntax_Syntax.n in
      match uu____13953 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____13958 -> false
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun l ->
      let uu____13969 = lookup_qname env l in
      match uu____13969 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se, uu____13971), uu____13972) ->
          FStar_Util.for_some
            (fun uu___85_14020 ->
               match uu___85_14020 with
               | FStar_Syntax_Syntax.Irreducible -> true
               | uu____14021 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14022 -> false
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14093 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se, uu____14109) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14126 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14133 ->
                 FStar_Pervasives_Native.Some true
             | uu____14150 -> FStar_Pervasives_Native.Some false) in
      let uu____14151 =
        let uu____14154 = lookup_qname env lid in
        FStar_Util.bind_opt uu____14154 mapper in
      match uu____14151 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None -> false
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env ->
    fun lid ->
      let uu____14204 = lookup_qname env lid in
      match uu____14204 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14205, uu____14206, tps, uu____14208, uu____14209,
                 uu____14210);
              FStar_Syntax_Syntax.sigrng = uu____14211;
              FStar_Syntax_Syntax.sigquals = uu____14212;
              FStar_Syntax_Syntax.sigmeta = uu____14213;
              FStar_Syntax_Syntax.sigattrs = uu____14214;_},
            uu____14215),
           uu____14216)
          -> FStar_List.length tps
      | uu____14279 ->
          let uu____14280 = name_not_found lid in
          let uu____14285 = FStar_Ident.range_of_lid lid in
          FStar_Errors.raise_error uu____14280 uu____14285
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,
        FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____14329 ->
              match uu____14329 with
              | (d, uu____14337) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env ->
    fun l ->
      let uu____14352 = effect_decl_opt env l in
      match uu____14352 with
      | FStar_Pervasives_Native.None ->
          let uu____14367 = name_not_found l in
          let uu____14372 = FStar_Ident.range_of_lid l in
          FStar_Errors.raise_error uu____14367 uu____14372
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____14394 -> fun t -> fun wp -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____14413 ->
            fun t -> fun wp -> fun e -> FStar_Util.return_all e))
  }
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident, mlift, mlift) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun l1 ->
      fun l2 ->
        let uu____14444 = FStar_Ident.lid_equals l1 l2 in
        if uu____14444
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____14452 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid)) in
           if uu____14452
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____14460 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____14513 ->
                        match uu____14513 with
                        | (m1, m2, uu____14526, uu____14527, uu____14528) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2))) in
              match uu____14460 with
              | FStar_Pervasives_Native.None ->
                  let uu____14545 =
                    let uu____14550 =
                      let uu____14551 = FStar_Syntax_Print.lid_to_string l1 in
                      let uu____14552 = FStar_Syntax_Print.lid_to_string l2 in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____14551
                        uu____14552 in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____14550) in
                  FStar_Errors.raise_error uu____14545 env.range
              | FStar_Pervasives_Native.Some
                  (uu____14559, uu____14560, m3, j1, j2) -> (m3, j1, j2)))
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env ->
    fun l1 ->
      fun l2 ->
        let uu____14593 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)) in
        if uu____14593
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux :
  'Auu____14609 .
    (FStar_Syntax_Syntax.eff_decl, 'Auu____14609)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls ->
    fun m ->
      let uu____14638 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____14664 ->
                match uu____14664 with
                | (d, uu____14670) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
      match uu____14638 with
      | FStar_Pervasives_Native.None ->
          let uu____14681 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str in
          failwith uu____14681
      | FStar_Pervasives_Native.Some (md, _q) ->
          let uu____14694 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature)) in
          (match uu____14694 with
           | (uu____14705, s) ->
               let s1 = FStar_Syntax_Subst.compress s in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([], FStar_Syntax_Syntax.Tm_arrow
                   ((a, uu____14715)::(wp, uu____14717)::[], c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____14753 -> failwith "Impossible"))
let (wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  = fun env -> fun m -> wp_sig_aux (env.effects).decls m
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env ->
    fun eff_name ->
      fun res_u ->
        fun res_t ->
          let uu____14800 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid in
          if uu____14800
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____14802 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid in
             if uu____14802
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
                  let uu____14810 = get_range env in
                  let uu____14811 =
                    let uu____14818 =
                      let uu____14819 =
                        let uu____14834 =
                          let uu____14837 = FStar_Syntax_Syntax.as_arg res_t in
                          [uu____14837] in
                        (null_wp, uu____14834) in
                      FStar_Syntax_Syntax.Tm_app uu____14819 in
                    FStar_Syntax_Syntax.mk uu____14818 in
                  uu____14811 FStar_Pervasives_Native.None uu____14810 in
                let uu____14843 =
                  let uu____14844 =
                    let uu____14853 = FStar_Syntax_Syntax.as_arg null_wp_res in
                    [uu____14853] in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____14844;
                    FStar_Syntax_Syntax.flags = []
                  } in
                FStar_Syntax_Syntax.mk_Comp uu____14843))
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___101_14866 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___101_14866.order);
              joins = (uu___101_14866.joins)
            } in
          let uu___102_14875 = env in
          {
            solver = (uu___102_14875.solver);
            range = (uu___102_14875.range);
            curmodule = (uu___102_14875.curmodule);
            gamma = (uu___102_14875.gamma);
            gamma_cache = (uu___102_14875.gamma_cache);
            modules = (uu___102_14875.modules);
            expected_typ = (uu___102_14875.expected_typ);
            sigtab = (uu___102_14875.sigtab);
            is_pattern = (uu___102_14875.is_pattern);
            instantiate_imp = (uu___102_14875.instantiate_imp);
            effects;
            generalize = (uu___102_14875.generalize);
            letrecs = (uu___102_14875.letrecs);
            top_level = (uu___102_14875.top_level);
            check_uvars = (uu___102_14875.check_uvars);
            use_eq = (uu___102_14875.use_eq);
            is_iface = (uu___102_14875.is_iface);
            admit = (uu___102_14875.admit);
            lax = (uu___102_14875.lax);
            lax_universes = (uu___102_14875.lax_universes);
            failhard = (uu___102_14875.failhard);
            nosynth = (uu___102_14875.nosynth);
            tc_term = (uu___102_14875.tc_term);
            type_of = (uu___102_14875.type_of);
            universe_of = (uu___102_14875.universe_of);
            check_type_of = (uu___102_14875.check_type_of);
            use_bv_sorts = (uu___102_14875.use_bv_sorts);
            qtbl_name_and_index = (uu___102_14875.qtbl_name_and_index);
            normalized_eff_names = (uu___102_14875.normalized_eff_names);
            proof_ns = (uu___102_14875.proof_ns);
            synth_hook = (uu___102_14875.synth_hook);
            splice = (uu___102_14875.splice);
            is_native_tactic = (uu___102_14875.is_native_tactic);
            identifier_info = (uu___102_14875.identifier_info);
            tc_hooks = (uu___102_14875.tc_hooks);
            dsenv = (uu___102_14875.dsenv);
            dep_graph = (uu___102_14875.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____14905 = (e1.mlift).mlift_wp u r wp1 in
                (e2.mlift).mlift_wp u r uu____14905 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some l1,
                   FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u ->
                          fun t ->
                            fun wp ->
                              fun e ->
                                let uu____15063 = (e1.mlift).mlift_wp u t wp in
                                let uu____15064 = l1 u t wp e in
                                l2 u t uu____15063 uu____15064))
                | uu____15065 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15133 = inst_tscheme_with lift_t [u] in
            match uu____15133 with
            | (uu____15140, lift_t1) ->
                let uu____15142 =
                  let uu____15149 =
                    let uu____15150 =
                      let uu____15165 =
                        let uu____15168 = FStar_Syntax_Syntax.as_arg r in
                        let uu____15169 =
                          let uu____15172 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____15172] in
                        uu____15168 :: uu____15169 in
                      (lift_t1, uu____15165) in
                    FStar_Syntax_Syntax.Tm_app uu____15150 in
                  FStar_Syntax_Syntax.mk uu____15149 in
                uu____15142 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____15244 = inst_tscheme_with lift_t [u] in
            match uu____15244 with
            | (uu____15251, lift_t1) ->
                let uu____15253 =
                  let uu____15260 =
                    let uu____15261 =
                      let uu____15276 =
                        let uu____15279 = FStar_Syntax_Syntax.as_arg r in
                        let uu____15280 =
                          let uu____15283 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____15284 =
                            let uu____15287 = FStar_Syntax_Syntax.as_arg e in
                            [uu____15287] in
                          uu____15283 :: uu____15284 in
                        uu____15279 :: uu____15280 in
                      (lift_t1, uu____15276) in
                    FStar_Syntax_Syntax.Tm_app uu____15261 in
                  FStar_Syntax_Syntax.mk uu____15260 in
                uu____15253 FStar_Pervasives_Native.None
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
              let uu____15343 =
                let uu____15344 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____15344
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____15343 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____15348 =
              let uu____15349 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp in
              FStar_Syntax_Print.term_to_string uu____15349 in
            let uu____15350 =
              let uu____15351 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1 ->
                     let uu____15377 = l1 FStar_Syntax_Syntax.U_zero arg wp e in
                     FStar_Syntax_Print.term_to_string uu____15377) in
              FStar_Util.dflt "none" uu____15351 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____15348
              uu____15350 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____15403 ->
                    match uu____15403 with
                    | (e, uu____15411) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____15434 =
            match uu____15434 with
            | (i, j) ->
                let uu____15445 = FStar_Ident.lid_equals i j in
                if uu____15445
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_17 -> FStar_Pervasives_Native.Some _0_17)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____15477 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i ->
                        let uu____15487 = FStar_Ident.lid_equals i k in
                        if uu____15487
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j ->
                                  let uu____15498 =
                                    FStar_Ident.lid_equals j k in
                                  if uu____15498
                                  then []
                                  else
                                    (let uu____15502 =
                                       let uu____15511 =
                                         find_edge order1 (i, k) in
                                       let uu____15514 =
                                         find_edge order1 (k, j) in
                                       (uu____15511, uu____15514) in
                                     match uu____15502 with
                                     | (FStar_Pervasives_Native.Some e1,
                                        FStar_Pervasives_Native.Some e2) ->
                                         let uu____15529 =
                                           compose_edges e1 e2 in
                                         [uu____15529]
                                     | uu____15530 -> []))))) in
              FStar_List.append order1 uu____15477 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1 ->
                 fun e2 ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1 ->
                   let uu____15560 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____15562 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____15562
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____15560
                   then
                     let uu____15567 =
                       let uu____15572 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____15572) in
                     let uu____15573 = get_range env in
                     FStar_Errors.raise_error uu____15567 uu____15573
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j ->
                              let join_opt =
                                let uu____15650 = FStar_Ident.lid_equals i j in
                                if uu____15650
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt ->
                                          fun k ->
                                            let uu____15699 =
                                              let uu____15708 =
                                                find_edge order2 (i, k) in
                                              let uu____15711 =
                                                find_edge order2 (j, k) in
                                              (uu____15708, uu____15711) in
                                            match uu____15699 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,
                                               FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub, uu____15753,
                                                      uu____15754)
                                                     ->
                                                     let uu____15761 =
                                                       let uu____15766 =
                                                         let uu____15767 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____15767 in
                                                       let uu____15770 =
                                                         let uu____15771 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____15771 in
                                                       (uu____15766,
                                                         uu____15770) in
                                                     (match uu____15761 with
                                                      | (true, true) ->
                                                          let uu____15782 =
                                                            FStar_Ident.lid_equals
                                                              k ub in
                                                          if uu____15782
                                                          then
                                                            (FStar_Errors.log_issue
                                                               FStar_Range.dummyRange
                                                               (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                 "Looking multiple times at the same upper bound candidate");
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false, false) ->
                                                          bopt
                                                      | (true, false) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false, true) -> bopt))
                                            | uu____15807 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None -> []
                              | FStar_Pervasives_Native.Some (k, e1, e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___103_15880 = env.effects in
              { decls = (uu___103_15880.decls); order = order2; joins } in
            let uu___104_15881 = env in
            {
              solver = (uu___104_15881.solver);
              range = (uu___104_15881.range);
              curmodule = (uu___104_15881.curmodule);
              gamma = (uu___104_15881.gamma);
              gamma_cache = (uu___104_15881.gamma_cache);
              modules = (uu___104_15881.modules);
              expected_typ = (uu___104_15881.expected_typ);
              sigtab = (uu___104_15881.sigtab);
              is_pattern = (uu___104_15881.is_pattern);
              instantiate_imp = (uu___104_15881.instantiate_imp);
              effects;
              generalize = (uu___104_15881.generalize);
              letrecs = (uu___104_15881.letrecs);
              top_level = (uu___104_15881.top_level);
              check_uvars = (uu___104_15881.check_uvars);
              use_eq = (uu___104_15881.use_eq);
              is_iface = (uu___104_15881.is_iface);
              admit = (uu___104_15881.admit);
              lax = (uu___104_15881.lax);
              lax_universes = (uu___104_15881.lax_universes);
              failhard = (uu___104_15881.failhard);
              nosynth = (uu___104_15881.nosynth);
              tc_term = (uu___104_15881.tc_term);
              type_of = (uu___104_15881.type_of);
              universe_of = (uu___104_15881.universe_of);
              check_type_of = (uu___104_15881.check_type_of);
              use_bv_sorts = (uu___104_15881.use_bv_sorts);
              qtbl_name_and_index = (uu___104_15881.qtbl_name_and_index);
              normalized_eff_names = (uu___104_15881.normalized_eff_names);
              proof_ns = (uu___104_15881.proof_ns);
              synth_hook = (uu___104_15881.synth_hook);
              splice = (uu___104_15881.splice);
              is_native_tactic = (uu___104_15881.is_native_tactic);
              identifier_info = (uu___104_15881.identifier_info);
              tc_hooks = (uu___104_15881.tc_hooks);
              dsenv = (uu___104_15881.dsenv);
              dep_graph = (uu___104_15881.dep_graph)
            }))
      | uu____15882 -> env
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env ->
    fun c ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____15910 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env ->
    fun comp ->
      let c = comp_to_comp_typ env comp in
      let uu____15922 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____15922 with
      | FStar_Pervasives_Native.None -> c
      | FStar_Pervasives_Native.Some (binders, cdef) ->
          let uu____15939 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____15939 with
           | (binders1, cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____15957 =
                     let uu____15962 =
                       let uu____15963 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1) in
                       let uu____15968 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1")) in
                       let uu____15975 =
                         let uu____15976 = FStar_Syntax_Syntax.mk_Comp c in
                         FStar_Syntax_Print.comp_to_string uu____15976 in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____15963 uu____15968 uu____15975 in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____15962) in
                   FStar_Errors.raise_error uu____15957
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____15981 =
                     let uu____15990 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____15990 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____16007 ->
                        fun uu____16008 ->
                          match (uu____16007, uu____16008) with
                          | ((x, uu____16030), (t, uu____16032)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____15981 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____16051 =
                     let uu___105_16052 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___105_16052.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___105_16052.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___105_16052.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___105_16052.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____16051
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let (effect_repr_aux :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option)
  =
  fun only_reifiable ->
    fun env ->
      fun c ->
        fun u_c ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
          let uu____16082 = effect_decl_opt env effect_name in
          match uu____16082 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed, qualifiers) ->
              let uu____16115 =
                only_reifiable &&
                  (let uu____16117 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
                   Prims.op_Negation uu____16117) in
              if uu____16115
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown ->
                     FStar_Pervasives_Native.None
                 | uu____16133 ->
                     let c1 = unfold_effect_abbrev env c in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____16152 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name in
                           let message =
                             let uu____16181 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name in
                             Prims.strcat uu____16181
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].") in
                           let uu____16182 = get_range env in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____16182 in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr)) in
                     let uu____16192 =
                       let uu____16195 = get_range env in
                       let uu____16196 =
                         let uu____16203 =
                           let uu____16204 =
                             let uu____16219 =
                               let uu____16222 =
                                 FStar_Syntax_Syntax.as_arg res_typ in
                               [uu____16222; wp] in
                             (repr, uu____16219) in
                           FStar_Syntax_Syntax.Tm_app uu____16204 in
                         FStar_Syntax_Syntax.mk uu____16203 in
                       uu____16196 FStar_Pervasives_Native.None uu____16195 in
                     FStar_Pervasives_Native.Some uu____16192)
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env -> fun c -> fun u_c -> effect_repr_aux false env c u_c
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun c ->
      fun u_c ->
        let no_reify l =
          let uu____16282 =
            let uu____16287 =
              let uu____16288 = FStar_Ident.string_of_lid l in
              FStar_Util.format1 "Effect %s cannot be reified" uu____16288 in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____16287) in
          let uu____16289 = get_range env in
          FStar_Errors.raise_error uu____16282 uu____16289 in
        let uu____16290 = effect_repr_aux true env c u_c in
        match uu____16290 with
        | FStar_Pervasives_Native.None ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun effect_lid ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let (is_reifiable : env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env ->
    fun c -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____16336 -> false
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____16347 =
        let uu____16348 = FStar_Syntax_Subst.compress t in
        uu____16348.FStar_Syntax_Syntax.n in
      match uu____16347 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____16351, c) ->
          is_reifiable_comp env c
      | uu____16369 -> false
let (push_in_gamma : env -> binding -> env) =
  fun env ->
    fun s ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____16399)::uu____16400 -> x :: rest
        | (Binding_sig_inst uu____16409)::uu____16410 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____16425 = push1 x rest1 in local :: uu____16425 in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___106_16429 = env in
       let uu____16430 = push1 s env.gamma in
       {
         solver = (uu___106_16429.solver);
         range = (uu___106_16429.range);
         curmodule = (uu___106_16429.curmodule);
         gamma = uu____16430;
         gamma_cache = (uu___106_16429.gamma_cache);
         modules = (uu___106_16429.modules);
         expected_typ = (uu___106_16429.expected_typ);
         sigtab = (uu___106_16429.sigtab);
         is_pattern = (uu___106_16429.is_pattern);
         instantiate_imp = (uu___106_16429.instantiate_imp);
         effects = (uu___106_16429.effects);
         generalize = (uu___106_16429.generalize);
         letrecs = (uu___106_16429.letrecs);
         top_level = (uu___106_16429.top_level);
         check_uvars = (uu___106_16429.check_uvars);
         use_eq = (uu___106_16429.use_eq);
         is_iface = (uu___106_16429.is_iface);
         admit = (uu___106_16429.admit);
         lax = (uu___106_16429.lax);
         lax_universes = (uu___106_16429.lax_universes);
         failhard = (uu___106_16429.failhard);
         nosynth = (uu___106_16429.nosynth);
         tc_term = (uu___106_16429.tc_term);
         type_of = (uu___106_16429.type_of);
         universe_of = (uu___106_16429.universe_of);
         check_type_of = (uu___106_16429.check_type_of);
         use_bv_sorts = (uu___106_16429.use_bv_sorts);
         qtbl_name_and_index = (uu___106_16429.qtbl_name_and_index);
         normalized_eff_names = (uu___106_16429.normalized_eff_names);
         proof_ns = (uu___106_16429.proof_ns);
         synth_hook = (uu___106_16429.synth_hook);
         splice = (uu___106_16429.splice);
         is_native_tactic = (uu___106_16429.is_native_tactic);
         identifier_info = (uu___106_16429.identifier_info);
         tc_hooks = (uu___106_16429.tc_hooks);
         dsenv = (uu___106_16429.dsenv);
         dep_graph = (uu___106_16429.dep_graph)
       })
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env ->
    fun s ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let (push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env)
  =
  fun env ->
    fun s ->
      fun us ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let (push_local_binding : env -> binding -> env) =
  fun env ->
    fun b ->
      let uu___107_16474 = env in
      {
        solver = (uu___107_16474.solver);
        range = (uu___107_16474.range);
        curmodule = (uu___107_16474.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___107_16474.gamma_cache);
        modules = (uu___107_16474.modules);
        expected_typ = (uu___107_16474.expected_typ);
        sigtab = (uu___107_16474.sigtab);
        is_pattern = (uu___107_16474.is_pattern);
        instantiate_imp = (uu___107_16474.instantiate_imp);
        effects = (uu___107_16474.effects);
        generalize = (uu___107_16474.generalize);
        letrecs = (uu___107_16474.letrecs);
        top_level = (uu___107_16474.top_level);
        check_uvars = (uu___107_16474.check_uvars);
        use_eq = (uu___107_16474.use_eq);
        is_iface = (uu___107_16474.is_iface);
        admit = (uu___107_16474.admit);
        lax = (uu___107_16474.lax);
        lax_universes = (uu___107_16474.lax_universes);
        failhard = (uu___107_16474.failhard);
        nosynth = (uu___107_16474.nosynth);
        tc_term = (uu___107_16474.tc_term);
        type_of = (uu___107_16474.type_of);
        universe_of = (uu___107_16474.universe_of);
        check_type_of = (uu___107_16474.check_type_of);
        use_bv_sorts = (uu___107_16474.use_bv_sorts);
        qtbl_name_and_index = (uu___107_16474.qtbl_name_and_index);
        normalized_eff_names = (uu___107_16474.normalized_eff_names);
        proof_ns = (uu___107_16474.proof_ns);
        synth_hook = (uu___107_16474.synth_hook);
        splice = (uu___107_16474.splice);
        is_native_tactic = (uu___107_16474.is_native_tactic);
        identifier_info = (uu___107_16474.identifier_info);
        tc_hooks = (uu___107_16474.tc_hooks);
        dsenv = (uu___107_16474.dsenv);
        dep_graph = (uu___107_16474.dep_graph)
      }
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env -> fun x -> push_local_binding env (Binding_var x)
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env ->
    fun bvs ->
      FStar_List.fold_left (fun env1 -> fun bv -> push_bv env1 bv) env bvs
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv, env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___108_16529 = env in
             {
               solver = (uu___108_16529.solver);
               range = (uu___108_16529.range);
               curmodule = (uu___108_16529.curmodule);
               gamma = rest;
               gamma_cache = (uu___108_16529.gamma_cache);
               modules = (uu___108_16529.modules);
               expected_typ = (uu___108_16529.expected_typ);
               sigtab = (uu___108_16529.sigtab);
               is_pattern = (uu___108_16529.is_pattern);
               instantiate_imp = (uu___108_16529.instantiate_imp);
               effects = (uu___108_16529.effects);
               generalize = (uu___108_16529.generalize);
               letrecs = (uu___108_16529.letrecs);
               top_level = (uu___108_16529.top_level);
               check_uvars = (uu___108_16529.check_uvars);
               use_eq = (uu___108_16529.use_eq);
               is_iface = (uu___108_16529.is_iface);
               admit = (uu___108_16529.admit);
               lax = (uu___108_16529.lax);
               lax_universes = (uu___108_16529.lax_universes);
               failhard = (uu___108_16529.failhard);
               nosynth = (uu___108_16529.nosynth);
               tc_term = (uu___108_16529.tc_term);
               type_of = (uu___108_16529.type_of);
               universe_of = (uu___108_16529.universe_of);
               check_type_of = (uu___108_16529.check_type_of);
               use_bv_sorts = (uu___108_16529.use_bv_sorts);
               qtbl_name_and_index = (uu___108_16529.qtbl_name_and_index);
               normalized_eff_names = (uu___108_16529.normalized_eff_names);
               proof_ns = (uu___108_16529.proof_ns);
               synth_hook = (uu___108_16529.synth_hook);
               splice = (uu___108_16529.splice);
               is_native_tactic = (uu___108_16529.is_native_tactic);
               identifier_info = (uu___108_16529.identifier_info);
               tc_hooks = (uu___108_16529.tc_hooks);
               dsenv = (uu___108_16529.dsenv);
               dep_graph = (uu___108_16529.dep_graph)
             }))
    | uu____16530 -> FStar_Pervasives_Native.None
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env ->
    fun bs ->
      FStar_List.fold_left
        (fun env1 ->
           fun uu____16556 ->
             match uu____16556 with | (x, uu____16562) -> push_bv env1 x) env
        bs
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding)
  =
  fun x ->
    fun t ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___109_16592 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___109_16592.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___109_16592.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env -> fun lb -> fun ts -> push_local_binding env (binding_of_lb lb ts)
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env ->
    fun m ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___110_16632 = env in
       {
         solver = (uu___110_16632.solver);
         range = (uu___110_16632.range);
         curmodule = (uu___110_16632.curmodule);
         gamma = [];
         gamma_cache = (uu___110_16632.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___110_16632.sigtab);
         is_pattern = (uu___110_16632.is_pattern);
         instantiate_imp = (uu___110_16632.instantiate_imp);
         effects = (uu___110_16632.effects);
         generalize = (uu___110_16632.generalize);
         letrecs = (uu___110_16632.letrecs);
         top_level = (uu___110_16632.top_level);
         check_uvars = (uu___110_16632.check_uvars);
         use_eq = (uu___110_16632.use_eq);
         is_iface = (uu___110_16632.is_iface);
         admit = (uu___110_16632.admit);
         lax = (uu___110_16632.lax);
         lax_universes = (uu___110_16632.lax_universes);
         failhard = (uu___110_16632.failhard);
         nosynth = (uu___110_16632.nosynth);
         tc_term = (uu___110_16632.tc_term);
         type_of = (uu___110_16632.type_of);
         universe_of = (uu___110_16632.universe_of);
         check_type_of = (uu___110_16632.check_type_of);
         use_bv_sorts = (uu___110_16632.use_bv_sorts);
         qtbl_name_and_index = (uu___110_16632.qtbl_name_and_index);
         normalized_eff_names = (uu___110_16632.normalized_eff_names);
         proof_ns = (uu___110_16632.proof_ns);
         synth_hook = (uu___110_16632.synth_hook);
         splice = (uu___110_16632.splice);
         is_native_tactic = (uu___110_16632.is_native_tactic);
         identifier_info = (uu___110_16632.identifier_info);
         tc_hooks = (uu___110_16632.tc_hooks);
         dsenv = (uu___110_16632.dsenv);
         dep_graph = (uu___110_16632.dep_graph)
       })
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env ->
    fun xs ->
      FStar_List.fold_left
        (fun env1 -> fun x -> push_local_binding env1 (Binding_univ x)) env
        xs
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env, FStar_Syntax_Syntax.univ_names,
          FStar_Syntax_Syntax.term Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun uvs ->
      fun terms ->
        let uu____16674 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____16674 with
        | (univ_subst, univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____16702 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____16702)
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env ->
    fun t ->
      let uu___111_16719 = env in
      {
        solver = (uu___111_16719.solver);
        range = (uu___111_16719.range);
        curmodule = (uu___111_16719.curmodule);
        gamma = (uu___111_16719.gamma);
        gamma_cache = (uu___111_16719.gamma_cache);
        modules = (uu___111_16719.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___111_16719.sigtab);
        is_pattern = (uu___111_16719.is_pattern);
        instantiate_imp = (uu___111_16719.instantiate_imp);
        effects = (uu___111_16719.effects);
        generalize = (uu___111_16719.generalize);
        letrecs = (uu___111_16719.letrecs);
        top_level = (uu___111_16719.top_level);
        check_uvars = (uu___111_16719.check_uvars);
        use_eq = false;
        is_iface = (uu___111_16719.is_iface);
        admit = (uu___111_16719.admit);
        lax = (uu___111_16719.lax);
        lax_universes = (uu___111_16719.lax_universes);
        failhard = (uu___111_16719.failhard);
        nosynth = (uu___111_16719.nosynth);
        tc_term = (uu___111_16719.tc_term);
        type_of = (uu___111_16719.type_of);
        universe_of = (uu___111_16719.universe_of);
        check_type_of = (uu___111_16719.check_type_of);
        use_bv_sorts = (uu___111_16719.use_bv_sorts);
        qtbl_name_and_index = (uu___111_16719.qtbl_name_and_index);
        normalized_eff_names = (uu___111_16719.normalized_eff_names);
        proof_ns = (uu___111_16719.proof_ns);
        synth_hook = (uu___111_16719.synth_hook);
        splice = (uu___111_16719.splice);
        is_native_tactic = (uu___111_16719.is_native_tactic);
        identifier_info = (uu___111_16719.identifier_info);
        tc_hooks = (uu___111_16719.tc_hooks);
        dsenv = (uu___111_16719.dsenv);
        dep_graph = (uu___111_16719.dep_graph)
      }
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let (clear_expected_typ :
  env ->
    (env, FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun env_ ->
    let uu____16747 = expected_typ env_ in
    ((let uu___112_16753 = env_ in
      {
        solver = (uu___112_16753.solver);
        range = (uu___112_16753.range);
        curmodule = (uu___112_16753.curmodule);
        gamma = (uu___112_16753.gamma);
        gamma_cache = (uu___112_16753.gamma_cache);
        modules = (uu___112_16753.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___112_16753.sigtab);
        is_pattern = (uu___112_16753.is_pattern);
        instantiate_imp = (uu___112_16753.instantiate_imp);
        effects = (uu___112_16753.effects);
        generalize = (uu___112_16753.generalize);
        letrecs = (uu___112_16753.letrecs);
        top_level = (uu___112_16753.top_level);
        check_uvars = (uu___112_16753.check_uvars);
        use_eq = false;
        is_iface = (uu___112_16753.is_iface);
        admit = (uu___112_16753.admit);
        lax = (uu___112_16753.lax);
        lax_universes = (uu___112_16753.lax_universes);
        failhard = (uu___112_16753.failhard);
        nosynth = (uu___112_16753.nosynth);
        tc_term = (uu___112_16753.tc_term);
        type_of = (uu___112_16753.type_of);
        universe_of = (uu___112_16753.universe_of);
        check_type_of = (uu___112_16753.check_type_of);
        use_bv_sorts = (uu___112_16753.use_bv_sorts);
        qtbl_name_and_index = (uu___112_16753.qtbl_name_and_index);
        normalized_eff_names = (uu___112_16753.normalized_eff_names);
        proof_ns = (uu___112_16753.proof_ns);
        synth_hook = (uu___112_16753.synth_hook);
        splice = (uu___112_16753.splice);
        is_native_tactic = (uu___112_16753.is_native_tactic);
        identifier_info = (uu___112_16753.identifier_info);
        tc_hooks = (uu___112_16753.tc_hooks);
        dsenv = (uu___112_16753.dsenv);
        dep_graph = (uu___112_16753.dep_graph)
      }), uu____16747)
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____16763 =
      let uu____16766 = FStar_Ident.id_of_text "" in [uu____16766] in
    FStar_Ident.lid_of_ids uu____16763 in
  fun env ->
    fun m ->
      let sigs =
        let uu____16772 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____16772
        then
          let uu____16775 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___86_16785 ->
                    match uu___86_16785 with
                    | Binding_sig (uu____16788, se) -> [se]
                    | uu____16794 -> [])) in
          FStar_All.pipe_right uu____16775 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___113_16801 = env in
       {
         solver = (uu___113_16801.solver);
         range = (uu___113_16801.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___113_16801.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___113_16801.expected_typ);
         sigtab = (uu___113_16801.sigtab);
         is_pattern = (uu___113_16801.is_pattern);
         instantiate_imp = (uu___113_16801.instantiate_imp);
         effects = (uu___113_16801.effects);
         generalize = (uu___113_16801.generalize);
         letrecs = (uu___113_16801.letrecs);
         top_level = (uu___113_16801.top_level);
         check_uvars = (uu___113_16801.check_uvars);
         use_eq = (uu___113_16801.use_eq);
         is_iface = (uu___113_16801.is_iface);
         admit = (uu___113_16801.admit);
         lax = (uu___113_16801.lax);
         lax_universes = (uu___113_16801.lax_universes);
         failhard = (uu___113_16801.failhard);
         nosynth = (uu___113_16801.nosynth);
         tc_term = (uu___113_16801.tc_term);
         type_of = (uu___113_16801.type_of);
         universe_of = (uu___113_16801.universe_of);
         check_type_of = (uu___113_16801.check_type_of);
         use_bv_sorts = (uu___113_16801.use_bv_sorts);
         qtbl_name_and_index = (uu___113_16801.qtbl_name_and_index);
         normalized_eff_names = (uu___113_16801.normalized_eff_names);
         proof_ns = (uu___113_16801.proof_ns);
         synth_hook = (uu___113_16801.synth_hook);
         splice = (uu___113_16801.splice);
         is_native_tactic = (uu___113_16801.is_native_tactic);
         identifier_info = (uu___113_16801.identifier_info);
         tc_hooks = (uu___113_16801.tc_hooks);
         dsenv = (uu___113_16801.dsenv);
         dep_graph = (uu___113_16801.dep_graph)
       })
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env ->
    let no_uvs = FStar_Syntax_Free.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____16892)::tl1 -> aux out tl1
      | (Binding_lid (uu____16896, (uu____16897, t)))::tl1 ->
          let uu____16912 =
            let uu____16919 = FStar_Syntax_Free.uvars t in
            ext out uu____16919 in
          aux uu____16912 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16926;
            FStar_Syntax_Syntax.index = uu____16927;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16934 =
            let uu____16941 = FStar_Syntax_Free.uvars t in
            ext out uu____16941 in
          aux uu____16934 tl1
      | (Binding_sig uu____16948)::uu____16949 -> out
      | (Binding_sig_inst uu____16958)::uu____16959 -> out in
    aux no_uvs env.gamma
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____17024)::tl1 -> aux out tl1
      | (Binding_univ uu____17036)::tl1 -> aux out tl1
      | (Binding_lid (uu____17040, (uu____17041, t)))::tl1 ->
          let uu____17056 =
            let uu____17059 = FStar_Syntax_Free.univs t in
            ext out uu____17059 in
          aux uu____17056 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17062;
            FStar_Syntax_Syntax.index = uu____17063;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17070 =
            let uu____17073 = FStar_Syntax_Free.univs t in
            ext out uu____17073 in
          aux uu____17070 tl1
      | (Binding_sig uu____17076)::uu____17077 -> out in
    aux no_univs env.gamma
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____17140)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____17156 = FStar_Util.set_add uname out in
          aux uu____17156 tl1
      | (Binding_lid (uu____17159, (uu____17160, t)))::tl1 ->
          let uu____17175 =
            let uu____17178 = FStar_Syntax_Free.univnames t in
            ext out uu____17178 in
          aux uu____17175 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17181;
            FStar_Syntax_Syntax.index = uu____17182;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17189 =
            let uu____17192 = FStar_Syntax_Free.univnames t in
            ext out uu____17192 in
          aux uu____17189 tl1
      | (Binding_sig uu____17195)::uu____17196 -> out in
    aux no_univ_names env.gamma
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___87_17222 ->
            match uu___87_17222 with
            | Binding_var x -> [x]
            | Binding_lid uu____17226 -> []
            | Binding_sig uu____17231 -> []
            | Binding_univ uu____17238 -> []
            | Binding_sig_inst uu____17239 -> []))
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs ->
    let uu____17257 =
      let uu____17260 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____17260
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____17257 FStar_List.rev
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env -> bound_vars_of_bindings env.gamma
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env -> binders_of_bindings env.gamma
let (print_gamma : env -> unit) =
  fun env ->
    let uu____17288 =
      let uu____17289 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___88_17299 ->
                match uu___88_17299 with
                | Binding_var x ->
                    let uu____17301 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____17301
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l, uu____17304) ->
                    let uu____17305 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____17305
                | Binding_sig (ls, uu____17307) ->
                    let uu____17312 =
                      let uu____17313 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____17313
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____17312
                | Binding_sig_inst (ls, uu____17323, uu____17324) ->
                    let uu____17329 =
                      let uu____17330 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____17330
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____17329)) in
      FStar_All.pipe_right uu____17289 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____17288 (FStar_Util.print1 "%s\n")
let (eq_gamma : env -> env -> Prims.bool) =
  fun env ->
    fun env' ->
      let uu____17351 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____17351
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____17379 ->
                 fun uu____17380 ->
                   match (uu____17379, uu____17380) with
                   | ((b1, uu____17398), (b2, uu____17400)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env ->
    fun f ->
      fun a -> FStar_List.fold_right (fun e -> fun a1 -> f a1 e) env.gamma a
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___89_17451 ->
    match uu___89_17451 with
    | NoDelta -> "NoDelta"
    | Inlining -> "Inlining"
    | Eager_unfolding_only -> "Eager_unfolding_only"
    | Unfold uu____17452 -> "Unfold _"
    | UnfoldTac -> "UnfoldTac"
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env ->
    let keys =
      FStar_List.fold_left
        (fun keys ->
           fun uu___90_17472 ->
             match uu___90_17472 with
             | Binding_sig (lids, uu____17478) -> FStar_List.append lids keys
             | uu____17483 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____17489 ->
         fun v1 ->
           fun keys1 ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env ->
    fun path ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([], uu____17531) -> true
        | (x::xs1, y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____17550, uu____17551) -> false in
      let uu____17560 =
        FStar_List.tryFind
          (fun uu____17578 ->
             match uu____17578 with | (p, uu____17586) -> list_prefix p path)
          env.proof_ns in
      match uu____17560 with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu____17597, b) -> b
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun lid ->
      let uu____17619 = FStar_Ident.path_of_lid lid in
      should_enc_path env uu____17619
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b ->
    fun e ->
      fun path ->
        let uu___114_17637 = e in
        {
          solver = (uu___114_17637.solver);
          range = (uu___114_17637.range);
          curmodule = (uu___114_17637.curmodule);
          gamma = (uu___114_17637.gamma);
          gamma_cache = (uu___114_17637.gamma_cache);
          modules = (uu___114_17637.modules);
          expected_typ = (uu___114_17637.expected_typ);
          sigtab = (uu___114_17637.sigtab);
          is_pattern = (uu___114_17637.is_pattern);
          instantiate_imp = (uu___114_17637.instantiate_imp);
          effects = (uu___114_17637.effects);
          generalize = (uu___114_17637.generalize);
          letrecs = (uu___114_17637.letrecs);
          top_level = (uu___114_17637.top_level);
          check_uvars = (uu___114_17637.check_uvars);
          use_eq = (uu___114_17637.use_eq);
          is_iface = (uu___114_17637.is_iface);
          admit = (uu___114_17637.admit);
          lax = (uu___114_17637.lax);
          lax_universes = (uu___114_17637.lax_universes);
          failhard = (uu___114_17637.failhard);
          nosynth = (uu___114_17637.nosynth);
          tc_term = (uu___114_17637.tc_term);
          type_of = (uu___114_17637.type_of);
          universe_of = (uu___114_17637.universe_of);
          check_type_of = (uu___114_17637.check_type_of);
          use_bv_sorts = (uu___114_17637.use_bv_sorts);
          qtbl_name_and_index = (uu___114_17637.qtbl_name_and_index);
          normalized_eff_names = (uu___114_17637.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___114_17637.synth_hook);
          splice = (uu___114_17637.splice);
          is_native_tactic = (uu___114_17637.is_native_tactic);
          identifier_info = (uu___114_17637.identifier_info);
          tc_hooks = (uu___114_17637.tc_hooks);
          dsenv = (uu___114_17637.dsenv);
          dep_graph = (uu___114_17637.dep_graph)
        }
let (add_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns true e path
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e -> fun path -> cons_proof_ns false e path
let (get_proof_ns : env -> proof_namespace) = fun e -> e.proof_ns
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns ->
    fun e ->
      let uu___115_17677 = e in
      {
        solver = (uu___115_17677.solver);
        range = (uu___115_17677.range);
        curmodule = (uu___115_17677.curmodule);
        gamma = (uu___115_17677.gamma);
        gamma_cache = (uu___115_17677.gamma_cache);
        modules = (uu___115_17677.modules);
        expected_typ = (uu___115_17677.expected_typ);
        sigtab = (uu___115_17677.sigtab);
        is_pattern = (uu___115_17677.is_pattern);
        instantiate_imp = (uu___115_17677.instantiate_imp);
        effects = (uu___115_17677.effects);
        generalize = (uu___115_17677.generalize);
        letrecs = (uu___115_17677.letrecs);
        top_level = (uu___115_17677.top_level);
        check_uvars = (uu___115_17677.check_uvars);
        use_eq = (uu___115_17677.use_eq);
        is_iface = (uu___115_17677.is_iface);
        admit = (uu___115_17677.admit);
        lax = (uu___115_17677.lax);
        lax_universes = (uu___115_17677.lax_universes);
        failhard = (uu___115_17677.failhard);
        nosynth = (uu___115_17677.nosynth);
        tc_term = (uu___115_17677.tc_term);
        type_of = (uu___115_17677.type_of);
        universe_of = (uu___115_17677.universe_of);
        check_type_of = (uu___115_17677.check_type_of);
        use_bv_sorts = (uu___115_17677.use_bv_sorts);
        qtbl_name_and_index = (uu___115_17677.qtbl_name_and_index);
        normalized_eff_names = (uu___115_17677.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___115_17677.synth_hook);
        splice = (uu___115_17677.splice);
        is_native_tactic = (uu___115_17677.is_native_tactic);
        identifier_info = (uu___115_17677.identifier_info);
        tc_hooks = (uu___115_17677.tc_hooks);
        dsenv = (uu___115_17677.dsenv);
        dep_graph = (uu___115_17677.dep_graph)
      }
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e ->
    fun t ->
      let uu____17692 = FStar_Syntax_Free.names t in
      let uu____17695 = bound_vars e in
      FStar_List.fold_left (fun s -> fun bv -> FStar_Util.set_remove bv s)
        uu____17692 uu____17695
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    fun t ->
      let uu____17716 = unbound_vars e t in
      FStar_Util.set_is_empty uu____17716
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____17724 = FStar_Syntax_Free.names t in
    FStar_Util.set_is_empty uu____17724
let (string_of_proof_ns : env -> Prims.string) =
  fun env ->
    let aux uu____17743 =
      match uu____17743 with
      | (p, b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____17759 = FStar_Ident.text_of_path p in
             Prims.strcat (if b then "+" else "-") uu____17759) in
    let uu____17761 =
      let uu____17764 = FStar_List.map aux env.proof_ns in
      FStar_All.pipe_right uu____17764 FStar_List.rev in
    FStar_All.pipe_right uu____17761 (FStar_String.concat " ")
let (dummy_solver : solver_t) =
  {
    init = (fun uu____17781 -> ());
    push = (fun uu____17783 -> ());
    pop = (fun uu____17785 -> ());
    encode_modul = (fun uu____17788 -> fun uu____17789 -> ());
    encode_sig = (fun uu____17792 -> fun uu____17793 -> ());
    preprocess =
      (fun e ->
         fun g ->
           let uu____17799 =
             let uu____17806 = FStar_Options.peek () in (e, g, uu____17806) in
           [uu____17799]);
    solve = (fun uu____17822 -> fun uu____17823 -> fun uu____17824 -> ());
    finish = (fun uu____17830 -> ());
    refresh = (fun uu____17832 -> ())
  }
let (mk_copy : env -> env) =
  fun en ->
    let uu___116_17838 = en in
    let uu____17839 = FStar_Util.smap_copy en.gamma_cache in
    let uu____17842 = FStar_Util.smap_copy en.sigtab in
    let uu____17845 = FStar_Syntax_DsEnv.mk_copy en.dsenv in
    {
      solver = (uu___116_17838.solver);
      range = (uu___116_17838.range);
      curmodule = (uu___116_17838.curmodule);
      gamma = (uu___116_17838.gamma);
      gamma_cache = uu____17839;
      modules = (uu___116_17838.modules);
      expected_typ = (uu___116_17838.expected_typ);
      sigtab = uu____17842;
      is_pattern = (uu___116_17838.is_pattern);
      instantiate_imp = (uu___116_17838.instantiate_imp);
      effects = (uu___116_17838.effects);
      generalize = (uu___116_17838.generalize);
      letrecs = (uu___116_17838.letrecs);
      top_level = (uu___116_17838.top_level);
      check_uvars = (uu___116_17838.check_uvars);
      use_eq = (uu___116_17838.use_eq);
      is_iface = (uu___116_17838.is_iface);
      admit = (uu___116_17838.admit);
      lax = (uu___116_17838.lax);
      lax_universes = (uu___116_17838.lax_universes);
      failhard = (uu___116_17838.failhard);
      nosynth = (uu___116_17838.nosynth);
      tc_term = (uu___116_17838.tc_term);
      type_of = (uu___116_17838.type_of);
      universe_of = (uu___116_17838.universe_of);
      check_type_of = (uu___116_17838.check_type_of);
      use_bv_sorts = (uu___116_17838.use_bv_sorts);
      qtbl_name_and_index = (uu___116_17838.qtbl_name_and_index);
      normalized_eff_names = (uu___116_17838.normalized_eff_names);
      proof_ns = (uu___116_17838.proof_ns);
      synth_hook = (uu___116_17838.synth_hook);
      splice = (uu___116_17838.splice);
      is_native_tactic = (uu___116_17838.is_native_tactic);
      identifier_info = (uu___116_17838.identifier_info);
      tc_hooks = (uu___116_17838.tc_hooks);
      dsenv = uu____17845;
      dep_graph = (uu___116_17838.dep_graph)
    }