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
  FStar_Pervasives_Native.tuple3 [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____45 -> false
  
let (__proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____63 -> false
  
let (__proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_sig : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____95 -> false
  
let (__proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____127 -> false
  
let (__proj__Binding_univ__item___0 :
  binding -> FStar_Syntax_Syntax.univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Binding_sig_inst : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____149 -> false
  
let (__proj__Binding_sig_inst__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0 
type delta_level =
  | NoDelta 
  | Inlining 
  | Eager_unfolding_only 
  | Unfold of FStar_Syntax_Syntax.delta_depth 
  | UnfoldTac [@@deriving show]
let (uu___is_NoDelta : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____190 -> false
  
let (uu___is_Inlining : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____196 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____202 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____209 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
let (uu___is_UnfoldTac : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____222 -> false
  
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
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term;_} ->
        __fname__mlift_term
  
type edge =
  {
  msource: FStar_Ident.lident ;
  mtarget: FStar_Ident.lident ;
  mlift: mlift }[@@deriving show]
let (__proj__Mkedge__item__msource : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__msource
  
let (__proj__Mkedge__item__mtarget : edge -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mtarget
  
let (__proj__Mkedge__item__mlift : edge -> mlift) =
  fun projectee  ->
    match projectee with
    | { msource = __fname__msource; mtarget = __fname__mtarget;
        mlift = __fname__mlift;_} -> __fname__mlift
  
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  order: edge Prims.list ;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list
    }[@@deriving show]
let (__proj__Mkeffects__item__decls :
  effects ->
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__decls
  
let (__proj__Mkeffects__item__order : effects -> edge Prims.list) =
  fun projectee  ->
    match projectee with
    | { decls = __fname__decls; order = __fname__order;
        joins = __fname__joins;_} -> __fname__order
  
let (__proj__Mkeffects__item__joins :
  effects ->
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list)
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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3
    ;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
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
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
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
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
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
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2
    ;
  implicits:
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list
    }[@@deriving show]
and tcenv_hooks = {
  tc_push_in_gamma_hook: env -> binding -> unit }[@@deriving show]
let (__proj__Mkenv__item__solver : env -> solver_t) =
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.univ_names)
      FStar_Pervasives_Native.tuple3 Prims.list)
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,guard_t)
          FStar_Pervasives_Native.tuple3)
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
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3)
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
    (Prims.int FStar_Util.smap,(FStar_Ident.lident,Prims.int)
                                 FStar_Pervasives_Native.tuple2
                                 FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { solver = __fname__solver; range = __fname__range;
        curmodule = __fname__curmodule; gamma = __fname__gamma;
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
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
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
        (env,goal,FStar_Options.optionstate) FStar_Pervasives_Native.tuple3
          Prims.list)
  =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__refresh
  
let (__proj__Mkguard_t__item__guard_f :
  guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__guard_f
  
let (__proj__Mkguard_t__item__deferred :
  guard_t -> FStar_TypeChecker_Common.deferred) =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__deferred
  
let (__proj__Mkguard_t__item__univ_ineqs :
  guard_t ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__univ_ineqs
  
let (__proj__Mkguard_t__item__implicits :
  guard_t ->
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { guard_f = __fname__guard_f; deferred = __fname__deferred;
        univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits;_}
        -> __fname__implicits
  
let (__proj__Mktcenv_hooks__item__tc_push_in_gamma_hook :
  tcenv_hooks -> env -> binding -> unit) =
  fun projectee  ->
    match projectee with
    | { tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook;_} ->
        __fname__tc_push_in_gamma_hook
  
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list[@@deriving show]
let (rename_gamma :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    binding Prims.list -> binding Prims.list)
  =
  fun subst1  ->
    fun gamma  ->
      FStar_All.pipe_right gamma
        (FStar_List.map
           (fun uu___73_7362  ->
              match uu___73_7362 with
              | Binding_var x ->
                  let y =
                    let uu____7365 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____7365  in
                  let uu____7366 =
                    let uu____7367 = FStar_Syntax_Subst.compress y  in
                    uu____7367.FStar_Syntax_Syntax.n  in
                  (match uu____7366 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____7371 =
                         let uu___88_7372 = y1  in
                         let uu____7373 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___88_7372.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___88_7372.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____7373
                         }  in
                       Binding_var uu____7371
                   | uu____7376 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___89_7388 = env  in
      let uu____7389 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___89_7388.solver);
        range = (uu___89_7388.range);
        curmodule = (uu___89_7388.curmodule);
        gamma = uu____7389;
        gamma_cache = (uu___89_7388.gamma_cache);
        modules = (uu___89_7388.modules);
        expected_typ = (uu___89_7388.expected_typ);
        sigtab = (uu___89_7388.sigtab);
        is_pattern = (uu___89_7388.is_pattern);
        instantiate_imp = (uu___89_7388.instantiate_imp);
        effects = (uu___89_7388.effects);
        generalize = (uu___89_7388.generalize);
        letrecs = (uu___89_7388.letrecs);
        top_level = (uu___89_7388.top_level);
        check_uvars = (uu___89_7388.check_uvars);
        use_eq = (uu___89_7388.use_eq);
        is_iface = (uu___89_7388.is_iface);
        admit = (uu___89_7388.admit);
        lax = (uu___89_7388.lax);
        lax_universes = (uu___89_7388.lax_universes);
        failhard = (uu___89_7388.failhard);
        nosynth = (uu___89_7388.nosynth);
        tc_term = (uu___89_7388.tc_term);
        type_of = (uu___89_7388.type_of);
        universe_of = (uu___89_7388.universe_of);
        check_type_of = (uu___89_7388.check_type_of);
        use_bv_sorts = (uu___89_7388.use_bv_sorts);
        qtbl_name_and_index = (uu___89_7388.qtbl_name_and_index);
        normalized_eff_names = (uu___89_7388.normalized_eff_names);
        proof_ns = (uu___89_7388.proof_ns);
        synth_hook = (uu___89_7388.synth_hook);
        splice = (uu___89_7388.splice);
        is_native_tactic = (uu___89_7388.is_native_tactic);
        identifier_info = (uu___89_7388.identifier_info);
        tc_hooks = (uu___89_7388.tc_hooks);
        dsenv = (uu___89_7388.dsenv);
        dep_graph = (uu___89_7388.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____7396  -> fun uu____7397  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___90_7413 = env  in
      {
        solver = (uu___90_7413.solver);
        range = (uu___90_7413.range);
        curmodule = (uu___90_7413.curmodule);
        gamma = (uu___90_7413.gamma);
        gamma_cache = (uu___90_7413.gamma_cache);
        modules = (uu___90_7413.modules);
        expected_typ = (uu___90_7413.expected_typ);
        sigtab = (uu___90_7413.sigtab);
        is_pattern = (uu___90_7413.is_pattern);
        instantiate_imp = (uu___90_7413.instantiate_imp);
        effects = (uu___90_7413.effects);
        generalize = (uu___90_7413.generalize);
        letrecs = (uu___90_7413.letrecs);
        top_level = (uu___90_7413.top_level);
        check_uvars = (uu___90_7413.check_uvars);
        use_eq = (uu___90_7413.use_eq);
        is_iface = (uu___90_7413.is_iface);
        admit = (uu___90_7413.admit);
        lax = (uu___90_7413.lax);
        lax_universes = (uu___90_7413.lax_universes);
        failhard = (uu___90_7413.failhard);
        nosynth = (uu___90_7413.nosynth);
        tc_term = (uu___90_7413.tc_term);
        type_of = (uu___90_7413.type_of);
        universe_of = (uu___90_7413.universe_of);
        check_type_of = (uu___90_7413.check_type_of);
        use_bv_sorts = (uu___90_7413.use_bv_sorts);
        qtbl_name_and_index = (uu___90_7413.qtbl_name_and_index);
        normalized_eff_names = (uu___90_7413.normalized_eff_names);
        proof_ns = (uu___90_7413.proof_ns);
        synth_hook = (uu___90_7413.synth_hook);
        splice = (uu___90_7413.splice);
        is_native_tactic = (uu___90_7413.is_native_tactic);
        identifier_info = (uu___90_7413.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___90_7413.dsenv);
        dep_graph = (uu___90_7413.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___91_7424 = e  in
      {
        solver = (uu___91_7424.solver);
        range = (uu___91_7424.range);
        curmodule = (uu___91_7424.curmodule);
        gamma = (uu___91_7424.gamma);
        gamma_cache = (uu___91_7424.gamma_cache);
        modules = (uu___91_7424.modules);
        expected_typ = (uu___91_7424.expected_typ);
        sigtab = (uu___91_7424.sigtab);
        is_pattern = (uu___91_7424.is_pattern);
        instantiate_imp = (uu___91_7424.instantiate_imp);
        effects = (uu___91_7424.effects);
        generalize = (uu___91_7424.generalize);
        letrecs = (uu___91_7424.letrecs);
        top_level = (uu___91_7424.top_level);
        check_uvars = (uu___91_7424.check_uvars);
        use_eq = (uu___91_7424.use_eq);
        is_iface = (uu___91_7424.is_iface);
        admit = (uu___91_7424.admit);
        lax = (uu___91_7424.lax);
        lax_universes = (uu___91_7424.lax_universes);
        failhard = (uu___91_7424.failhard);
        nosynth = (uu___91_7424.nosynth);
        tc_term = (uu___91_7424.tc_term);
        type_of = (uu___91_7424.type_of);
        universe_of = (uu___91_7424.universe_of);
        check_type_of = (uu___91_7424.check_type_of);
        use_bv_sorts = (uu___91_7424.use_bv_sorts);
        qtbl_name_and_index = (uu___91_7424.qtbl_name_and_index);
        normalized_eff_names = (uu___91_7424.normalized_eff_names);
        proof_ns = (uu___91_7424.proof_ns);
        synth_hook = (uu___91_7424.synth_hook);
        splice = (uu___91_7424.splice);
        is_native_tactic = (uu___91_7424.is_native_tactic);
        identifier_info = (uu___91_7424.identifier_info);
        tc_hooks = (uu___91_7424.tc_hooks);
        dsenv = (uu___91_7424.dsenv);
        dep_graph = g
      }
  
let (dep_graph : env -> FStar_Parser_Dep.deps) = fun e  -> e.dep_graph 
type env_t = env[@@deriving show]
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap[@@deriving show]
let (should_verify : env -> Prims.bool) =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
  
let (visible_at : delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____7447) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____7448,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____7449,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____7450 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____7459 . unit -> 'Auu____7459 FStar_Util.smap =
  fun uu____7466  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____7471 . unit -> 'Auu____7471 FStar_Util.smap =
  fun uu____7478  -> FStar_Util.smap_create (Prims.parse_int "100") 
let (initial_env :
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
          (Prims.bool ->
             env ->
               FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.typ -> guard_t)
            -> solver_t -> FStar_Ident.lident -> env)
  =
  fun deps  ->
    fun tc_term  ->
      fun type_of  ->
        fun universe_of  ->
          fun check_type_of  ->
            fun solver  ->
              fun module_lid  ->
                let uu____7588 = new_gamma_cache ()  in
                let uu____7591 = new_sigtab ()  in
                let uu____7594 =
                  let uu____7607 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____7607, FStar_Pervasives_Native.None)  in
                let uu____7622 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____7625 = FStar_Options.using_facts_from ()  in
                let uu____7626 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____7629 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____7588;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____7591;
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
                  qtbl_name_and_index = uu____7594;
                  normalized_eff_names = uu____7622;
                  proof_ns = uu____7625;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____7665  -> false);
                  identifier_info = uu____7626;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____7629;
                  dep_graph = deps
                }
  
let (dsenv : env -> FStar_Syntax_DsEnv.env) = fun env  -> env.dsenv 
let (sigtab : env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap) =
  fun env  -> env.sigtab 
let (gamma_cache : env -> cached_elt FStar_Util.smap) =
  fun env  -> env.gamma_cache 
let (query_indices :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref)
  = FStar_Util.mk_ref [[]] 
let (push_query_indices : unit -> unit) =
  fun uu____7756  ->
    let uu____7757 = FStar_ST.op_Bang query_indices  in
    match uu____7757 with
    | [] -> failwith "Empty query indices!"
    | uu____7811 ->
        let uu____7820 =
          let uu____7829 =
            let uu____7836 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____7836  in
          let uu____7890 = FStar_ST.op_Bang query_indices  in uu____7829 ::
            uu____7890
           in
        FStar_ST.op_Colon_Equals query_indices uu____7820
  
let (pop_query_indices : unit -> unit) =
  fun uu____7987  ->
    let uu____7988 = FStar_ST.op_Bang query_indices  in
    match uu____7988 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8111  ->
    match uu____8111 with
    | (l,n1) ->
        let uu____8118 = FStar_ST.op_Bang query_indices  in
        (match uu____8118 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____8237 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____8256  ->
    let uu____8257 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____8257
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    let uu____8333 =
      let uu____8334 =
        let uu____8337 = FStar_ST.op_Bang stack  in env :: uu____8337  in
      FStar_ST.op_Colon_Equals stack uu____8334  in
    let uu___92_8394 = env  in
    let uu____8395 = FStar_Util.smap_copy (gamma_cache env)  in
    let uu____8398 = FStar_Util.smap_copy (sigtab env)  in
    let uu____8401 =
      let uu____8414 =
        let uu____8417 =
          FStar_All.pipe_right env.qtbl_name_and_index
            FStar_Pervasives_Native.fst
           in
        FStar_Util.smap_copy uu____8417  in
      let uu____8442 =
        FStar_All.pipe_right env.qtbl_name_and_index
          FStar_Pervasives_Native.snd
         in
      (uu____8414, uu____8442)  in
    let uu____8483 = FStar_Util.smap_copy env.normalized_eff_names  in
    let uu____8486 =
      let uu____8489 = FStar_ST.op_Bang env.identifier_info  in
      FStar_Util.mk_ref uu____8489  in
    {
      solver = (uu___92_8394.solver);
      range = (uu___92_8394.range);
      curmodule = (uu___92_8394.curmodule);
      gamma = (uu___92_8394.gamma);
      gamma_cache = uu____8395;
      modules = (uu___92_8394.modules);
      expected_typ = (uu___92_8394.expected_typ);
      sigtab = uu____8398;
      is_pattern = (uu___92_8394.is_pattern);
      instantiate_imp = (uu___92_8394.instantiate_imp);
      effects = (uu___92_8394.effects);
      generalize = (uu___92_8394.generalize);
      letrecs = (uu___92_8394.letrecs);
      top_level = (uu___92_8394.top_level);
      check_uvars = (uu___92_8394.check_uvars);
      use_eq = (uu___92_8394.use_eq);
      is_iface = (uu___92_8394.is_iface);
      admit = (uu___92_8394.admit);
      lax = (uu___92_8394.lax);
      lax_universes = (uu___92_8394.lax_universes);
      failhard = (uu___92_8394.failhard);
      nosynth = (uu___92_8394.nosynth);
      tc_term = (uu___92_8394.tc_term);
      type_of = (uu___92_8394.type_of);
      universe_of = (uu___92_8394.universe_of);
      check_type_of = (uu___92_8394.check_type_of);
      use_bv_sorts = (uu___92_8394.use_bv_sorts);
      qtbl_name_and_index = uu____8401;
      normalized_eff_names = uu____8483;
      proof_ns = (uu___92_8394.proof_ns);
      synth_hook = (uu___92_8394.synth_hook);
      splice = (uu___92_8394.splice);
      is_native_tactic = (uu___92_8394.is_native_tactic);
      identifier_info = uu____8486;
      tc_hooks = (uu___92_8394.tc_hooks);
      dsenv = (uu___92_8394.dsenv);
      dep_graph = (uu___92_8394.dep_graph)
    }
  
let (pop_stack : unit -> env) =
  fun uu____8539  ->
    let uu____8540 = FStar_ST.op_Bang stack  in
    match uu____8540 with
    | env::tl1 -> let uu____8574 = FStar_ST.op_Colon_Equals stack tl1  in env
    | uu____8602 -> failwith "Impossible: Too many pops"
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____8615 = push_query_indices ()  in
      let uu____8616 = (env.solver).push msg  in push_stack env
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____8627 = (env.solver).pop msg  in
      let uu____8628 = pop_query_indices ()  in pop_stack ()
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____8641,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____8673 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____8699  ->
                  match uu____8699 with
                  | (m,uu____8705) -> FStar_Ident.lid_equals l m))
           in
        (match uu____8673 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             let uu____8711 = add_query_index (l, next)  in
             let uu____8712 = FStar_Util.smap_add tbl l.FStar_Ident.str next
                in
             let uu___93_8713 = env  in
             {
               solver = (uu___93_8713.solver);
               range = (uu___93_8713.range);
               curmodule = (uu___93_8713.curmodule);
               gamma = (uu___93_8713.gamma);
               gamma_cache = (uu___93_8713.gamma_cache);
               modules = (uu___93_8713.modules);
               expected_typ = (uu___93_8713.expected_typ);
               sigtab = (uu___93_8713.sigtab);
               is_pattern = (uu___93_8713.is_pattern);
               instantiate_imp = (uu___93_8713.instantiate_imp);
               effects = (uu___93_8713.effects);
               generalize = (uu___93_8713.generalize);
               letrecs = (uu___93_8713.letrecs);
               top_level = (uu___93_8713.top_level);
               check_uvars = (uu___93_8713.check_uvars);
               use_eq = (uu___93_8713.use_eq);
               is_iface = (uu___93_8713.is_iface);
               admit = (uu___93_8713.admit);
               lax = (uu___93_8713.lax);
               lax_universes = (uu___93_8713.lax_universes);
               failhard = (uu___93_8713.failhard);
               nosynth = (uu___93_8713.nosynth);
               tc_term = (uu___93_8713.tc_term);
               type_of = (uu___93_8713.type_of);
               universe_of = (uu___93_8713.universe_of);
               check_type_of = (uu___93_8713.check_type_of);
               use_bv_sorts = (uu___93_8713.use_bv_sorts);
               qtbl_name_and_index =
                 (tbl, (FStar_Pervasives_Native.Some (l, next)));
               normalized_eff_names = (uu___93_8713.normalized_eff_names);
               proof_ns = (uu___93_8713.proof_ns);
               synth_hook = (uu___93_8713.synth_hook);
               splice = (uu___93_8713.splice);
               is_native_tactic = (uu___93_8713.is_native_tactic);
               identifier_info = (uu___93_8713.identifier_info);
               tc_hooks = (uu___93_8713.tc_hooks);
               dsenv = (uu___93_8713.dsenv);
               dep_graph = (uu___93_8713.dep_graph)
             }
         | FStar_Pervasives_Native.Some (uu____8726,m) ->
             let next = m + (Prims.parse_int "1")  in
             let uu____8733 = add_query_index (l, next)  in
             let uu____8734 = FStar_Util.smap_add tbl l.FStar_Ident.str next
                in
             let uu___94_8735 = env  in
             {
               solver = (uu___94_8735.solver);
               range = (uu___94_8735.range);
               curmodule = (uu___94_8735.curmodule);
               gamma = (uu___94_8735.gamma);
               gamma_cache = (uu___94_8735.gamma_cache);
               modules = (uu___94_8735.modules);
               expected_typ = (uu___94_8735.expected_typ);
               sigtab = (uu___94_8735.sigtab);
               is_pattern = (uu___94_8735.is_pattern);
               instantiate_imp = (uu___94_8735.instantiate_imp);
               effects = (uu___94_8735.effects);
               generalize = (uu___94_8735.generalize);
               letrecs = (uu___94_8735.letrecs);
               top_level = (uu___94_8735.top_level);
               check_uvars = (uu___94_8735.check_uvars);
               use_eq = (uu___94_8735.use_eq);
               is_iface = (uu___94_8735.is_iface);
               admit = (uu___94_8735.admit);
               lax = (uu___94_8735.lax);
               lax_universes = (uu___94_8735.lax_universes);
               failhard = (uu___94_8735.failhard);
               nosynth = (uu___94_8735.nosynth);
               tc_term = (uu___94_8735.tc_term);
               type_of = (uu___94_8735.type_of);
               universe_of = (uu___94_8735.universe_of);
               check_type_of = (uu___94_8735.check_type_of);
               use_bv_sorts = (uu___94_8735.use_bv_sorts);
               qtbl_name_and_index =
                 (tbl, (FStar_Pervasives_Native.Some (l, next)));
               normalized_eff_names = (uu___94_8735.normalized_eff_names);
               proof_ns = (uu___94_8735.proof_ns);
               synth_hook = (uu___94_8735.synth_hook);
               splice = (uu___94_8735.splice);
               is_native_tactic = (uu___94_8735.is_native_tactic);
               identifier_info = (uu___94_8735.identifier_info);
               tc_hooks = (uu___94_8735.tc_hooks);
               dsenv = (uu___94_8735.dsenv);
               dep_graph = (uu___94_8735.dep_graph)
             })
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___95_8769 = e  in
         {
           solver = (uu___95_8769.solver);
           range = r;
           curmodule = (uu___95_8769.curmodule);
           gamma = (uu___95_8769.gamma);
           gamma_cache = (uu___95_8769.gamma_cache);
           modules = (uu___95_8769.modules);
           expected_typ = (uu___95_8769.expected_typ);
           sigtab = (uu___95_8769.sigtab);
           is_pattern = (uu___95_8769.is_pattern);
           instantiate_imp = (uu___95_8769.instantiate_imp);
           effects = (uu___95_8769.effects);
           generalize = (uu___95_8769.generalize);
           letrecs = (uu___95_8769.letrecs);
           top_level = (uu___95_8769.top_level);
           check_uvars = (uu___95_8769.check_uvars);
           use_eq = (uu___95_8769.use_eq);
           is_iface = (uu___95_8769.is_iface);
           admit = (uu___95_8769.admit);
           lax = (uu___95_8769.lax);
           lax_universes = (uu___95_8769.lax_universes);
           failhard = (uu___95_8769.failhard);
           nosynth = (uu___95_8769.nosynth);
           tc_term = (uu___95_8769.tc_term);
           type_of = (uu___95_8769.type_of);
           universe_of = (uu___95_8769.universe_of);
           check_type_of = (uu___95_8769.check_type_of);
           use_bv_sorts = (uu___95_8769.use_bv_sorts);
           qtbl_name_and_index = (uu___95_8769.qtbl_name_and_index);
           normalized_eff_names = (uu___95_8769.normalized_eff_names);
           proof_ns = (uu___95_8769.proof_ns);
           synth_hook = (uu___95_8769.synth_hook);
           splice = (uu___95_8769.splice);
           is_native_tactic = (uu___95_8769.is_native_tactic);
           identifier_info = (uu___95_8769.identifier_info);
           tc_hooks = (uu___95_8769.tc_hooks);
           dsenv = (uu___95_8769.dsenv);
           dep_graph = (uu___95_8769.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____8785 =
        let uu____8786 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____8786 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____8785
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____8848 =
          let uu____8849 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____8849 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____8848
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____8911 =
          let uu____8912 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____8912 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____8911
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____8974 =
        let uu____8975 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____8975 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____8974
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___96_9044 = env  in
      {
        solver = (uu___96_9044.solver);
        range = (uu___96_9044.range);
        curmodule = lid;
        gamma = (uu___96_9044.gamma);
        gamma_cache = (uu___96_9044.gamma_cache);
        modules = (uu___96_9044.modules);
        expected_typ = (uu___96_9044.expected_typ);
        sigtab = (uu___96_9044.sigtab);
        is_pattern = (uu___96_9044.is_pattern);
        instantiate_imp = (uu___96_9044.instantiate_imp);
        effects = (uu___96_9044.effects);
        generalize = (uu___96_9044.generalize);
        letrecs = (uu___96_9044.letrecs);
        top_level = (uu___96_9044.top_level);
        check_uvars = (uu___96_9044.check_uvars);
        use_eq = (uu___96_9044.use_eq);
        is_iface = (uu___96_9044.is_iface);
        admit = (uu___96_9044.admit);
        lax = (uu___96_9044.lax);
        lax_universes = (uu___96_9044.lax_universes);
        failhard = (uu___96_9044.failhard);
        nosynth = (uu___96_9044.nosynth);
        tc_term = (uu___96_9044.tc_term);
        type_of = (uu___96_9044.type_of);
        universe_of = (uu___96_9044.universe_of);
        check_type_of = (uu___96_9044.check_type_of);
        use_bv_sorts = (uu___96_9044.use_bv_sorts);
        qtbl_name_and_index = (uu___96_9044.qtbl_name_and_index);
        normalized_eff_names = (uu___96_9044.normalized_eff_names);
        proof_ns = (uu___96_9044.proof_ns);
        synth_hook = (uu___96_9044.synth_hook);
        splice = (uu___96_9044.splice);
        is_native_tactic = (uu___96_9044.is_native_tactic);
        identifier_info = (uu___96_9044.identifier_info);
        tc_hooks = (uu___96_9044.tc_hooks);
        dsenv = (uu___96_9044.dsenv);
        dep_graph = (uu___96_9044.dep_graph)
      }
  
let (has_interface : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
  
let (find_in_sigtab :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____9071 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____9071
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____9081 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____9081)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____9091 =
      let uu____9092 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____9092  in
    (FStar_Errors.Fatal_VariableNotFound, uu____9091)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____9097  ->
    let uu____9098 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____9098
  
let (inst_tscheme_with :
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____9140) ->
          let uu____9151 = ()  in
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____9162 = FStar_Syntax_Subst.subst vs t  in (us, uu____9162)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___74_9178  ->
    match uu___74_9178 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____9202  -> new_u_univ ()))
           in
        inst_tscheme_with (us, t) us'
  
let (inst_tscheme_with_range :
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun t  ->
      let uu____9219 = inst_tscheme t  in
      match uu____9219 with
      | (us,t1) ->
          let uu____9230 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____9230)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____9250  ->
          match uu____9250 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   let uu____9264 =
                     if
                       (FStar_List.length insts) <>
                         (FStar_List.length univs1)
                     then
                       let uu____9265 =
                         let uu____9266 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____9267 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____9268 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____9269 = FStar_Syntax_Print.term_to_string t
                            in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____9266 uu____9267 uu____9268 uu____9269
                          in
                       failwith uu____9265
                     else ()  in
                   let uu____9271 =
                     inst_tscheme_with
                       ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                         t) insts
                      in
                   FStar_Pervasives_Native.snd uu____9271
               | uu____9278 ->
                   let uu____9279 =
                     let uu____9280 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____9280
                      in
                   failwith uu____9279)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  -> match projectee with | Yes  -> true | uu____9286 -> false 
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____9292 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____9298 -> false
  
let (in_cur_mod : env -> FStar_Ident.lident -> tri) =
  fun env  ->
    fun l  ->
      let cur = current_module env  in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident]
              in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident]  in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____9340) -> Maybe
             | (uu____9347,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____9366 -> No  in
           aux cur1 lns)
        else No
  
type qninfo =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option[@@deriving
                                                                   show]
let (lookup_qname : env -> FStar_Ident.lident -> qninfo) =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid  in
      let cache t =
        let uu____9415 =
          FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t  in
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____9457 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____9457 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___75_9503  ->
                   match uu___75_9503 with
                   | Binding_lid (l,t) ->
                       let uu____9526 = FStar_Ident.lid_equals lid l  in
                       if uu____9526
                       then
                         let uu____9547 =
                           let uu____9566 =
                             let uu____9581 = inst_tscheme t  in
                             FStar_Util.Inl uu____9581  in
                           let uu____9596 = FStar_Ident.range_of_lid l  in
                           (uu____9566, uu____9596)  in
                         FStar_Pervasives_Native.Some uu____9547
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____9648,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____9650);
                                     FStar_Syntax_Syntax.sigrng = uu____9651;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____9652;
                                     FStar_Syntax_Syntax.sigmeta = uu____9653;
                                     FStar_Syntax_Syntax.sigattrs =
                                       uu____9654;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____9674 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____9674
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____9722 ->
                             FStar_Pervasives_Native.Some t
                         | uu____9729 -> cache t  in
                       let uu____9730 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____9730 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____9772 =
                              let uu____9773 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                uu____9773)
                               in
                            maybe_cache uu____9772)
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____9807 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____9807 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____9849 =
                              let uu____9868 = FStar_Ident.range_of_lid l  in
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                uu____9868)
                               in
                            FStar_Pervasives_Native.Some uu____9849)
                   | uu____9913 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____9973 = find_in_sigtab env lid  in
         match uu____9973 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____10060) ->
          add_sigelts env ses
      | uu____10069 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
          let uu____10073 =
            FStar_List.iter
              (fun l  ->
                 FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se) lids
             in
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                 (FStar_List.iter
                    (fun a  ->
                       let se_let =
                         FStar_Syntax_Util.action_as_lb
                           ne.FStar_Syntax_Syntax.mname a
                           (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                          in
                       FStar_Util.smap_add (sigtab env)
                         (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                         se_let))
           | uu____10083 -> ())

and (add_sigelts : env -> FStar_Syntax_Syntax.sigelt Prims.list -> unit) =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))

let (try_lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___76_10114  ->
           match uu___76_10114 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____10132 -> FStar_Pervasives_Native.None)
  
let (lookup_type_of_let :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_let ((uu____10193,lb::[]),uu____10195) ->
            let uu____10208 =
              let uu____10217 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____10226 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____10217, uu____10226)  in
            FStar_Pervasives_Native.Some uu____10208
        | FStar_Syntax_Syntax.Sig_let ((uu____10239,lbs),uu____10241) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____10277 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____10289 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____10289
                     then
                       let uu____10300 =
                         let uu____10309 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____10318 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____10309, uu____10318)  in
                       FStar_Pervasives_Native.Some uu____10300
                     else FStar_Pervasives_Native.None)
        | uu____10340 -> FStar_Pervasives_Native.None
  
let (effect_signature :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.sigelt ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun se  ->
      let inst_tscheme1 ts =
        match us_opt with
        | FStar_Pervasives_Native.None  -> inst_tscheme ts
        | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let uu____10399 =
            let uu____10408 =
              let uu____10413 =
                let uu____10414 =
                  let uu____10417 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____10417
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____10414)  in
              inst_tscheme1 uu____10413  in
            (uu____10408, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____10399
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____10437,uu____10438) ->
          let uu____10443 =
            let uu____10452 =
              let uu____10457 =
                let uu____10458 =
                  let uu____10461 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____10461  in
                (us, uu____10458)  in
              inst_tscheme1 uu____10457  in
            (uu____10452, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____10443
      | uu____10478 -> FStar_Pervasives_Native.None
  
let (try_lookup_lid_aux :
  FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option ->
    env ->
      FStar_Ident.lident ->
        ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term'
                                          FStar_Syntax_Syntax.syntax)
           FStar_Pervasives_Native.tuple2,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun us_opt  ->
    fun env  ->
      fun lid  ->
        let inst_tscheme1 ts =
          match us_opt with
          | FStar_Pervasives_Native.None  -> inst_tscheme ts
          | FStar_Pervasives_Native.Some us -> inst_tscheme_with ts us  in
        let mapper uu____10566 =
          match uu____10566 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____10662,uvs,t,uu____10665,uu____10666,uu____10667);
                      FStar_Syntax_Syntax.sigrng = uu____10668;
                      FStar_Syntax_Syntax.sigquals = uu____10669;
                      FStar_Syntax_Syntax.sigmeta = uu____10670;
                      FStar_Syntax_Syntax.sigattrs = uu____10671;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____10692 =
                     let uu____10701 = inst_tscheme1 (uvs, t)  in
                     (uu____10701, rng)  in
                   FStar_Pervasives_Native.Some uu____10692
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____10721;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____10723;
                      FStar_Syntax_Syntax.sigattrs = uu____10724;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____10741 =
                     let uu____10742 = in_cur_mod env l  in uu____10742 = Yes
                      in
                   if uu____10741
                   then
                     let uu____10753 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____10753
                      then
                        let uu____10766 =
                          let uu____10775 = inst_tscheme1 (uvs, t)  in
                          (uu____10775, rng)  in
                        FStar_Pervasives_Native.Some uu____10766
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____10802 =
                        let uu____10811 = inst_tscheme1 (uvs, t)  in
                        (uu____10811, rng)  in
                      FStar_Pervasives_Native.Some uu____10802)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____10832,uu____10833);
                      FStar_Syntax_Syntax.sigrng = uu____10834;
                      FStar_Syntax_Syntax.sigquals = uu____10835;
                      FStar_Syntax_Syntax.sigmeta = uu____10836;
                      FStar_Syntax_Syntax.sigattrs = uu____10837;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____10876 =
                          let uu____10885 = inst_tscheme1 (uvs, k)  in
                          (uu____10885, rng)  in
                        FStar_Pervasives_Native.Some uu____10876
                    | uu____10902 ->
                        let uu____10903 =
                          let uu____10912 =
                            let uu____10917 =
                              let uu____10918 =
                                let uu____10921 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____10921
                                 in
                              (uvs, uu____10918)  in
                            inst_tscheme1 uu____10917  in
                          (uu____10912, rng)  in
                        FStar_Pervasives_Native.Some uu____10903)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____10942,uu____10943);
                      FStar_Syntax_Syntax.sigrng = uu____10944;
                      FStar_Syntax_Syntax.sigquals = uu____10945;
                      FStar_Syntax_Syntax.sigmeta = uu____10946;
                      FStar_Syntax_Syntax.sigattrs = uu____10947;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____10987 =
                          let uu____10996 = inst_tscheme_with (uvs, k) us  in
                          (uu____10996, rng)  in
                        FStar_Pervasives_Native.Some uu____10987
                    | uu____11013 ->
                        let uu____11014 =
                          let uu____11023 =
                            let uu____11028 =
                              let uu____11029 =
                                let uu____11032 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11032
                                 in
                              (uvs, uu____11029)  in
                            inst_tscheme_with uu____11028 us  in
                          (uu____11023, rng)  in
                        FStar_Pervasives_Native.Some uu____11014)
               | FStar_Util.Inr se ->
                   let uu____11066 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____11087;
                          FStar_Syntax_Syntax.sigrng = uu____11088;
                          FStar_Syntax_Syntax.sigquals = uu____11089;
                          FStar_Syntax_Syntax.sigmeta = uu____11090;
                          FStar_Syntax_Syntax.sigattrs = uu____11091;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____11106 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____11066
                     (FStar_Util.map_option
                        (fun uu____11154  ->
                           match uu____11154 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____11185 =
          let uu____11196 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____11196 mapper  in
        match uu____11185 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____11270 =
              let uu____11281 =
                let uu____11288 =
                  let uu___97_11291 = t  in
                  let uu____11292 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___97_11291.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____11292;
                    FStar_Syntax_Syntax.vars =
                      (uu___97_11291.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____11288)  in
              (uu____11281, r)  in
            FStar_Pervasives_Native.Some uu____11270
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____11339 = lookup_qname env l  in
      match uu____11339 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____11358 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____11410 = try_lookup_bv env bv  in
      match uu____11410 with
      | FStar_Pervasives_Native.None  ->
          let uu____11425 = variable_not_found bv  in
          FStar_Errors.raise_error uu____11425 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____11440 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____11441 =
            let uu____11442 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____11442  in
          (uu____11440, uu____11441)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____11463 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____11463 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____11529 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____11529  in
          let uu____11530 =
            let uu____11539 =
              let uu____11544 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____11544)  in
            (uu____11539, r1)  in
          FStar_Pervasives_Native.Some uu____11530
  
let (try_lookup_and_inst_lid :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.typ,FStar_Range.range)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun us  ->
      fun l  ->
        let uu____11578 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____11578 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____11611,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____11636 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____11636  in
            let uu____11637 =
              let uu____11642 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____11642, r1)  in
            FStar_Pervasives_Native.Some uu____11637
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____11665 = try_lookup_lid env l  in
      match uu____11665 with
      | FStar_Pervasives_Native.None  ->
          let uu____11692 = name_not_found l  in
          let uu____11697 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____11692 uu____11697
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___77_11737  ->
              match uu___77_11737 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____11739 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____11758 = lookup_qname env lid  in
      match uu____11758 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11767,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____11770;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____11772;
              FStar_Syntax_Syntax.sigattrs = uu____11773;_},FStar_Pervasives_Native.None
            ),uu____11774)
          ->
          let uu____11823 =
            let uu____11834 =
              let uu____11839 =
                let uu____11840 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____11840 t  in
              (uvs, uu____11839)  in
            (uu____11834, q)  in
          FStar_Pervasives_Native.Some uu____11823
      | uu____11857 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____11878 = lookup_qname env lid  in
      match uu____11878 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____11883,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____11886;
              FStar_Syntax_Syntax.sigquals = uu____11887;
              FStar_Syntax_Syntax.sigmeta = uu____11888;
              FStar_Syntax_Syntax.sigattrs = uu____11889;_},FStar_Pervasives_Native.None
            ),uu____11890)
          ->
          let uu____11939 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____11939 (uvs, t)
      | uu____11940 ->
          let uu____11941 = name_not_found lid  in
          let uu____11946 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____11941 uu____11946
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____11965 = lookup_qname env lid  in
      match uu____11965 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____11970,uvs,t,uu____11973,uu____11974,uu____11975);
              FStar_Syntax_Syntax.sigrng = uu____11976;
              FStar_Syntax_Syntax.sigquals = uu____11977;
              FStar_Syntax_Syntax.sigmeta = uu____11978;
              FStar_Syntax_Syntax.sigattrs = uu____11979;_},FStar_Pervasives_Native.None
            ),uu____11980)
          ->
          let uu____12033 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12033 (uvs, t)
      | uu____12034 ->
          let uu____12035 = name_not_found lid  in
          let uu____12040 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12035 uu____12040
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12061 = lookup_qname env lid  in
      match uu____12061 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____12068,uu____12069,uu____12070,uu____12071,uu____12072,dcs);
              FStar_Syntax_Syntax.sigrng = uu____12074;
              FStar_Syntax_Syntax.sigquals = uu____12075;
              FStar_Syntax_Syntax.sigmeta = uu____12076;
              FStar_Syntax_Syntax.sigattrs = uu____12077;_},uu____12078),uu____12079)
          -> (true, dcs)
      | uu____12140 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____12153 = lookup_qname env lid  in
      match uu____12153 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12154,uu____12155,uu____12156,l,uu____12158,uu____12159);
              FStar_Syntax_Syntax.sigrng = uu____12160;
              FStar_Syntax_Syntax.sigquals = uu____12161;
              FStar_Syntax_Syntax.sigmeta = uu____12162;
              FStar_Syntax_Syntax.sigattrs = uu____12163;_},uu____12164),uu____12165)
          -> l
      | uu____12220 ->
          let uu____12221 =
            let uu____12222 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____12222  in
          failwith uu____12221
  
let (lookup_definition_qninfo :
  delta_level Prims.list ->
    FStar_Ident.lident ->
      qninfo ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun lid  ->
      fun qninfo  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl))))
           in
        match qninfo with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____12271)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____12322,lbs),uu____12324)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____12352 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____12352
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____12384 -> FStar_Pervasives_Native.None)
        | uu____12389 -> FStar_Pervasives_Native.None
  
let (lookup_definition :
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let uu____12419 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____12419
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____12444),uu____12445) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____12494 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12515 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____12515
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____12534 = lookup_qname env ftv  in
      match uu____12534 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____12538) ->
          let uu____12583 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____12583 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____12604,t),r) ->
               let uu____12619 =
                 let uu____12620 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____12620 t  in
               FStar_Pervasives_Native.Some uu____12619)
      | uu____12621 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____12632 = try_lookup_effect_lid env ftv  in
      match uu____12632 with
      | FStar_Pervasives_Native.None  ->
          let uu____12635 = name_not_found ftv  in
          let uu____12640 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____12635 uu____12640
      | FStar_Pervasives_Native.Some k -> k
  
let (lookup_effect_abbrev :
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____12663 = lookup_qname env lid0  in
        match uu____12663 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____12674);
                FStar_Syntax_Syntax.sigrng = uu____12675;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____12677;
                FStar_Syntax_Syntax.sigattrs = uu____12678;_},FStar_Pervasives_Native.None
              ),uu____12679)
            ->
            let lid1 =
              let uu____12733 =
                let uu____12734 = FStar_Ident.range_of_lid lid  in
                let uu____12735 =
                  let uu____12736 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____12736  in
                FStar_Range.set_use_range uu____12734 uu____12735  in
              FStar_Ident.set_lid_range lid uu____12733  in
            let uu____12737 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___78_12741  ->
                      match uu___78_12741 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____12742 -> false))
               in
            if uu____12737
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____12756 =
                      let uu____12757 =
                        let uu____12758 = get_range env  in
                        FStar_Range.string_of_range uu____12758  in
                      let uu____12759 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____12760 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____12757 uu____12759 uu____12760
                       in
                    failwith uu____12756)
                  in
               match (binders, univs1) with
               | ([],uu____12767) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____12784,uu____12785::uu____12786::uu____12787) ->
                   let uu____12792 =
                     let uu____12793 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____12794 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____12793 uu____12794
                      in
                   failwith uu____12792
               | uu____12801 ->
                   let uu____12806 =
                     let uu____12811 =
                       let uu____12812 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____12812)  in
                     inst_tscheme_with uu____12811 insts  in
                   (match uu____12806 with
                    | (uu____12823,t) ->
                        let t1 =
                          let uu____12826 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____12826 t  in
                        let uu____12827 =
                          let uu____12828 = FStar_Syntax_Subst.compress t1
                             in
                          uu____12828.FStar_Syntax_Syntax.n  in
                        (match uu____12827 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____12875 -> failwith "Impossible")))
        | uu____12882 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____12905 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____12905 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____12918,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____12925 = find1 l2  in
            (match uu____12925 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____12932 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____12932 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____12936 = find1 l  in
            (match uu____12936 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 let uu____12940 =
                   FStar_Util.smap_add env.normalized_eff_names
                     l.FStar_Ident.str m
                    in
                 m)
         in
      let uu____12941 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____12941
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____12955 = lookup_qname env l1  in
      match uu____12955 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____12958;
              FStar_Syntax_Syntax.sigrng = uu____12959;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12961;
              FStar_Syntax_Syntax.sigattrs = uu____12962;_},uu____12963),uu____12964)
          -> q
      | uu____13015 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____13036 =
          let uu____13037 =
            let uu____13038 = FStar_Util.string_of_int i  in
            let uu____13039 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____13038 uu____13039
             in
          failwith uu____13037  in
        let uu____13040 = lookup_datacon env lid  in
        match uu____13040 with
        | (uu____13045,t) ->
            let uu____13047 =
              let uu____13048 = FStar_Syntax_Subst.compress t  in
              uu____13048.FStar_Syntax_Syntax.n  in
            (match uu____13047 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____13052) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____13083 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____13083
                      FStar_Pervasives_Native.fst)
             | uu____13092 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13103 = lookup_qname env l  in
      match uu____13103 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____13104,uu____13105,uu____13106);
              FStar_Syntax_Syntax.sigrng = uu____13107;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13109;
              FStar_Syntax_Syntax.sigattrs = uu____13110;_},uu____13111),uu____13112)
          ->
          FStar_Util.for_some
            (fun uu___79_13165  ->
               match uu___79_13165 with
               | FStar_Syntax_Syntax.Projector uu____13166 -> true
               | uu____13171 -> false) quals
      | uu____13172 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13183 = lookup_qname env lid  in
      match uu____13183 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13184,uu____13185,uu____13186,uu____13187,uu____13188,uu____13189);
              FStar_Syntax_Syntax.sigrng = uu____13190;
              FStar_Syntax_Syntax.sigquals = uu____13191;
              FStar_Syntax_Syntax.sigmeta = uu____13192;
              FStar_Syntax_Syntax.sigattrs = uu____13193;_},uu____13194),uu____13195)
          -> true
      | uu____13250 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13261 = lookup_qname env lid  in
      match uu____13261 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13262,uu____13263,uu____13264,uu____13265,uu____13266,uu____13267);
              FStar_Syntax_Syntax.sigrng = uu____13268;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____13270;
              FStar_Syntax_Syntax.sigattrs = uu____13271;_},uu____13272),uu____13273)
          ->
          FStar_Util.for_some
            (fun uu___80_13334  ->
               match uu___80_13334 with
               | FStar_Syntax_Syntax.RecordType uu____13335 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____13344 -> true
               | uu____13353 -> false) quals
      | uu____13354 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____13360,uu____13361);
            FStar_Syntax_Syntax.sigrng = uu____13362;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____13364;
            FStar_Syntax_Syntax.sigattrs = uu____13365;_},uu____13366),uu____13367)
        ->
        FStar_Util.for_some
          (fun uu___81_13424  ->
             match uu___81_13424 with
             | FStar_Syntax_Syntax.Action uu____13425 -> true
             | uu____13426 -> false) quals
    | uu____13427 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____13438 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____13438
  
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
    FStar_Parser_Const.op_Negation]  in
  fun env  ->
    fun head1  ->
      let uu____13452 =
        let uu____13453 = FStar_Syntax_Util.un_uinst head1  in
        uu____13453.FStar_Syntax_Syntax.n  in
      match uu____13452 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____13457 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____13468 = lookup_qname env l  in
      match uu____13468 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____13470),uu____13471) ->
          FStar_Util.for_some
            (fun uu___82_13519  ->
               match uu___82_13519 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____13520 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____13521 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____13592 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____13608) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____13625 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____13632 ->
                 FStar_Pervasives_Native.Some true
             | uu____13649 -> FStar_Pervasives_Native.Some false)
         in
      let uu____13650 =
        let uu____13653 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____13653 mapper  in
      match uu____13650 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____13703 = lookup_qname env lid  in
      match uu____13703 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13704,uu____13705,tps,uu____13707,uu____13708,uu____13709);
              FStar_Syntax_Syntax.sigrng = uu____13710;
              FStar_Syntax_Syntax.sigquals = uu____13711;
              FStar_Syntax_Syntax.sigmeta = uu____13712;
              FStar_Syntax_Syntax.sigattrs = uu____13713;_},uu____13714),uu____13715)
          -> FStar_List.length tps
      | uu____13778 ->
          let uu____13779 = name_not_found lid  in
          let uu____13784 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13779 uu____13784
  
let (effect_decl_opt :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____13828  ->
              match uu____13828 with
              | (d,uu____13836) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____13851 = effect_decl_opt env l  in
      match uu____13851 with
      | FStar_Pervasives_Native.None  ->
          let uu____13866 = name_not_found l  in
          let uu____13871 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____13866 uu____13871
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____13893  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____13912  ->
            fun t  -> fun wp  -> fun e  -> FStar_Util.return_all e))
  } 
let (join :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____13943 = FStar_Ident.lid_equals l1 l2  in
        if uu____13943
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____13951 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____13951
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____13959 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____14012  ->
                        match uu____14012 with
                        | (m1,m2,uu____14025,uu____14026,uu____14027) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____13959 with
              | FStar_Pervasives_Native.None  ->
                  let uu____14044 =
                    let uu____14049 =
                      let uu____14050 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____14051 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____14050
                        uu____14051
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____14049)
                     in
                  FStar_Errors.raise_error uu____14044 env.range
              | FStar_Pervasives_Native.Some
                  (uu____14058,uu____14059,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____14092 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____14092
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
  
let wp_sig_aux :
  'Auu____14108 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____14108)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____14137 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____14163  ->
                match uu____14163 with
                | (d,uu____14169) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____14137 with
      | FStar_Pervasives_Native.None  ->
          let uu____14180 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____14180
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____14193 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____14193 with
           | (uu____14204,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____14214)::(wp,uu____14216)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____14252 -> failwith "Impossible"))
  
let (wp_signature :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m 
let (null_wp_for_eff :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          let uu____14299 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____14299
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____14301 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____14301
             then
               FStar_Syntax_Syntax.mk_GTotal' res_t
                 (FStar_Pervasives_Native.Some res_u)
             else
               (let eff_name1 = norm_eff_name env eff_name  in
                let ed = get_effect_decl env eff_name1  in
                let null_wp =
                  inst_effect_fun_with [res_u] env ed
                    ed.FStar_Syntax_Syntax.null_wp
                   in
                let null_wp_res =
                  let uu____14309 = get_range env  in
                  let uu____14310 =
                    let uu____14317 =
                      let uu____14318 =
                        let uu____14333 =
                          let uu____14336 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____14336]  in
                        (null_wp, uu____14333)  in
                      FStar_Syntax_Syntax.Tm_app uu____14318  in
                    FStar_Syntax_Syntax.mk uu____14317  in
                  uu____14310 FStar_Pervasives_Native.None uu____14309  in
                let uu____14342 =
                  let uu____14343 =
                    let uu____14352 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____14352]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____14343;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____14342))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___98_14365 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___98_14365.order);
              joins = (uu___98_14365.joins)
            }  in
          let uu___99_14374 = env  in
          {
            solver = (uu___99_14374.solver);
            range = (uu___99_14374.range);
            curmodule = (uu___99_14374.curmodule);
            gamma = (uu___99_14374.gamma);
            gamma_cache = (uu___99_14374.gamma_cache);
            modules = (uu___99_14374.modules);
            expected_typ = (uu___99_14374.expected_typ);
            sigtab = (uu___99_14374.sigtab);
            is_pattern = (uu___99_14374.is_pattern);
            instantiate_imp = (uu___99_14374.instantiate_imp);
            effects;
            generalize = (uu___99_14374.generalize);
            letrecs = (uu___99_14374.letrecs);
            top_level = (uu___99_14374.top_level);
            check_uvars = (uu___99_14374.check_uvars);
            use_eq = (uu___99_14374.use_eq);
            is_iface = (uu___99_14374.is_iface);
            admit = (uu___99_14374.admit);
            lax = (uu___99_14374.lax);
            lax_universes = (uu___99_14374.lax_universes);
            failhard = (uu___99_14374.failhard);
            nosynth = (uu___99_14374.nosynth);
            tc_term = (uu___99_14374.tc_term);
            type_of = (uu___99_14374.type_of);
            universe_of = (uu___99_14374.universe_of);
            check_type_of = (uu___99_14374.check_type_of);
            use_bv_sorts = (uu___99_14374.use_bv_sorts);
            qtbl_name_and_index = (uu___99_14374.qtbl_name_and_index);
            normalized_eff_names = (uu___99_14374.normalized_eff_names);
            proof_ns = (uu___99_14374.proof_ns);
            synth_hook = (uu___99_14374.synth_hook);
            splice = (uu___99_14374.splice);
            is_native_tactic = (uu___99_14374.is_native_tactic);
            identifier_info = (uu___99_14374.identifier_info);
            tc_hooks = (uu___99_14374.tc_hooks);
            dsenv = (uu___99_14374.dsenv);
            dep_graph = (uu___99_14374.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____14404 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____14404  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____14562 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____14563 = l1 u t wp e  in
                                l2 u t uu____14562 uu____14563))
                | uu____14564 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____14632 = inst_tscheme_with lift_t [u]  in
            match uu____14632 with
            | (uu____14639,lift_t1) ->
                let uu____14641 =
                  let uu____14648 =
                    let uu____14649 =
                      let uu____14664 =
                        let uu____14667 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____14668 =
                          let uu____14671 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____14671]  in
                        uu____14667 :: uu____14668  in
                      (lift_t1, uu____14664)  in
                    FStar_Syntax_Syntax.Tm_app uu____14649  in
                  FStar_Syntax_Syntax.mk uu____14648  in
                uu____14641 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage"
             in
          let mk_mlift_term lift_t u r wp1 e =
            let uu____14743 = inst_tscheme_with lift_t [u]  in
            match uu____14743 with
            | (uu____14750,lift_t1) ->
                let uu____14752 =
                  let uu____14759 =
                    let uu____14760 =
                      let uu____14775 =
                        let uu____14778 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____14779 =
                          let uu____14782 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____14783 =
                            let uu____14786 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____14786]  in
                          uu____14782 :: uu____14783  in
                        uu____14778 :: uu____14779  in
                      (lift_t1, uu____14775)  in
                    FStar_Syntax_Syntax.Tm_app uu____14760  in
                  FStar_Syntax_Syntax.mk uu____14759  in
                uu____14752 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
             in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term
             in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            }  in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            }  in
          let print_mlift l =
            let bogus_term s =
              let uu____14842 =
                let uu____14843 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____14843
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____14842  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____14847 =
              let uu____14848 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____14848  in
            let uu____14849 =
              let uu____14850 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____14876 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____14876)
                 in
              FStar_Util.dflt "none" uu____14850  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____14847
              uu____14849
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____14902  ->
                    match uu____14902 with
                    | (e,uu____14910) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____14933 =
            match uu____14933 with
            | (i,j) ->
                let uu____14944 = FStar_Ident.lid_equals i j  in
                if uu____14944
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j)))
             in
          let order1 =
            let fold_fun order1 k =
              let uu____14976 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____14986 = FStar_Ident.lid_equals i k  in
                        if uu____14986
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____14997 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____14997
                                  then []
                                  else
                                    (let uu____15001 =
                                       let uu____15010 =
                                         find_edge order1 (i, k)  in
                                       let uu____15013 =
                                         find_edge order1 (k, j)  in
                                       (uu____15010, uu____15013)  in
                                     match uu____15001 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____15028 =
                                           compose_edges e1 e2  in
                                         [uu____15028]
                                     | uu____15029 -> [])))))
                 in
              FStar_List.append order1 uu____14976  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          let uu____15051 =
            FStar_All.pipe_right order2
              (FStar_List.iter
                 (fun edge1  ->
                    let uu____15059 =
                      (FStar_Ident.lid_equals edge1.msource
                         FStar_Parser_Const.effect_DIV_lid)
                        &&
                        (let uu____15061 =
                           lookup_effect_quals env edge1.mtarget  in
                         FStar_All.pipe_right uu____15061
                           (FStar_List.contains
                              FStar_Syntax_Syntax.TotalEffect))
                       in
                    if uu____15059
                    then
                      let uu____15066 =
                        let uu____15071 =
                          FStar_Util.format1
                            "Divergent computations cannot be included in an effect %s marked 'total'"
                            (edge1.mtarget).FStar_Ident.str
                           in
                        (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                          uu____15071)
                         in
                      let uu____15072 = get_range env  in
                      FStar_Errors.raise_error uu____15066 uu____15072
                    else ()))
             in
          let joins =
            FStar_All.pipe_right ms
              (FStar_List.collect
                 (fun i  ->
                    FStar_All.pipe_right ms
                      (FStar_List.collect
                         (fun j  ->
                            let join_opt =
                              let uu____15149 = FStar_Ident.lid_equals i j
                                 in
                              if uu____15149
                              then
                                FStar_Pervasives_Native.Some
                                  (i, (id_edge i), (id_edge i))
                              else
                                FStar_All.pipe_right ms
                                  (FStar_List.fold_left
                                     (fun bopt  ->
                                        fun k  ->
                                          let uu____15198 =
                                            let uu____15207 =
                                              find_edge order2 (i, k)  in
                                            let uu____15210 =
                                              find_edge order2 (j, k)  in
                                            (uu____15207, uu____15210)  in
                                          match uu____15198 with
                                          | (FStar_Pervasives_Native.Some
                                             ik,FStar_Pervasives_Native.Some
                                             jk) ->
                                              (match bopt with
                                               | FStar_Pervasives_Native.None
                                                    ->
                                                   FStar_Pervasives_Native.Some
                                                     (k, ik, jk)
                                               | FStar_Pervasives_Native.Some
                                                   (ub,uu____15252,uu____15253)
                                                   ->
                                                   let uu____15260 =
                                                     let uu____15265 =
                                                       let uu____15266 =
                                                         find_edge order2
                                                           (k, ub)
                                                          in
                                                       FStar_Util.is_some
                                                         uu____15266
                                                        in
                                                     let uu____15269 =
                                                       let uu____15270 =
                                                         find_edge order2
                                                           (ub, k)
                                                          in
                                                       FStar_Util.is_some
                                                         uu____15270
                                                        in
                                                     (uu____15265,
                                                       uu____15269)
                                                      in
                                                   (match uu____15260 with
                                                    | (true ,true ) ->
                                                        let uu____15281 =
                                                          FStar_Ident.lid_equals
                                                            k ub
                                                           in
                                                        if uu____15281
                                                        then
                                                          let uu____15290 =
                                                            FStar_Errors.log_issue
                                                              FStar_Range.dummyRange
                                                              (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                "Looking multiple times at the same upper bound candidate")
                                                             in
                                                          bopt
                                                        else
                                                          failwith
                                                            "Found a cycle in the lattice"
                                                    | (false ,false ) -> bopt
                                                    | (true ,false ) ->
                                                        FStar_Pervasives_Native.Some
                                                          (k, ik, jk)
                                                    | (false ,true ) -> bopt))
                                          | uu____15306 -> bopt)
                                     FStar_Pervasives_Native.None)
                               in
                            match join_opt with
                            | FStar_Pervasives_Native.None  -> []
                            | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                [(i, j, k, (e1.mlift), (e2.mlift))]))))
             in
          let effects =
            let uu___100_15379 = env.effects  in
            { decls = (uu___100_15379.decls); order = order2; joins }  in
          let uu___101_15380 = env  in
          {
            solver = (uu___101_15380.solver);
            range = (uu___101_15380.range);
            curmodule = (uu___101_15380.curmodule);
            gamma = (uu___101_15380.gamma);
            gamma_cache = (uu___101_15380.gamma_cache);
            modules = (uu___101_15380.modules);
            expected_typ = (uu___101_15380.expected_typ);
            sigtab = (uu___101_15380.sigtab);
            is_pattern = (uu___101_15380.is_pattern);
            instantiate_imp = (uu___101_15380.instantiate_imp);
            effects;
            generalize = (uu___101_15380.generalize);
            letrecs = (uu___101_15380.letrecs);
            top_level = (uu___101_15380.top_level);
            check_uvars = (uu___101_15380.check_uvars);
            use_eq = (uu___101_15380.use_eq);
            is_iface = (uu___101_15380.is_iface);
            admit = (uu___101_15380.admit);
            lax = (uu___101_15380.lax);
            lax_universes = (uu___101_15380.lax_universes);
            failhard = (uu___101_15380.failhard);
            nosynth = (uu___101_15380.nosynth);
            tc_term = (uu___101_15380.tc_term);
            type_of = (uu___101_15380.type_of);
            universe_of = (uu___101_15380.universe_of);
            check_type_of = (uu___101_15380.check_type_of);
            use_bv_sorts = (uu___101_15380.use_bv_sorts);
            qtbl_name_and_index = (uu___101_15380.qtbl_name_and_index);
            normalized_eff_names = (uu___101_15380.normalized_eff_names);
            proof_ns = (uu___101_15380.proof_ns);
            synth_hook = (uu___101_15380.synth_hook);
            splice = (uu___101_15380.splice);
            is_native_tactic = (uu___101_15380.is_native_tactic);
            identifier_info = (uu___101_15380.identifier_info);
            tc_hooks = (uu___101_15380.tc_hooks);
            dsenv = (uu___101_15380.dsenv);
            dep_graph = (uu___101_15380.dep_graph)
          }
      | uu____15381 -> env
  
let (comp_to_comp_typ :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t  in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____15409 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____15421 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____15421 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____15438 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____15438 with
           | (binders1,cdef1) ->
               let uu____15445 =
                 if
                   (FStar_List.length binders1) <>
                     ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                        (Prims.parse_int "1"))
                 then
                   let uu____15456 =
                     let uu____15461 =
                       let uu____15462 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____15467 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____15474 =
                         let uu____15475 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____15475  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____15462 uu____15467 uu____15474
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____15461)
                      in
                   FStar_Errors.raise_error uu____15456
                     comp.FStar_Syntax_Syntax.pos
                 else ()  in
               let inst1 =
                 let uu____15480 =
                   let uu____15489 =
                     FStar_Syntax_Syntax.as_arg
                       c.FStar_Syntax_Syntax.result_typ
                      in
                   uu____15489 :: (c.FStar_Syntax_Syntax.effect_args)  in
                 FStar_List.map2
                   (fun uu____15506  ->
                      fun uu____15507  ->
                        match (uu____15506, uu____15507) with
                        | ((x,uu____15529),(t,uu____15531)) ->
                            FStar_Syntax_Syntax.NT (x, t)) binders1
                   uu____15480
                  in
               let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
               let c2 =
                 let uu____15550 =
                   let uu___102_15551 = comp_to_comp_typ env c1  in
                   {
                     FStar_Syntax_Syntax.comp_univs =
                       (uu___102_15551.FStar_Syntax_Syntax.comp_univs);
                     FStar_Syntax_Syntax.effect_name =
                       (uu___102_15551.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___102_15551.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___102_15551.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (c.FStar_Syntax_Syntax.flags)
                   }  in
                 FStar_All.pipe_right uu____15550 FStar_Syntax_Syntax.mk_Comp
                  in
               unfold_effect_abbrev env c2)
  
let (effect_repr_aux :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.universe ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
            FStar_Pervasives_Native.option)
  =
  fun only_reifiable  ->
    fun env  ->
      fun c  ->
        fun u_c  ->
          let effect_name =
            norm_eff_name env (FStar_Syntax_Util.comp_effect_name c)  in
          let uu____15581 = effect_decl_opt env effect_name  in
          match uu____15581 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____15614 =
                only_reifiable &&
                  (let uu____15616 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____15616)
                 in
              if uu____15614
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____15632 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____15651 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____15680 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____15680
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____15681 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____15681
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____15691 =
                       let uu____15694 = get_range env  in
                       let uu____15695 =
                         let uu____15702 =
                           let uu____15703 =
                             let uu____15718 =
                               let uu____15721 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____15721; wp]  in
                             (repr, uu____15718)  in
                           FStar_Syntax_Syntax.Tm_app uu____15703  in
                         FStar_Syntax_Syntax.mk uu____15702  in
                       uu____15695 FStar_Pervasives_Native.None uu____15694
                        in
                     FStar_Pervasives_Native.Some uu____15691)
  
let (effect_repr :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c 
let (reify_comp :
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____15781 =
            let uu____15786 =
              let uu____15787 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____15787
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____15786)  in
          let uu____15788 = get_range env  in
          FStar_Errors.raise_error uu____15781 uu____15788  in
        let uu____15789 = effect_repr_aux true env c u_c  in
        match uu____15789 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
  
let (is_reifiable_effect : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid  in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
  
let (is_reifiable : env -> FStar_Syntax_Syntax.residual_comp -> Prims.bool) =
  fun env  ->
    fun c  -> is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect
  
let (is_reifiable_comp : env -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____15835 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____15846 =
        let uu____15847 = FStar_Syntax_Subst.compress t  in
        uu____15847.FStar_Syntax_Syntax.n  in
      match uu____15846 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____15850,c) ->
          is_reifiable_comp env c
      | uu____15868 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____15898)::uu____15899 -> x :: rest
        | (Binding_sig_inst uu____15908)::uu____15909 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____15924 = push1 x rest1  in local :: uu____15924
         in
      let uu____15927 = (env.tc_hooks).tc_push_in_gamma_hook env s  in
      let uu___103_15928 = env  in
      let uu____15929 = push1 s env.gamma  in
      {
        solver = (uu___103_15928.solver);
        range = (uu___103_15928.range);
        curmodule = (uu___103_15928.curmodule);
        gamma = uu____15929;
        gamma_cache = (uu___103_15928.gamma_cache);
        modules = (uu___103_15928.modules);
        expected_typ = (uu___103_15928.expected_typ);
        sigtab = (uu___103_15928.sigtab);
        is_pattern = (uu___103_15928.is_pattern);
        instantiate_imp = (uu___103_15928.instantiate_imp);
        effects = (uu___103_15928.effects);
        generalize = (uu___103_15928.generalize);
        letrecs = (uu___103_15928.letrecs);
        top_level = (uu___103_15928.top_level);
        check_uvars = (uu___103_15928.check_uvars);
        use_eq = (uu___103_15928.use_eq);
        is_iface = (uu___103_15928.is_iface);
        admit = (uu___103_15928.admit);
        lax = (uu___103_15928.lax);
        lax_universes = (uu___103_15928.lax_universes);
        failhard = (uu___103_15928.failhard);
        nosynth = (uu___103_15928.nosynth);
        tc_term = (uu___103_15928.tc_term);
        type_of = (uu___103_15928.type_of);
        universe_of = (uu___103_15928.universe_of);
        check_type_of = (uu___103_15928.check_type_of);
        use_bv_sorts = (uu___103_15928.use_bv_sorts);
        qtbl_name_and_index = (uu___103_15928.qtbl_name_and_index);
        normalized_eff_names = (uu___103_15928.normalized_eff_names);
        proof_ns = (uu___103_15928.proof_ns);
        synth_hook = (uu___103_15928.synth_hook);
        splice = (uu___103_15928.splice);
        is_native_tactic = (uu___103_15928.is_native_tactic);
        identifier_info = (uu___103_15928.identifier_info);
        tc_hooks = (uu___103_15928.tc_hooks);
        dsenv = (uu___103_15928.dsenv);
        dep_graph = (uu___103_15928.dep_graph)
      }
  
let (push_sigelt : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s))
         in
      build_lattice env1 s
  
let (push_sigelt_inst :
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env)
  =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us))
           in
        build_lattice env1 s
  
let (push_local_binding : env -> binding -> env) =
  fun env  ->
    fun b  ->
      let uu___104_15973 = env  in
      {
        solver = (uu___104_15973.solver);
        range = (uu___104_15973.range);
        curmodule = (uu___104_15973.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___104_15973.gamma_cache);
        modules = (uu___104_15973.modules);
        expected_typ = (uu___104_15973.expected_typ);
        sigtab = (uu___104_15973.sigtab);
        is_pattern = (uu___104_15973.is_pattern);
        instantiate_imp = (uu___104_15973.instantiate_imp);
        effects = (uu___104_15973.effects);
        generalize = (uu___104_15973.generalize);
        letrecs = (uu___104_15973.letrecs);
        top_level = (uu___104_15973.top_level);
        check_uvars = (uu___104_15973.check_uvars);
        use_eq = (uu___104_15973.use_eq);
        is_iface = (uu___104_15973.is_iface);
        admit = (uu___104_15973.admit);
        lax = (uu___104_15973.lax);
        lax_universes = (uu___104_15973.lax_universes);
        failhard = (uu___104_15973.failhard);
        nosynth = (uu___104_15973.nosynth);
        tc_term = (uu___104_15973.tc_term);
        type_of = (uu___104_15973.type_of);
        universe_of = (uu___104_15973.universe_of);
        check_type_of = (uu___104_15973.check_type_of);
        use_bv_sorts = (uu___104_15973.use_bv_sorts);
        qtbl_name_and_index = (uu___104_15973.qtbl_name_and_index);
        normalized_eff_names = (uu___104_15973.normalized_eff_names);
        proof_ns = (uu___104_15973.proof_ns);
        synth_hook = (uu___104_15973.synth_hook);
        splice = (uu___104_15973.splice);
        is_native_tactic = (uu___104_15973.is_native_tactic);
        identifier_info = (uu___104_15973.identifier_info);
        tc_hooks = (uu___104_15973.tc_hooks);
        dsenv = (uu___104_15973.dsenv);
        dep_graph = (uu___104_15973.dep_graph)
      }
  
let (push_bv : env -> FStar_Syntax_Syntax.bv -> env) =
  fun env  -> fun x  -> push_local_binding env (Binding_var x) 
let (push_bvs : env -> FStar_Syntax_Syntax.bv Prims.list -> env) =
  fun env  ->
    fun bvs  ->
      FStar_List.fold_left (fun env1  -> fun bv  -> push_bv env1 bv) env bvs
  
let (pop_bv :
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___105_16028 = env  in
             {
               solver = (uu___105_16028.solver);
               range = (uu___105_16028.range);
               curmodule = (uu___105_16028.curmodule);
               gamma = rest;
               gamma_cache = (uu___105_16028.gamma_cache);
               modules = (uu___105_16028.modules);
               expected_typ = (uu___105_16028.expected_typ);
               sigtab = (uu___105_16028.sigtab);
               is_pattern = (uu___105_16028.is_pattern);
               instantiate_imp = (uu___105_16028.instantiate_imp);
               effects = (uu___105_16028.effects);
               generalize = (uu___105_16028.generalize);
               letrecs = (uu___105_16028.letrecs);
               top_level = (uu___105_16028.top_level);
               check_uvars = (uu___105_16028.check_uvars);
               use_eq = (uu___105_16028.use_eq);
               is_iface = (uu___105_16028.is_iface);
               admit = (uu___105_16028.admit);
               lax = (uu___105_16028.lax);
               lax_universes = (uu___105_16028.lax_universes);
               failhard = (uu___105_16028.failhard);
               nosynth = (uu___105_16028.nosynth);
               tc_term = (uu___105_16028.tc_term);
               type_of = (uu___105_16028.type_of);
               universe_of = (uu___105_16028.universe_of);
               check_type_of = (uu___105_16028.check_type_of);
               use_bv_sorts = (uu___105_16028.use_bv_sorts);
               qtbl_name_and_index = (uu___105_16028.qtbl_name_and_index);
               normalized_eff_names = (uu___105_16028.normalized_eff_names);
               proof_ns = (uu___105_16028.proof_ns);
               synth_hook = (uu___105_16028.synth_hook);
               splice = (uu___105_16028.splice);
               is_native_tactic = (uu___105_16028.is_native_tactic);
               identifier_info = (uu___105_16028.identifier_info);
               tc_hooks = (uu___105_16028.tc_hooks);
               dsenv = (uu___105_16028.dsenv);
               dep_graph = (uu___105_16028.dep_graph)
             }))
    | uu____16029 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____16055  ->
             match uu____16055 with | (x,uu____16061) -> push_bv env1 x) env
        bs
  
let (binding_of_lb :
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,FStar_Syntax_Syntax.term'
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding)
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____16089 = ()  in
          let x2 =
            let uu___106_16091 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___106_16091.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___106_16091.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            }  in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
  
let (push_let_binding :
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env) =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
  
let (push_module : env -> FStar_Syntax_Syntax.modul -> env) =
  fun env  ->
    fun m  ->
      let uu____16130 = add_sigelts env m.FStar_Syntax_Syntax.exports  in
      let uu___107_16131 = env  in
      {
        solver = (uu___107_16131.solver);
        range = (uu___107_16131.range);
        curmodule = (uu___107_16131.curmodule);
        gamma = [];
        gamma_cache = (uu___107_16131.gamma_cache);
        modules = (m :: (env.modules));
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___107_16131.sigtab);
        is_pattern = (uu___107_16131.is_pattern);
        instantiate_imp = (uu___107_16131.instantiate_imp);
        effects = (uu___107_16131.effects);
        generalize = (uu___107_16131.generalize);
        letrecs = (uu___107_16131.letrecs);
        top_level = (uu___107_16131.top_level);
        check_uvars = (uu___107_16131.check_uvars);
        use_eq = (uu___107_16131.use_eq);
        is_iface = (uu___107_16131.is_iface);
        admit = (uu___107_16131.admit);
        lax = (uu___107_16131.lax);
        lax_universes = (uu___107_16131.lax_universes);
        failhard = (uu___107_16131.failhard);
        nosynth = (uu___107_16131.nosynth);
        tc_term = (uu___107_16131.tc_term);
        type_of = (uu___107_16131.type_of);
        universe_of = (uu___107_16131.universe_of);
        check_type_of = (uu___107_16131.check_type_of);
        use_bv_sorts = (uu___107_16131.use_bv_sorts);
        qtbl_name_and_index = (uu___107_16131.qtbl_name_and_index);
        normalized_eff_names = (uu___107_16131.normalized_eff_names);
        proof_ns = (uu___107_16131.proof_ns);
        synth_hook = (uu___107_16131.synth_hook);
        splice = (uu___107_16131.splice);
        is_native_tactic = (uu___107_16131.is_native_tactic);
        identifier_info = (uu___107_16131.identifier_info);
        tc_hooks = (uu___107_16131.tc_hooks);
        dsenv = (uu___107_16131.dsenv);
        dep_graph = (uu___107_16131.dep_graph)
      }
  
let (push_univ_vars : env -> FStar_Syntax_Syntax.univ_names -> env) =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
  
let (open_universes_in :
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____16173 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____16173 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____16201 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____16201)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___108_16218 = env  in
      {
        solver = (uu___108_16218.solver);
        range = (uu___108_16218.range);
        curmodule = (uu___108_16218.curmodule);
        gamma = (uu___108_16218.gamma);
        gamma_cache = (uu___108_16218.gamma_cache);
        modules = (uu___108_16218.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___108_16218.sigtab);
        is_pattern = (uu___108_16218.is_pattern);
        instantiate_imp = (uu___108_16218.instantiate_imp);
        effects = (uu___108_16218.effects);
        generalize = (uu___108_16218.generalize);
        letrecs = (uu___108_16218.letrecs);
        top_level = (uu___108_16218.top_level);
        check_uvars = (uu___108_16218.check_uvars);
        use_eq = false;
        is_iface = (uu___108_16218.is_iface);
        admit = (uu___108_16218.admit);
        lax = (uu___108_16218.lax);
        lax_universes = (uu___108_16218.lax_universes);
        failhard = (uu___108_16218.failhard);
        nosynth = (uu___108_16218.nosynth);
        tc_term = (uu___108_16218.tc_term);
        type_of = (uu___108_16218.type_of);
        universe_of = (uu___108_16218.universe_of);
        check_type_of = (uu___108_16218.check_type_of);
        use_bv_sorts = (uu___108_16218.use_bv_sorts);
        qtbl_name_and_index = (uu___108_16218.qtbl_name_and_index);
        normalized_eff_names = (uu___108_16218.normalized_eff_names);
        proof_ns = (uu___108_16218.proof_ns);
        synth_hook = (uu___108_16218.synth_hook);
        splice = (uu___108_16218.splice);
        is_native_tactic = (uu___108_16218.is_native_tactic);
        identifier_info = (uu___108_16218.identifier_info);
        tc_hooks = (uu___108_16218.tc_hooks);
        dsenv = (uu___108_16218.dsenv);
        dep_graph = (uu___108_16218.dep_graph)
      }
  
let (expected_typ :
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
  
let (clear_expected_typ :
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun env_  ->
    let uu____16246 = expected_typ env_  in
    ((let uu___109_16252 = env_  in
      {
        solver = (uu___109_16252.solver);
        range = (uu___109_16252.range);
        curmodule = (uu___109_16252.curmodule);
        gamma = (uu___109_16252.gamma);
        gamma_cache = (uu___109_16252.gamma_cache);
        modules = (uu___109_16252.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___109_16252.sigtab);
        is_pattern = (uu___109_16252.is_pattern);
        instantiate_imp = (uu___109_16252.instantiate_imp);
        effects = (uu___109_16252.effects);
        generalize = (uu___109_16252.generalize);
        letrecs = (uu___109_16252.letrecs);
        top_level = (uu___109_16252.top_level);
        check_uvars = (uu___109_16252.check_uvars);
        use_eq = false;
        is_iface = (uu___109_16252.is_iface);
        admit = (uu___109_16252.admit);
        lax = (uu___109_16252.lax);
        lax_universes = (uu___109_16252.lax_universes);
        failhard = (uu___109_16252.failhard);
        nosynth = (uu___109_16252.nosynth);
        tc_term = (uu___109_16252.tc_term);
        type_of = (uu___109_16252.type_of);
        universe_of = (uu___109_16252.universe_of);
        check_type_of = (uu___109_16252.check_type_of);
        use_bv_sorts = (uu___109_16252.use_bv_sorts);
        qtbl_name_and_index = (uu___109_16252.qtbl_name_and_index);
        normalized_eff_names = (uu___109_16252.normalized_eff_names);
        proof_ns = (uu___109_16252.proof_ns);
        synth_hook = (uu___109_16252.synth_hook);
        splice = (uu___109_16252.splice);
        is_native_tactic = (uu___109_16252.is_native_tactic);
        identifier_info = (uu___109_16252.identifier_info);
        tc_hooks = (uu___109_16252.tc_hooks);
        dsenv = (uu___109_16252.dsenv);
        dep_graph = (uu___109_16252.dep_graph)
      }), uu____16246)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____16262 =
      let uu____16265 = FStar_Ident.id_of_text ""  in [uu____16265]  in
    FStar_Ident.lid_of_ids uu____16262  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____16271 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____16271
        then
          let uu____16274 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___83_16284  ->
                    match uu___83_16284 with
                    | Binding_sig (uu____16287,se) -> [se]
                    | uu____16293 -> []))
             in
          FStar_All.pipe_right uu____16274 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      let uu____16299 = add_sigelts env sigs  in
      let uu___110_16300 = env  in
      {
        solver = (uu___110_16300.solver);
        range = (uu___110_16300.range);
        curmodule = empty_lid;
        gamma = [];
        gamma_cache = (uu___110_16300.gamma_cache);
        modules = (m :: (env.modules));
        expected_typ = (uu___110_16300.expected_typ);
        sigtab = (uu___110_16300.sigtab);
        is_pattern = (uu___110_16300.is_pattern);
        instantiate_imp = (uu___110_16300.instantiate_imp);
        effects = (uu___110_16300.effects);
        generalize = (uu___110_16300.generalize);
        letrecs = (uu___110_16300.letrecs);
        top_level = (uu___110_16300.top_level);
        check_uvars = (uu___110_16300.check_uvars);
        use_eq = (uu___110_16300.use_eq);
        is_iface = (uu___110_16300.is_iface);
        admit = (uu___110_16300.admit);
        lax = (uu___110_16300.lax);
        lax_universes = (uu___110_16300.lax_universes);
        failhard = (uu___110_16300.failhard);
        nosynth = (uu___110_16300.nosynth);
        tc_term = (uu___110_16300.tc_term);
        type_of = (uu___110_16300.type_of);
        universe_of = (uu___110_16300.universe_of);
        check_type_of = (uu___110_16300.check_type_of);
        use_bv_sorts = (uu___110_16300.use_bv_sorts);
        qtbl_name_and_index = (uu___110_16300.qtbl_name_and_index);
        normalized_eff_names = (uu___110_16300.normalized_eff_names);
        proof_ns = (uu___110_16300.proof_ns);
        synth_hook = (uu___110_16300.synth_hook);
        splice = (uu___110_16300.splice);
        is_native_tactic = (uu___110_16300.is_native_tactic);
        identifier_info = (uu___110_16300.identifier_info);
        tc_hooks = (uu___110_16300.tc_hooks);
        dsenv = (uu___110_16300.dsenv);
        dep_graph = (uu___110_16300.dep_graph)
      }
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____16391)::tl1 -> aux out tl1
      | (Binding_lid (uu____16395,(uu____16396,t)))::tl1 ->
          let uu____16411 =
            let uu____16418 = FStar_Syntax_Free.uvars t  in
            ext out uu____16418  in
          aux uu____16411 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16425;
            FStar_Syntax_Syntax.index = uu____16426;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16433 =
            let uu____16440 = FStar_Syntax_Free.uvars t  in
            ext out uu____16440  in
          aux uu____16433 tl1
      | (Binding_sig uu____16447)::uu____16448 -> out
      | (Binding_sig_inst uu____16457)::uu____16458 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____16523)::tl1 -> aux out tl1
      | (Binding_univ uu____16535)::tl1 -> aux out tl1
      | (Binding_lid (uu____16539,(uu____16540,t)))::tl1 ->
          let uu____16555 =
            let uu____16558 = FStar_Syntax_Free.univs t  in
            ext out uu____16558  in
          aux uu____16555 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16561;
            FStar_Syntax_Syntax.index = uu____16562;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16569 =
            let uu____16572 = FStar_Syntax_Free.univs t  in
            ext out uu____16572  in
          aux uu____16569 tl1
      | (Binding_sig uu____16575)::uu____16576 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____16639)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____16655 = FStar_Util.set_add uname out  in
          aux uu____16655 tl1
      | (Binding_lid (uu____16658,(uu____16659,t)))::tl1 ->
          let uu____16674 =
            let uu____16677 = FStar_Syntax_Free.univnames t  in
            ext out uu____16677  in
          aux uu____16674 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____16680;
            FStar_Syntax_Syntax.index = uu____16681;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____16688 =
            let uu____16691 = FStar_Syntax_Free.univnames t  in
            ext out uu____16691  in
          aux uu____16688 tl1
      | (Binding_sig uu____16694)::uu____16695 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___84_16721  ->
            match uu___84_16721 with
            | Binding_var x -> [x]
            | Binding_lid uu____16725 -> []
            | Binding_sig uu____16730 -> []
            | Binding_univ uu____16737 -> []
            | Binding_sig_inst uu____16738 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____16756 =
      let uu____16759 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____16759
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____16756 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> unit) =
  fun env  ->
    let uu____16787 =
      let uu____16788 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___85_16798  ->
                match uu___85_16798 with
                | Binding_var x ->
                    let uu____16800 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____16800
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____16803) ->
                    let uu____16804 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____16804
                | Binding_sig (ls,uu____16806) ->
                    let uu____16811 =
                      let uu____16812 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____16812
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____16811
                | Binding_sig_inst (ls,uu____16822,uu____16823) ->
                    let uu____16828 =
                      let uu____16829 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____16829
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____16828))
         in
      FStar_All.pipe_right uu____16788 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____16787 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____16850 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____16850
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____16878  ->
                 fun uu____16879  ->
                   match (uu____16878, uu____16879) with
                   | ((b1,uu____16897),(b2,uu____16899)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___86_16950  ->
    match uu___86_16950 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____16951 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___87_16971  ->
             match uu___87_16971 with
             | Binding_sig (lids,uu____16977) -> FStar_List.append lids keys
             | uu____16982 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____16988  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____17030) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____17049,uu____17050) -> false  in
      let uu____17059 =
        FStar_List.tryFind
          (fun uu____17077  ->
             match uu____17077 with | (p,uu____17085) -> list_prefix p path)
          env.proof_ns
         in
      match uu____17059 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____17096,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____17118 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____17118
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___111_17136 = e  in
        {
          solver = (uu___111_17136.solver);
          range = (uu___111_17136.range);
          curmodule = (uu___111_17136.curmodule);
          gamma = (uu___111_17136.gamma);
          gamma_cache = (uu___111_17136.gamma_cache);
          modules = (uu___111_17136.modules);
          expected_typ = (uu___111_17136.expected_typ);
          sigtab = (uu___111_17136.sigtab);
          is_pattern = (uu___111_17136.is_pattern);
          instantiate_imp = (uu___111_17136.instantiate_imp);
          effects = (uu___111_17136.effects);
          generalize = (uu___111_17136.generalize);
          letrecs = (uu___111_17136.letrecs);
          top_level = (uu___111_17136.top_level);
          check_uvars = (uu___111_17136.check_uvars);
          use_eq = (uu___111_17136.use_eq);
          is_iface = (uu___111_17136.is_iface);
          admit = (uu___111_17136.admit);
          lax = (uu___111_17136.lax);
          lax_universes = (uu___111_17136.lax_universes);
          failhard = (uu___111_17136.failhard);
          nosynth = (uu___111_17136.nosynth);
          tc_term = (uu___111_17136.tc_term);
          type_of = (uu___111_17136.type_of);
          universe_of = (uu___111_17136.universe_of);
          check_type_of = (uu___111_17136.check_type_of);
          use_bv_sorts = (uu___111_17136.use_bv_sorts);
          qtbl_name_and_index = (uu___111_17136.qtbl_name_and_index);
          normalized_eff_names = (uu___111_17136.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___111_17136.synth_hook);
          splice = (uu___111_17136.splice);
          is_native_tactic = (uu___111_17136.is_native_tactic);
          identifier_info = (uu___111_17136.identifier_info);
          tc_hooks = (uu___111_17136.tc_hooks);
          dsenv = (uu___111_17136.dsenv);
          dep_graph = (uu___111_17136.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___112_17176 = e  in
      {
        solver = (uu___112_17176.solver);
        range = (uu___112_17176.range);
        curmodule = (uu___112_17176.curmodule);
        gamma = (uu___112_17176.gamma);
        gamma_cache = (uu___112_17176.gamma_cache);
        modules = (uu___112_17176.modules);
        expected_typ = (uu___112_17176.expected_typ);
        sigtab = (uu___112_17176.sigtab);
        is_pattern = (uu___112_17176.is_pattern);
        instantiate_imp = (uu___112_17176.instantiate_imp);
        effects = (uu___112_17176.effects);
        generalize = (uu___112_17176.generalize);
        letrecs = (uu___112_17176.letrecs);
        top_level = (uu___112_17176.top_level);
        check_uvars = (uu___112_17176.check_uvars);
        use_eq = (uu___112_17176.use_eq);
        is_iface = (uu___112_17176.is_iface);
        admit = (uu___112_17176.admit);
        lax = (uu___112_17176.lax);
        lax_universes = (uu___112_17176.lax_universes);
        failhard = (uu___112_17176.failhard);
        nosynth = (uu___112_17176.nosynth);
        tc_term = (uu___112_17176.tc_term);
        type_of = (uu___112_17176.type_of);
        universe_of = (uu___112_17176.universe_of);
        check_type_of = (uu___112_17176.check_type_of);
        use_bv_sorts = (uu___112_17176.use_bv_sorts);
        qtbl_name_and_index = (uu___112_17176.qtbl_name_and_index);
        normalized_eff_names = (uu___112_17176.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___112_17176.synth_hook);
        splice = (uu___112_17176.splice);
        is_native_tactic = (uu___112_17176.is_native_tactic);
        identifier_info = (uu___112_17176.identifier_info);
        tc_hooks = (uu___112_17176.tc_hooks);
        dsenv = (uu___112_17176.dsenv);
        dep_graph = (uu___112_17176.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____17191 = FStar_Syntax_Free.names t  in
      let uu____17194 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____17191 uu____17194
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____17215 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____17215
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____17223 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____17223
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____17242 =
      match uu____17242 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____17258 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____17258)
       in
    let uu____17260 =
      let uu____17263 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____17263 FStar_List.rev  in
    FStar_All.pipe_right uu____17260 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____17280  -> ());
    push = (fun uu____17282  -> ());
    pop = (fun uu____17284  -> ());
    encode_modul = (fun uu____17287  -> fun uu____17288  -> ());
    encode_sig = (fun uu____17291  -> fun uu____17292  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____17298 =
             let uu____17305 = FStar_Options.peek ()  in (e, g, uu____17305)
              in
           [uu____17298]);
    solve = (fun uu____17321  -> fun uu____17322  -> fun uu____17323  -> ());
    finish = (fun uu____17329  -> ());
    refresh = (fun uu____17331  -> ())
  } 
let (mk_copy : env -> env) =
  fun en  ->
    let uu___113_17337 = en  in
    let uu____17338 = FStar_Util.smap_copy en.gamma_cache  in
    let uu____17341 = FStar_Util.smap_copy en.sigtab  in
    let uu____17344 = FStar_Syntax_DsEnv.mk_copy en.dsenv  in
    {
      solver = (uu___113_17337.solver);
      range = (uu___113_17337.range);
      curmodule = (uu___113_17337.curmodule);
      gamma = (uu___113_17337.gamma);
      gamma_cache = uu____17338;
      modules = (uu___113_17337.modules);
      expected_typ = (uu___113_17337.expected_typ);
      sigtab = uu____17341;
      is_pattern = (uu___113_17337.is_pattern);
      instantiate_imp = (uu___113_17337.instantiate_imp);
      effects = (uu___113_17337.effects);
      generalize = (uu___113_17337.generalize);
      letrecs = (uu___113_17337.letrecs);
      top_level = (uu___113_17337.top_level);
      check_uvars = (uu___113_17337.check_uvars);
      use_eq = (uu___113_17337.use_eq);
      is_iface = (uu___113_17337.is_iface);
      admit = (uu___113_17337.admit);
      lax = (uu___113_17337.lax);
      lax_universes = (uu___113_17337.lax_universes);
      failhard = (uu___113_17337.failhard);
      nosynth = (uu___113_17337.nosynth);
      tc_term = (uu___113_17337.tc_term);
      type_of = (uu___113_17337.type_of);
      universe_of = (uu___113_17337.universe_of);
      check_type_of = (uu___113_17337.check_type_of);
      use_bv_sorts = (uu___113_17337.use_bv_sorts);
      qtbl_name_and_index = (uu___113_17337.qtbl_name_and_index);
      normalized_eff_names = (uu___113_17337.normalized_eff_names);
      proof_ns = (uu___113_17337.proof_ns);
      synth_hook = (uu___113_17337.synth_hook);
      splice = (uu___113_17337.splice);
      is_native_tactic = (uu___113_17337.is_native_tactic);
      identifier_info = (uu___113_17337.identifier_info);
      tc_hooks = (uu___113_17337.tc_hooks);
      dsenv = uu____17344;
      dep_graph = (uu___113_17337.dep_graph)
    }
  