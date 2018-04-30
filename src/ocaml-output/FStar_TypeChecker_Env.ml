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
    match projectee with | Binding_var _0 -> true | uu____50 -> false
  
let (__proj__Binding_var__item___0 : binding -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_lid : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____68 -> false
  
let (__proj__Binding_lid__item___0 :
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0 
let (uu___is_Binding_sig : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____100 -> false
  
let (__proj__Binding_sig__item___0 :
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0 
let (uu___is_Binding_univ : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____132 -> false
  
let (__proj__Binding_univ__item___0 :
  binding -> FStar_Syntax_Syntax.univ_name) =
  fun projectee  -> match projectee with | Binding_univ _0 -> _0 
let (uu___is_Binding_sig_inst : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____154 -> false
  
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
    match projectee with | NoDelta  -> true | uu____196 -> false
  
let (uu___is_Inlining : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____202 -> false
  
let (uu___is_Eager_unfolding_only : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____208 -> false
  
let (uu___is_Unfold : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____215 -> false
  
let (__proj__Unfold__item___0 :
  delta_level -> FStar_Syntax_Syntax.delta_depth) =
  fun projectee  -> match projectee with | Unfold _0 -> _0 
let (uu___is_UnfoldTac : delta_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnfoldTac  -> true | uu____228 -> false
  
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
  snapshot:
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2
    ;
  rollback:
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit
    ;
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
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__init
  
let (__proj__Mksolver_t__item__push : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__push
  
let (__proj__Mksolver_t__item__pop : solver_t -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__pop
  
let (__proj__Mksolver_t__item__snapshot :
  solver_t ->
    Prims.string ->
      ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,
        unit) FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__snapshot
  
let (__proj__Mksolver_t__item__rollback :
  solver_t ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option -> unit)
  =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__rollback
  
let (__proj__Mksolver_t__item__encode_modul :
  solver_t -> env -> FStar_Syntax_Syntax.modul -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__encode_modul
  
let (__proj__Mksolver_t__item__encode_sig :
  solver_t -> env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
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
        snapshot = __fname__snapshot; rollback = __fname__rollback;
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
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__solve
  
let (__proj__Mksolver_t__item__finish : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        encode_modul = __fname__encode_modul;
        encode_sig = __fname__encode_sig; preprocess = __fname__preprocess;
        solve = __fname__solve; finish = __fname__finish;
        refresh = __fname__refresh;_} -> __fname__finish
  
let (__proj__Mksolver_t__item__refresh : solver_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { init = __fname__init; push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
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
  
type solver_depth_t =
  (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                  show]
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
           (fun uu___99_8030  ->
              match uu___99_8030 with
              | Binding_var x ->
                  let y =
                    let uu____8033 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Subst.subst subst1 uu____8033  in
                  let uu____8034 =
                    let uu____8035 = FStar_Syntax_Subst.compress y  in
                    uu____8035.FStar_Syntax_Syntax.n  in
                  (match uu____8034 with
                   | FStar_Syntax_Syntax.Tm_name y1 ->
                       let uu____8039 =
                         let uu___114_8040 = y1  in
                         let uu____8041 =
                           FStar_Syntax_Subst.subst subst1
                             x.FStar_Syntax_Syntax.sort
                            in
                         {
                           FStar_Syntax_Syntax.ppname =
                             (uu___114_8040.FStar_Syntax_Syntax.ppname);
                           FStar_Syntax_Syntax.index =
                             (uu___114_8040.FStar_Syntax_Syntax.index);
                           FStar_Syntax_Syntax.sort = uu____8041
                         }  in
                       Binding_var uu____8039
                   | uu____8044 -> failwith "Not a renaming")
              | b -> b))
  
let (rename_env : FStar_Syntax_Syntax.subst_t -> env -> env) =
  fun subst1  ->
    fun env  ->
      let uu___115_8056 = env  in
      let uu____8057 = rename_gamma subst1 env.gamma  in
      {
        solver = (uu___115_8056.solver);
        range = (uu___115_8056.range);
        curmodule = (uu___115_8056.curmodule);
        gamma = uu____8057;
        gamma_cache = (uu___115_8056.gamma_cache);
        modules = (uu___115_8056.modules);
        expected_typ = (uu___115_8056.expected_typ);
        sigtab = (uu___115_8056.sigtab);
        is_pattern = (uu___115_8056.is_pattern);
        instantiate_imp = (uu___115_8056.instantiate_imp);
        effects = (uu___115_8056.effects);
        generalize = (uu___115_8056.generalize);
        letrecs = (uu___115_8056.letrecs);
        top_level = (uu___115_8056.top_level);
        check_uvars = (uu___115_8056.check_uvars);
        use_eq = (uu___115_8056.use_eq);
        is_iface = (uu___115_8056.is_iface);
        admit = (uu___115_8056.admit);
        lax = (uu___115_8056.lax);
        lax_universes = (uu___115_8056.lax_universes);
        failhard = (uu___115_8056.failhard);
        nosynth = (uu___115_8056.nosynth);
        tc_term = (uu___115_8056.tc_term);
        type_of = (uu___115_8056.type_of);
        universe_of = (uu___115_8056.universe_of);
        check_type_of = (uu___115_8056.check_type_of);
        use_bv_sorts = (uu___115_8056.use_bv_sorts);
        qtbl_name_and_index = (uu___115_8056.qtbl_name_and_index);
        normalized_eff_names = (uu___115_8056.normalized_eff_names);
        proof_ns = (uu___115_8056.proof_ns);
        synth_hook = (uu___115_8056.synth_hook);
        splice = (uu___115_8056.splice);
        is_native_tactic = (uu___115_8056.is_native_tactic);
        identifier_info = (uu___115_8056.identifier_info);
        tc_hooks = (uu___115_8056.tc_hooks);
        dsenv = (uu___115_8056.dsenv);
        dep_graph = (uu___115_8056.dep_graph)
      }
  
let (default_tc_hooks : tcenv_hooks) =
  { tc_push_in_gamma_hook = (fun uu____8064  -> fun uu____8065  -> ()) } 
let (tc_hooks : env -> tcenv_hooks) = fun env  -> env.tc_hooks 
let (set_tc_hooks : env -> tcenv_hooks -> env) =
  fun env  ->
    fun hooks  ->
      let uu___116_8081 = env  in
      {
        solver = (uu___116_8081.solver);
        range = (uu___116_8081.range);
        curmodule = (uu___116_8081.curmodule);
        gamma = (uu___116_8081.gamma);
        gamma_cache = (uu___116_8081.gamma_cache);
        modules = (uu___116_8081.modules);
        expected_typ = (uu___116_8081.expected_typ);
        sigtab = (uu___116_8081.sigtab);
        is_pattern = (uu___116_8081.is_pattern);
        instantiate_imp = (uu___116_8081.instantiate_imp);
        effects = (uu___116_8081.effects);
        generalize = (uu___116_8081.generalize);
        letrecs = (uu___116_8081.letrecs);
        top_level = (uu___116_8081.top_level);
        check_uvars = (uu___116_8081.check_uvars);
        use_eq = (uu___116_8081.use_eq);
        is_iface = (uu___116_8081.is_iface);
        admit = (uu___116_8081.admit);
        lax = (uu___116_8081.lax);
        lax_universes = (uu___116_8081.lax_universes);
        failhard = (uu___116_8081.failhard);
        nosynth = (uu___116_8081.nosynth);
        tc_term = (uu___116_8081.tc_term);
        type_of = (uu___116_8081.type_of);
        universe_of = (uu___116_8081.universe_of);
        check_type_of = (uu___116_8081.check_type_of);
        use_bv_sorts = (uu___116_8081.use_bv_sorts);
        qtbl_name_and_index = (uu___116_8081.qtbl_name_and_index);
        normalized_eff_names = (uu___116_8081.normalized_eff_names);
        proof_ns = (uu___116_8081.proof_ns);
        synth_hook = (uu___116_8081.synth_hook);
        splice = (uu___116_8081.splice);
        is_native_tactic = (uu___116_8081.is_native_tactic);
        identifier_info = (uu___116_8081.identifier_info);
        tc_hooks = hooks;
        dsenv = (uu___116_8081.dsenv);
        dep_graph = (uu___116_8081.dep_graph)
      }
  
let (set_dep_graph : env -> FStar_Parser_Dep.deps -> env) =
  fun e  ->
    fun g  ->
      let uu___117_8092 = e  in
      {
        solver = (uu___117_8092.solver);
        range = (uu___117_8092.range);
        curmodule = (uu___117_8092.curmodule);
        gamma = (uu___117_8092.gamma);
        gamma_cache = (uu___117_8092.gamma_cache);
        modules = (uu___117_8092.modules);
        expected_typ = (uu___117_8092.expected_typ);
        sigtab = (uu___117_8092.sigtab);
        is_pattern = (uu___117_8092.is_pattern);
        instantiate_imp = (uu___117_8092.instantiate_imp);
        effects = (uu___117_8092.effects);
        generalize = (uu___117_8092.generalize);
        letrecs = (uu___117_8092.letrecs);
        top_level = (uu___117_8092.top_level);
        check_uvars = (uu___117_8092.check_uvars);
        use_eq = (uu___117_8092.use_eq);
        is_iface = (uu___117_8092.is_iface);
        admit = (uu___117_8092.admit);
        lax = (uu___117_8092.lax);
        lax_universes = (uu___117_8092.lax_universes);
        failhard = (uu___117_8092.failhard);
        nosynth = (uu___117_8092.nosynth);
        tc_term = (uu___117_8092.tc_term);
        type_of = (uu___117_8092.type_of);
        universe_of = (uu___117_8092.universe_of);
        check_type_of = (uu___117_8092.check_type_of);
        use_bv_sorts = (uu___117_8092.use_bv_sorts);
        qtbl_name_and_index = (uu___117_8092.qtbl_name_and_index);
        normalized_eff_names = (uu___117_8092.normalized_eff_names);
        proof_ns = (uu___117_8092.proof_ns);
        synth_hook = (uu___117_8092.synth_hook);
        splice = (uu___117_8092.splice);
        is_native_tactic = (uu___117_8092.is_native_tactic);
        identifier_info = (uu___117_8092.identifier_info);
        tc_hooks = (uu___117_8092.tc_hooks);
        dsenv = (uu___117_8092.dsenv);
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
      | (NoDelta ,uu____8115) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____8116,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____8117,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____8118 -> false
  
let (default_table_size : Prims.int) = (Prims.parse_int "200") 
let new_sigtab : 'Auu____8127 . unit -> 'Auu____8127 FStar_Util.smap =
  fun uu____8134  -> FStar_Util.smap_create default_table_size 
let new_gamma_cache : 'Auu____8139 . unit -> 'Auu____8139 FStar_Util.smap =
  fun uu____8146  -> FStar_Util.smap_create (Prims.parse_int "100") 
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
                let uu____8256 = new_gamma_cache ()  in
                let uu____8259 = new_sigtab ()  in
                let uu____8262 =
                  let uu____8275 =
                    FStar_Util.smap_create (Prims.parse_int "10")  in
                  (uu____8275, FStar_Pervasives_Native.None)  in
                let uu____8290 =
                  FStar_Util.smap_create (Prims.parse_int "20")  in
                let uu____8293 = FStar_Options.using_facts_from ()  in
                let uu____8294 =
                  FStar_Util.mk_ref
                    FStar_TypeChecker_Common.id_info_table_empty
                   in
                let uu____8297 = FStar_Syntax_DsEnv.empty_env ()  in
                {
                  solver;
                  range = FStar_Range.dummyRange;
                  curmodule = module_lid;
                  gamma = [];
                  gamma_cache = uu____8256;
                  modules = [];
                  expected_typ = FStar_Pervasives_Native.None;
                  sigtab = uu____8259;
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
                  qtbl_name_and_index = uu____8262;
                  normalized_eff_names = uu____8290;
                  proof_ns = uu____8293;
                  synth_hook =
                    (fun e  ->
                       fun g  ->
                         fun tau  -> failwith "no synthesizer available");
                  splice =
                    (fun e  -> fun tau  -> failwith "no splicer available");
                  is_native_tactic = (fun uu____8333  -> false);
                  identifier_info = uu____8294;
                  tc_hooks = default_tc_hooks;
                  dsenv = uu____8297;
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
  fun uu____8424  ->
    let uu____8425 = FStar_ST.op_Bang query_indices  in
    match uu____8425 with
    | [] -> failwith "Empty query indices!"
    | uu____8479 ->
        let uu____8488 =
          let uu____8497 =
            let uu____8504 = FStar_ST.op_Bang query_indices  in
            FStar_List.hd uu____8504  in
          let uu____8558 = FStar_ST.op_Bang query_indices  in uu____8497 ::
            uu____8558
           in
        FStar_ST.op_Colon_Equals query_indices uu____8488
  
let (pop_query_indices : unit -> unit) =
  fun uu____8655  ->
    let uu____8656 = FStar_ST.op_Bang query_indices  in
    match uu____8656 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.op_Colon_Equals query_indices tl1
  
let (snapshot_query_indices :
  unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun uu____8779  ->
    FStar_Common.snapshot push_query_indices query_indices ()
  
let (rollback_query_indices :
  Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth  -> FStar_Common.rollback pop_query_indices query_indices depth 
let (add_query_index :
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> unit) =
  fun uu____8809  ->
    match uu____8809 with
    | (l,n1) ->
        let uu____8816 = FStar_ST.op_Bang query_indices  in
        (match uu____8816 with
         | hd1::tl1 ->
             FStar_ST.op_Colon_Equals query_indices (((l, n1) :: hd1) :: tl1)
         | uu____8935 -> failwith "Empty query indices")
  
let (peek_query_indices :
  unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun uu____8954  ->
    let uu____8955 = FStar_ST.op_Bang query_indices  in
    FStar_List.hd uu____8955
  
let (stack : env Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (push_stack : env -> env) =
  fun env  ->
    (let uu____9032 =
       let uu____9035 = FStar_ST.op_Bang stack  in env :: uu____9035  in
     FStar_ST.op_Colon_Equals stack uu____9032);
    (let uu___118_9092 = env  in
     let uu____9093 = FStar_Util.smap_copy (gamma_cache env)  in
     let uu____9096 = FStar_Util.smap_copy (sigtab env)  in
     let uu____9099 =
       let uu____9112 =
         let uu____9115 =
           FStar_All.pipe_right env.qtbl_name_and_index
             FStar_Pervasives_Native.fst
            in
         FStar_Util.smap_copy uu____9115  in
       let uu____9140 =
         FStar_All.pipe_right env.qtbl_name_and_index
           FStar_Pervasives_Native.snd
          in
       (uu____9112, uu____9140)  in
     let uu____9181 = FStar_Util.smap_copy env.normalized_eff_names  in
     let uu____9184 =
       let uu____9187 = FStar_ST.op_Bang env.identifier_info  in
       FStar_Util.mk_ref uu____9187  in
     {
       solver = (uu___118_9092.solver);
       range = (uu___118_9092.range);
       curmodule = (uu___118_9092.curmodule);
       gamma = (uu___118_9092.gamma);
       gamma_cache = uu____9093;
       modules = (uu___118_9092.modules);
       expected_typ = (uu___118_9092.expected_typ);
       sigtab = uu____9096;
       is_pattern = (uu___118_9092.is_pattern);
       instantiate_imp = (uu___118_9092.instantiate_imp);
       effects = (uu___118_9092.effects);
       generalize = (uu___118_9092.generalize);
       letrecs = (uu___118_9092.letrecs);
       top_level = (uu___118_9092.top_level);
       check_uvars = (uu___118_9092.check_uvars);
       use_eq = (uu___118_9092.use_eq);
       is_iface = (uu___118_9092.is_iface);
       admit = (uu___118_9092.admit);
       lax = (uu___118_9092.lax);
       lax_universes = (uu___118_9092.lax_universes);
       failhard = (uu___118_9092.failhard);
       nosynth = (uu___118_9092.nosynth);
       tc_term = (uu___118_9092.tc_term);
       type_of = (uu___118_9092.type_of);
       universe_of = (uu___118_9092.universe_of);
       check_type_of = (uu___118_9092.check_type_of);
       use_bv_sorts = (uu___118_9092.use_bv_sorts);
       qtbl_name_and_index = uu____9099;
       normalized_eff_names = uu____9181;
       proof_ns = (uu___118_9092.proof_ns);
       synth_hook = (uu___118_9092.synth_hook);
       splice = (uu___118_9092.splice);
       is_native_tactic = (uu___118_9092.is_native_tactic);
       identifier_info = uu____9184;
       tc_hooks = (uu___118_9092.tc_hooks);
       dsenv = (uu___118_9092.dsenv);
       dep_graph = (uu___118_9092.dep_graph)
     })
  
let (pop_stack : unit -> env) =
  fun uu____9237  ->
    let uu____9238 = FStar_ST.op_Bang stack  in
    match uu____9238 with
    | env::tl1 -> (FStar_ST.op_Colon_Equals stack tl1; env)
    | uu____9300 -> failwith "Impossible: Too many pops"
  
let (snapshot_stack : env -> (Prims.int,env) FStar_Pervasives_Native.tuple2)
  = fun env  -> FStar_Common.snapshot push_stack stack env 
let (rollback_stack : Prims.int FStar_Pervasives_Native.option -> env) =
  fun depth  -> FStar_Common.rollback pop_stack stack depth 
type tcenv_depth_t =
  (Prims.int,Prims.int,solver_depth_t,Prims.int)
    FStar_Pervasives_Native.tuple4[@@deriving show]
let (snapshot :
  env -> Prims.string -> (tcenv_depth_t,env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun msg  ->
      FStar_Util.atomically
        (fun uu____9372  ->
           let uu____9373 = snapshot_stack env  in
           match uu____9373 with
           | (stack_depth,env1) ->
               let uu____9398 = snapshot_query_indices ()  in
               (match uu____9398 with
                | (query_indices_depth,()) ->
                    let uu____9422 = (env1.solver).snapshot msg  in
                    (match uu____9422 with
                     | (solver_depth,()) ->
                         let uu____9464 =
                           FStar_Syntax_DsEnv.snapshot env1.dsenv  in
                         (match uu____9464 with
                          | (dsenv_depth,dsenv1) ->
                              ((stack_depth, query_indices_depth,
                                 solver_depth, dsenv_depth),
                                (let uu___119_9510 = env1  in
                                 {
                                   solver = (uu___119_9510.solver);
                                   range = (uu___119_9510.range);
                                   curmodule = (uu___119_9510.curmodule);
                                   gamma = (uu___119_9510.gamma);
                                   gamma_cache = (uu___119_9510.gamma_cache);
                                   modules = (uu___119_9510.modules);
                                   expected_typ =
                                     (uu___119_9510.expected_typ);
                                   sigtab = (uu___119_9510.sigtab);
                                   is_pattern = (uu___119_9510.is_pattern);
                                   instantiate_imp =
                                     (uu___119_9510.instantiate_imp);
                                   effects = (uu___119_9510.effects);
                                   generalize = (uu___119_9510.generalize);
                                   letrecs = (uu___119_9510.letrecs);
                                   top_level = (uu___119_9510.top_level);
                                   check_uvars = (uu___119_9510.check_uvars);
                                   use_eq = (uu___119_9510.use_eq);
                                   is_iface = (uu___119_9510.is_iface);
                                   admit = (uu___119_9510.admit);
                                   lax = (uu___119_9510.lax);
                                   lax_universes =
                                     (uu___119_9510.lax_universes);
                                   failhard = (uu___119_9510.failhard);
                                   nosynth = (uu___119_9510.nosynth);
                                   tc_term = (uu___119_9510.tc_term);
                                   type_of = (uu___119_9510.type_of);
                                   universe_of = (uu___119_9510.universe_of);
                                   check_type_of =
                                     (uu___119_9510.check_type_of);
                                   use_bv_sorts =
                                     (uu___119_9510.use_bv_sorts);
                                   qtbl_name_and_index =
                                     (uu___119_9510.qtbl_name_and_index);
                                   normalized_eff_names =
                                     (uu___119_9510.normalized_eff_names);
                                   proof_ns = (uu___119_9510.proof_ns);
                                   synth_hook = (uu___119_9510.synth_hook);
                                   splice = (uu___119_9510.splice);
                                   is_native_tactic =
                                     (uu___119_9510.is_native_tactic);
                                   identifier_info =
                                     (uu___119_9510.identifier_info);
                                   tc_hooks = (uu___119_9510.tc_hooks);
                                   dsenv = dsenv1;
                                   dep_graph = (uu___119_9510.dep_graph)
                                 }))))))
  
let (rollback :
  solver_t ->
    Prims.string -> tcenv_depth_t FStar_Pervasives_Native.option -> env)
  =
  fun solver  ->
    fun msg  ->
      fun depth  ->
        FStar_Util.atomically
          (fun uu____9541  ->
             let uu____9542 =
               match depth with
               | FStar_Pervasives_Native.Some (s1,s2,s3,s4) ->
                   ((FStar_Pervasives_Native.Some s1),
                     (FStar_Pervasives_Native.Some s2),
                     (FStar_Pervasives_Native.Some s3),
                     (FStar_Pervasives_Native.Some s4))
               | FStar_Pervasives_Native.None  ->
                   (FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None,
                     FStar_Pervasives_Native.None)
                in
             match uu____9542 with
             | (stack_depth,query_indices_depth,solver_depth,dsenv_depth) ->
                 (solver.rollback msg solver_depth;
                  (match () with
                   | () ->
                       (rollback_query_indices query_indices_depth;
                        (match () with
                         | () ->
                             let tcenv = rollback_stack stack_depth  in
                             let dsenv1 =
                               FStar_Syntax_DsEnv.rollback dsenv_depth  in
                             ((let uu____9628 =
                                 FStar_Util.physical_equality tcenv.dsenv
                                   dsenv1
                                  in
                               FStar_Common.runtime_assert uu____9628
                                 "Inconsistent stack state");
                              tcenv))))))
  
let (push : env -> Prims.string -> env) =
  fun env  ->
    fun msg  ->
      let uu____9639 = snapshot env msg  in
      FStar_Pervasives_Native.snd uu____9639
  
let (pop : env -> Prims.string -> env) =
  fun env  ->
    fun msg  -> rollback env.solver msg FStar_Pervasives_Native.None
  
let (incr_query_index : env -> env) =
  fun env  ->
    let qix = peek_query_indices ()  in
    match env.qtbl_name_and_index with
    | (uu____9666,FStar_Pervasives_Native.None ) -> env
    | (tbl,FStar_Pervasives_Native.Some (l,n1)) ->
        let uu____9698 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____9724  ->
                  match uu____9724 with
                  | (m,uu____9730) -> FStar_Ident.lid_equals l m))
           in
        (match uu____9698 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___120_9738 = env  in
               {
                 solver = (uu___120_9738.solver);
                 range = (uu___120_9738.range);
                 curmodule = (uu___120_9738.curmodule);
                 gamma = (uu___120_9738.gamma);
                 gamma_cache = (uu___120_9738.gamma_cache);
                 modules = (uu___120_9738.modules);
                 expected_typ = (uu___120_9738.expected_typ);
                 sigtab = (uu___120_9738.sigtab);
                 is_pattern = (uu___120_9738.is_pattern);
                 instantiate_imp = (uu___120_9738.instantiate_imp);
                 effects = (uu___120_9738.effects);
                 generalize = (uu___120_9738.generalize);
                 letrecs = (uu___120_9738.letrecs);
                 top_level = (uu___120_9738.top_level);
                 check_uvars = (uu___120_9738.check_uvars);
                 use_eq = (uu___120_9738.use_eq);
                 is_iface = (uu___120_9738.is_iface);
                 admit = (uu___120_9738.admit);
                 lax = (uu___120_9738.lax);
                 lax_universes = (uu___120_9738.lax_universes);
                 failhard = (uu___120_9738.failhard);
                 nosynth = (uu___120_9738.nosynth);
                 tc_term = (uu___120_9738.tc_term);
                 type_of = (uu___120_9738.type_of);
                 universe_of = (uu___120_9738.universe_of);
                 check_type_of = (uu___120_9738.check_type_of);
                 use_bv_sorts = (uu___120_9738.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___120_9738.normalized_eff_names);
                 proof_ns = (uu___120_9738.proof_ns);
                 synth_hook = (uu___120_9738.synth_hook);
                 splice = (uu___120_9738.splice);
                 is_native_tactic = (uu___120_9738.is_native_tactic);
                 identifier_info = (uu___120_9738.identifier_info);
                 tc_hooks = (uu___120_9738.tc_hooks);
                 dsenv = (uu___120_9738.dsenv);
                 dep_graph = (uu___120_9738.dep_graph)
               }))
         | FStar_Pervasives_Native.Some (uu____9751,m) ->
             let next = m + (Prims.parse_int "1")  in
             (add_query_index (l, next);
              FStar_Util.smap_add tbl l.FStar_Ident.str next;
              (let uu___121_9760 = env  in
               {
                 solver = (uu___121_9760.solver);
                 range = (uu___121_9760.range);
                 curmodule = (uu___121_9760.curmodule);
                 gamma = (uu___121_9760.gamma);
                 gamma_cache = (uu___121_9760.gamma_cache);
                 modules = (uu___121_9760.modules);
                 expected_typ = (uu___121_9760.expected_typ);
                 sigtab = (uu___121_9760.sigtab);
                 is_pattern = (uu___121_9760.is_pattern);
                 instantiate_imp = (uu___121_9760.instantiate_imp);
                 effects = (uu___121_9760.effects);
                 generalize = (uu___121_9760.generalize);
                 letrecs = (uu___121_9760.letrecs);
                 top_level = (uu___121_9760.top_level);
                 check_uvars = (uu___121_9760.check_uvars);
                 use_eq = (uu___121_9760.use_eq);
                 is_iface = (uu___121_9760.is_iface);
                 admit = (uu___121_9760.admit);
                 lax = (uu___121_9760.lax);
                 lax_universes = (uu___121_9760.lax_universes);
                 failhard = (uu___121_9760.failhard);
                 nosynth = (uu___121_9760.nosynth);
                 tc_term = (uu___121_9760.tc_term);
                 type_of = (uu___121_9760.type_of);
                 universe_of = (uu___121_9760.universe_of);
                 check_type_of = (uu___121_9760.check_type_of);
                 use_bv_sorts = (uu___121_9760.use_bv_sorts);
                 qtbl_name_and_index =
                   (tbl, (FStar_Pervasives_Native.Some (l, next)));
                 normalized_eff_names = (uu___121_9760.normalized_eff_names);
                 proof_ns = (uu___121_9760.proof_ns);
                 synth_hook = (uu___121_9760.synth_hook);
                 splice = (uu___121_9760.splice);
                 is_native_tactic = (uu___121_9760.is_native_tactic);
                 identifier_info = (uu___121_9760.identifier_info);
                 tc_hooks = (uu___121_9760.tc_hooks);
                 dsenv = (uu___121_9760.dsenv);
                 dep_graph = (uu___121_9760.dep_graph)
               })))
  
let (debug : env -> FStar_Options.debug_level_t -> Prims.bool) =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
  
let (set_range : env -> FStar_Range.range -> env) =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___122_9794 = e  in
         {
           solver = (uu___122_9794.solver);
           range = r;
           curmodule = (uu___122_9794.curmodule);
           gamma = (uu___122_9794.gamma);
           gamma_cache = (uu___122_9794.gamma_cache);
           modules = (uu___122_9794.modules);
           expected_typ = (uu___122_9794.expected_typ);
           sigtab = (uu___122_9794.sigtab);
           is_pattern = (uu___122_9794.is_pattern);
           instantiate_imp = (uu___122_9794.instantiate_imp);
           effects = (uu___122_9794.effects);
           generalize = (uu___122_9794.generalize);
           letrecs = (uu___122_9794.letrecs);
           top_level = (uu___122_9794.top_level);
           check_uvars = (uu___122_9794.check_uvars);
           use_eq = (uu___122_9794.use_eq);
           is_iface = (uu___122_9794.is_iface);
           admit = (uu___122_9794.admit);
           lax = (uu___122_9794.lax);
           lax_universes = (uu___122_9794.lax_universes);
           failhard = (uu___122_9794.failhard);
           nosynth = (uu___122_9794.nosynth);
           tc_term = (uu___122_9794.tc_term);
           type_of = (uu___122_9794.type_of);
           universe_of = (uu___122_9794.universe_of);
           check_type_of = (uu___122_9794.check_type_of);
           use_bv_sorts = (uu___122_9794.use_bv_sorts);
           qtbl_name_and_index = (uu___122_9794.qtbl_name_and_index);
           normalized_eff_names = (uu___122_9794.normalized_eff_names);
           proof_ns = (uu___122_9794.proof_ns);
           synth_hook = (uu___122_9794.synth_hook);
           splice = (uu___122_9794.splice);
           is_native_tactic = (uu___122_9794.is_native_tactic);
           identifier_info = (uu___122_9794.identifier_info);
           tc_hooks = (uu___122_9794.tc_hooks);
           dsenv = (uu___122_9794.dsenv);
           dep_graph = (uu___122_9794.dep_graph)
         })
  
let (get_range : env -> FStar_Range.range) = fun e  -> e.range 
let (toggle_id_info : env -> Prims.bool -> unit) =
  fun env  ->
    fun enabled  ->
      let uu____9810 =
        let uu____9811 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_toggle uu____9811 enabled  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9810
  
let (insert_bv_info :
  env -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun bv  ->
      fun ty  ->
        let uu____9873 =
          let uu____9874 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_bv uu____9874 bv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9873
  
let (insert_fv_info :
  env -> FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.typ -> unit) =
  fun env  ->
    fun fv  ->
      fun ty  ->
        let uu____9936 =
          let uu____9937 = FStar_ST.op_Bang env.identifier_info  in
          FStar_TypeChecker_Common.id_info_insert_fv uu____9937 fv ty  in
        FStar_ST.op_Colon_Equals env.identifier_info uu____9936
  
let (promote_id_info :
  env -> (FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) -> unit) =
  fun env  ->
    fun ty_map  ->
      let uu____9999 =
        let uu____10000 = FStar_ST.op_Bang env.identifier_info  in
        FStar_TypeChecker_Common.id_info_promote uu____10000 ty_map  in
      FStar_ST.op_Colon_Equals env.identifier_info uu____9999
  
let (modules : env -> FStar_Syntax_Syntax.modul Prims.list) =
  fun env  -> env.modules 
let (current_module : env -> FStar_Ident.lident) = fun env  -> env.curmodule 
let (set_current_module : env -> FStar_Ident.lident -> env) =
  fun env  ->
    fun lid  ->
      let uu___123_10069 = env  in
      {
        solver = (uu___123_10069.solver);
        range = (uu___123_10069.range);
        curmodule = lid;
        gamma = (uu___123_10069.gamma);
        gamma_cache = (uu___123_10069.gamma_cache);
        modules = (uu___123_10069.modules);
        expected_typ = (uu___123_10069.expected_typ);
        sigtab = (uu___123_10069.sigtab);
        is_pattern = (uu___123_10069.is_pattern);
        instantiate_imp = (uu___123_10069.instantiate_imp);
        effects = (uu___123_10069.effects);
        generalize = (uu___123_10069.generalize);
        letrecs = (uu___123_10069.letrecs);
        top_level = (uu___123_10069.top_level);
        check_uvars = (uu___123_10069.check_uvars);
        use_eq = (uu___123_10069.use_eq);
        is_iface = (uu___123_10069.is_iface);
        admit = (uu___123_10069.admit);
        lax = (uu___123_10069.lax);
        lax_universes = (uu___123_10069.lax_universes);
        failhard = (uu___123_10069.failhard);
        nosynth = (uu___123_10069.nosynth);
        tc_term = (uu___123_10069.tc_term);
        type_of = (uu___123_10069.type_of);
        universe_of = (uu___123_10069.universe_of);
        check_type_of = (uu___123_10069.check_type_of);
        use_bv_sorts = (uu___123_10069.use_bv_sorts);
        qtbl_name_and_index = (uu___123_10069.qtbl_name_and_index);
        normalized_eff_names = (uu___123_10069.normalized_eff_names);
        proof_ns = (uu___123_10069.proof_ns);
        synth_hook = (uu___123_10069.synth_hook);
        splice = (uu___123_10069.splice);
        is_native_tactic = (uu___123_10069.is_native_tactic);
        identifier_info = (uu___123_10069.identifier_info);
        tc_hooks = (uu___123_10069.tc_hooks);
        dsenv = (uu___123_10069.dsenv);
        dep_graph = (uu___123_10069.dep_graph)
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
      let uu____10096 = FStar_Ident.text_of_lid lid  in
      FStar_Util.smap_try_find (sigtab env) uu____10096
  
let (name_not_found :
  FStar_Ident.lid ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____10106 =
      FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str  in
    (FStar_Errors.Fatal_NameNotFound, uu____10106)
  
let (variable_not_found :
  FStar_Syntax_Syntax.bv ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun v1  ->
    let uu____10116 =
      let uu____10117 = FStar_Syntax_Print.bv_to_string v1  in
      FStar_Util.format1 "Variable \"%s\" not found" uu____10117  in
    (FStar_Errors.Fatal_VariableNotFound, uu____10116)
  
let (new_u_univ : unit -> FStar_Syntax_Syntax.universe) =
  fun uu____10122  ->
    let uu____10123 = FStar_Syntax_Unionfind.univ_fresh ()  in
    FStar_Syntax_Syntax.U_unif uu____10123
  
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
      | ((formals,t),uu____10165) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1")  in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u)))
             in
          let uu____10187 = FStar_Syntax_Subst.subst vs t  in
          (us, uu____10187)
  
let (inst_tscheme :
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___100_10203  ->
    match uu___100_10203 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____10227  -> new_u_univ ()))
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
      let uu____10244 = inst_tscheme t  in
      match uu____10244 with
      | (us,t1) ->
          let uu____10255 = FStar_Syntax_Subst.set_use_range r t1  in
          (us, uu____10255)
  
let (inst_effect_fun_with :
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term)
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____10275  ->
          match uu____10275 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us  in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____10290 =
                         let uu____10291 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1)
                            in
                         let uu____10292 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts)
                            in
                         let uu____10293 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname
                            in
                         let uu____10294 =
                           FStar_Syntax_Print.term_to_string t  in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____10291 uu____10292 uu____10293 uu____10294
                          in
                       failwith uu____10290)
                    else ();
                    (let uu____10296 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts
                        in
                     FStar_Pervasives_Native.snd uu____10296))
               | uu____10303 ->
                   let uu____10304 =
                     let uu____10305 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname
                        in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____10305
                      in
                   failwith uu____10304)
  
type tri =
  | Yes 
  | No 
  | Maybe [@@deriving show]
let (uu___is_Yes : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Yes  -> true | uu____10311 -> false
  
let (uu___is_No : tri -> Prims.bool) =
  fun projectee  -> match projectee with | No  -> true | uu____10317 -> false 
let (uu___is_Maybe : tri -> Prims.bool) =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____10323 -> false
  
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
             | ([],uu____10365) -> Maybe
             | (uu____10372,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____10391 -> No  in
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
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t  in
      let found =
        if cur_mod <> No
        then
          let uu____10482 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str
             in
          match uu____10482 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___101_10528  ->
                   match uu___101_10528 with
                   | Binding_lid (l,t) ->
                       let uu____10551 = FStar_Ident.lid_equals lid l  in
                       if uu____10551
                       then
                         let uu____10572 =
                           let uu____10591 =
                             let uu____10606 = inst_tscheme t  in
                             FStar_Util.Inl uu____10606  in
                           let uu____10621 = FStar_Ident.range_of_lid l  in
                           (uu____10591, uu____10621)  in
                         FStar_Pervasives_Native.Some uu____10572
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____10673,{
                                      FStar_Syntax_Syntax.sigel =
                                        FStar_Syntax_Syntax.Sig_bundle
                                        (ses,uu____10675);
                                      FStar_Syntax_Syntax.sigrng =
                                        uu____10676;
                                      FStar_Syntax_Syntax.sigquals =
                                        uu____10677;
                                      FStar_Syntax_Syntax.sigmeta =
                                        uu____10678;
                                      FStar_Syntax_Syntax.sigattrs =
                                        uu____10679;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____10699 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid))
                               in
                            if uu____10699
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____10747 ->
                             FStar_Pervasives_Native.Some t
                         | uu____10754 -> cache t  in
                       let uu____10755 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____10755 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____10797 =
                              let uu____10798 = FStar_Ident.range_of_lid l
                                 in
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                uu____10798)
                               in
                            maybe_cache uu____10797)
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____10832 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids
                          in
                       (match uu____10832 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            let uu____10874 =
                              let uu____10893 = FStar_Ident.range_of_lid l
                                 in
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                uu____10893)
                               in
                            FStar_Pervasives_Native.Some uu____10874)
                   | uu____10938 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None  in
      if FStar_Util.is_some found
      then found
      else
        (let uu____10998 = find_in_sigtab env lid  in
         match uu____10998 with
         | FStar_Pervasives_Native.Some se ->
             FStar_Pervasives_Native.Some
               ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                 (FStar_Syntax_Util.range_of_sigelt se))
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
  
let rec (add_sigelt : env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____11085) ->
          add_sigelts env ses
      | uu____11094 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se  in
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
                            ne.FStar_Syntax_Syntax.mname a
                            (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                           in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____11108 -> ()))

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
        (fun uu___102_11139  ->
           match uu___102_11139 with
           | Binding_var id1 when FStar_Syntax_Syntax.bv_eq id1 bv ->
               FStar_Pervasives_Native.Some
                 ((id1.FStar_Syntax_Syntax.sort),
                   ((id1.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____11157 -> FStar_Pervasives_Native.None)
  
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
        | FStar_Syntax_Syntax.Sig_let ((uu____11218,lb::[]),uu____11220) ->
            let uu____11233 =
              let uu____11242 =
                inst_tscheme1
                  ((lb.FStar_Syntax_Syntax.lbunivs),
                    (lb.FStar_Syntax_Syntax.lbtyp))
                 in
              let uu____11251 =
                FStar_Syntax_Syntax.range_of_lbname
                  lb.FStar_Syntax_Syntax.lbname
                 in
              (uu____11242, uu____11251)  in
            FStar_Pervasives_Native.Some uu____11233
        | FStar_Syntax_Syntax.Sig_let ((uu____11264,lbs),uu____11266) ->
            FStar_Util.find_map lbs
              (fun lb  ->
                 match lb.FStar_Syntax_Syntax.lbname with
                 | FStar_Util.Inl uu____11302 -> failwith "impossible"
                 | FStar_Util.Inr fv ->
                     let uu____11314 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                        in
                     if uu____11314
                     then
                       let uu____11325 =
                         let uu____11334 =
                           inst_tscheme1
                             ((lb.FStar_Syntax_Syntax.lbunivs),
                               (lb.FStar_Syntax_Syntax.lbtyp))
                            in
                         let uu____11343 = FStar_Syntax_Syntax.range_of_fv fv
                            in
                         (uu____11334, uu____11343)  in
                       FStar_Pervasives_Native.Some uu____11325
                     else FStar_Pervasives_Native.None)
        | uu____11365 -> FStar_Pervasives_Native.None
  
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
          let uu____11424 =
            let uu____11433 =
              let uu____11438 =
                let uu____11439 =
                  let uu____11442 =
                    FStar_Syntax_Syntax.mk_Total
                      ne.FStar_Syntax_Syntax.signature
                     in
                  FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                    uu____11442
                   in
                ((ne.FStar_Syntax_Syntax.univs), uu____11439)  in
              inst_tscheme1 uu____11438  in
            (uu____11433, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11424
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,us,binders,uu____11462,uu____11463) ->
          let uu____11468 =
            let uu____11477 =
              let uu____11482 =
                let uu____11483 =
                  let uu____11486 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff  in
                  FStar_Syntax_Util.arrow binders uu____11486  in
                (us, uu____11483)  in
              inst_tscheme1 uu____11482  in
            (uu____11477, (se.FStar_Syntax_Syntax.sigrng))  in
          FStar_Pervasives_Native.Some uu____11468
      | uu____11503 -> FStar_Pervasives_Native.None
  
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
        let mapper uu____11591 =
          match uu____11591 with
          | (lr,rng) ->
              (match lr with
               | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_datacon
                        (uu____11687,uvs,t,uu____11690,uu____11691,uu____11692);
                      FStar_Syntax_Syntax.sigrng = uu____11693;
                      FStar_Syntax_Syntax.sigquals = uu____11694;
                      FStar_Syntax_Syntax.sigmeta = uu____11695;
                      FStar_Syntax_Syntax.sigattrs = uu____11696;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11717 =
                     let uu____11726 = inst_tscheme1 (uvs, t)  in
                     (uu____11726, rng)  in
                   FStar_Pervasives_Native.Some uu____11717
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                      FStar_Syntax_Syntax.sigrng = uu____11746;
                      FStar_Syntax_Syntax.sigquals = qs;
                      FStar_Syntax_Syntax.sigmeta = uu____11748;
                      FStar_Syntax_Syntax.sigattrs = uu____11749;_},FStar_Pervasives_Native.None
                    )
                   ->
                   let uu____11766 =
                     let uu____11767 = in_cur_mod env l  in uu____11767 = Yes
                      in
                   if uu____11766
                   then
                     let uu____11778 =
                       (FStar_All.pipe_right qs
                          (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                         || env.is_iface
                        in
                     (if uu____11778
                      then
                        let uu____11791 =
                          let uu____11800 = inst_tscheme1 (uvs, t)  in
                          (uu____11800, rng)  in
                        FStar_Pervasives_Native.Some uu____11791
                      else FStar_Pervasives_Native.None)
                   else
                     (let uu____11827 =
                        let uu____11836 = inst_tscheme1 (uvs, t)  in
                        (uu____11836, rng)  in
                      FStar_Pervasives_Native.Some uu____11827)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11857,uu____11858);
                      FStar_Syntax_Syntax.sigrng = uu____11859;
                      FStar_Syntax_Syntax.sigquals = uu____11860;
                      FStar_Syntax_Syntax.sigmeta = uu____11861;
                      FStar_Syntax_Syntax.sigattrs = uu____11862;_},FStar_Pervasives_Native.None
                    )
                   ->
                   (match tps with
                    | [] ->
                        let uu____11901 =
                          let uu____11910 = inst_tscheme1 (uvs, k)  in
                          (uu____11910, rng)  in
                        FStar_Pervasives_Native.Some uu____11901
                    | uu____11927 ->
                        let uu____11928 =
                          let uu____11937 =
                            let uu____11942 =
                              let uu____11943 =
                                let uu____11946 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____11946
                                 in
                              (uvs, uu____11943)  in
                            inst_tscheme1 uu____11942  in
                          (uu____11937, rng)  in
                        FStar_Pervasives_Native.Some uu____11928)
               | FStar_Util.Inr
                   ({
                      FStar_Syntax_Syntax.sigel =
                        FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid1,uvs,tps,k,uu____11967,uu____11968);
                      FStar_Syntax_Syntax.sigrng = uu____11969;
                      FStar_Syntax_Syntax.sigquals = uu____11970;
                      FStar_Syntax_Syntax.sigmeta = uu____11971;
                      FStar_Syntax_Syntax.sigattrs = uu____11972;_},FStar_Pervasives_Native.Some
                    us)
                   ->
                   (match tps with
                    | [] ->
                        let uu____12012 =
                          let uu____12021 = inst_tscheme_with (uvs, k) us  in
                          (uu____12021, rng)  in
                        FStar_Pervasives_Native.Some uu____12012
                    | uu____12038 ->
                        let uu____12039 =
                          let uu____12048 =
                            let uu____12053 =
                              let uu____12054 =
                                let uu____12057 =
                                  FStar_Syntax_Syntax.mk_Total k  in
                                FStar_Syntax_Util.flat_arrow tps uu____12057
                                 in
                              (uvs, uu____12054)  in
                            inst_tscheme_with uu____12053 us  in
                          (uu____12048, rng)  in
                        FStar_Pervasives_Native.Some uu____12039)
               | FStar_Util.Inr se ->
                   let uu____12091 =
                     match se with
                     | ({
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_let uu____12112;
                          FStar_Syntax_Syntax.sigrng = uu____12113;
                          FStar_Syntax_Syntax.sigquals = uu____12114;
                          FStar_Syntax_Syntax.sigmeta = uu____12115;
                          FStar_Syntax_Syntax.sigattrs = uu____12116;_},FStar_Pervasives_Native.None
                        ) ->
                         lookup_type_of_let us_opt
                           (FStar_Pervasives_Native.fst se) lid
                     | uu____12131 ->
                         effect_signature us_opt
                           (FStar_Pervasives_Native.fst se)
                      in
                   FStar_All.pipe_right uu____12091
                     (FStar_Util.map_option
                        (fun uu____12179  ->
                           match uu____12179 with
                           | (us_t,rng1) -> (us_t, rng1))))
           in
        let uu____12210 =
          let uu____12221 = lookup_qname env lid  in
          FStar_Util.bind_opt uu____12221 mapper  in
        match uu____12210 with
        | FStar_Pervasives_Native.Some ((us,t),r) ->
            let uu____12295 =
              let uu____12306 =
                let uu____12313 =
                  let uu___124_12316 = t  in
                  let uu____12317 = FStar_Ident.range_of_lid lid  in
                  {
                    FStar_Syntax_Syntax.n =
                      (uu___124_12316.FStar_Syntax_Syntax.n);
                    FStar_Syntax_Syntax.pos = uu____12317;
                    FStar_Syntax_Syntax.vars =
                      (uu___124_12316.FStar_Syntax_Syntax.vars)
                  }  in
                (us, uu____12313)  in
              (uu____12306, r)  in
            FStar_Pervasives_Native.Some uu____12295
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lid_exists : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____12364 = lookup_qname env l  in
      match uu____12364 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____12383 -> true
  
let (lookup_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv  in
      let uu____12435 = try_lookup_bv env bv  in
      match uu____12435 with
      | FStar_Pervasives_Native.None  ->
          let uu____12450 = variable_not_found bv  in
          FStar_Errors.raise_error uu____12450 bvr
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____12465 = FStar_Syntax_Subst.set_use_range bvr t  in
          let uu____12466 =
            let uu____12467 = FStar_Range.use_range bvr  in
            FStar_Range.set_use_range r uu____12467  in
          (uu____12465, uu____12466)
  
let (try_lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____12488 = try_lookup_lid_aux FStar_Pervasives_Native.None env l
         in
      match uu____12488 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range1 = FStar_Ident.range_of_lid l  in
          let r1 =
            let uu____12554 = FStar_Range.use_range use_range1  in
            FStar_Range.set_use_range r uu____12554  in
          let uu____12555 =
            let uu____12564 =
              let uu____12569 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (us, uu____12569)  in
            (uu____12564, r1)  in
          FStar_Pervasives_Native.Some uu____12555
  
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
        let uu____12603 =
          try_lookup_lid_aux (FStar_Pervasives_Native.Some us) env l  in
        match uu____12603 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some ((uu____12636,t),r) ->
            let use_range1 = FStar_Ident.range_of_lid l  in
            let r1 =
              let uu____12661 = FStar_Range.use_range use_range1  in
              FStar_Range.set_use_range r uu____12661  in
            let uu____12662 =
              let uu____12667 = FStar_Syntax_Subst.set_use_range use_range1 t
                 in
              (uu____12667, r1)  in
            FStar_Pervasives_Native.Some uu____12662
  
let (lookup_lid :
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun l  ->
      let uu____12690 = try_lookup_lid env l  in
      match uu____12690 with
      | FStar_Pervasives_Native.None  ->
          let uu____12717 = name_not_found l  in
          let uu____12722 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____12717 uu____12722
      | FStar_Pervasives_Native.Some v1 -> v1
  
let (lookup_univ : env -> FStar_Syntax_Syntax.univ_name -> Prims.bool) =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___103_12762  ->
              match uu___103_12762 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____12764 -> false) env.gamma) FStar_Option.isSome
  
let (try_lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____12783 = lookup_qname env lid  in
      match uu____12783 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12792,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12795;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____12797;
              FStar_Syntax_Syntax.sigattrs = uu____12798;_},FStar_Pervasives_Native.None
            ),uu____12799)
          ->
          let uu____12848 =
            let uu____12859 =
              let uu____12864 =
                let uu____12865 = FStar_Ident.range_of_lid lid  in
                FStar_Syntax_Subst.set_use_range uu____12865 t  in
              (uvs, uu____12864)  in
            (uu____12859, q)  in
          FStar_Pervasives_Native.Some uu____12848
      | uu____12882 -> FStar_Pervasives_Native.None
  
let (lookup_val_decl :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12903 = lookup_qname env lid  in
      match uu____12903 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____12908,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____12911;
              FStar_Syntax_Syntax.sigquals = uu____12912;
              FStar_Syntax_Syntax.sigmeta = uu____12913;
              FStar_Syntax_Syntax.sigattrs = uu____12914;_},FStar_Pervasives_Native.None
            ),uu____12915)
          ->
          let uu____12964 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____12964 (uvs, t)
      | uu____12965 ->
          let uu____12966 = name_not_found lid  in
          let uu____12971 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____12966 uu____12971
  
let (lookup_datacon :
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____12990 = lookup_qname env lid  in
      match uu____12990 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____12995,uvs,t,uu____12998,uu____12999,uu____13000);
              FStar_Syntax_Syntax.sigrng = uu____13001;
              FStar_Syntax_Syntax.sigquals = uu____13002;
              FStar_Syntax_Syntax.sigmeta = uu____13003;
              FStar_Syntax_Syntax.sigattrs = uu____13004;_},FStar_Pervasives_Native.None
            ),uu____13005)
          ->
          let uu____13058 = FStar_Ident.range_of_lid lid  in
          inst_tscheme_with_range uu____13058 (uvs, t)
      | uu____13059 ->
          let uu____13060 = name_not_found lid  in
          let uu____13065 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____13060 uu____13065
  
let (datacons_of_typ :
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lid  ->
      let uu____13086 = lookup_qname env lid  in
      match uu____13086 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____13093,uu____13094,uu____13095,uu____13096,uu____13097,dcs);
              FStar_Syntax_Syntax.sigrng = uu____13099;
              FStar_Syntax_Syntax.sigquals = uu____13100;
              FStar_Syntax_Syntax.sigmeta = uu____13101;
              FStar_Syntax_Syntax.sigattrs = uu____13102;_},uu____13103),uu____13104)
          -> (true, dcs)
      | uu____13165 -> (false, [])
  
let (typ_of_datacon : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      let uu____13178 = lookup_qname env lid  in
      match uu____13178 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____13179,uu____13180,uu____13181,l,uu____13183,uu____13184);
              FStar_Syntax_Syntax.sigrng = uu____13185;
              FStar_Syntax_Syntax.sigquals = uu____13186;
              FStar_Syntax_Syntax.sigmeta = uu____13187;
              FStar_Syntax_Syntax.sigattrs = uu____13188;_},uu____13189),uu____13190)
          -> l
      | uu____13245 ->
          let uu____13246 =
            let uu____13247 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format1 "Not a datacon: %s" uu____13247  in
          failwith uu____13246
  
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
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13296)
            ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let ((uu____13347,lbs),uu____13349)
                 when visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                         in
                      let uu____13377 = FStar_Syntax_Syntax.fv_eq_lid fv lid
                         in
                      if uu____13377
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____13409 -> FStar_Pervasives_Native.None)
        | uu____13414 -> FStar_Pervasives_Native.None
  
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
        let uu____13444 = lookup_qname env lid  in
        FStar_All.pipe_left (lookup_definition_qninfo delta_levels lid)
          uu____13444
  
let (attrs_of_qninfo :
  qninfo ->
    FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr (se,uu____13469),uu____13470) ->
        FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigattrs)
    | uu____13519 -> FStar_Pervasives_Native.None
  
let (lookup_attrs_of_lid :
  env ->
    FStar_Ident.lid ->
      FStar_Syntax_Syntax.attribute Prims.list FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____13540 = lookup_qname env lid  in
      FStar_All.pipe_left attrs_of_qninfo uu____13540
  
let (try_lookup_effect_lid :
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun ftv  ->
      let uu____13559 = lookup_qname env ftv  in
      match uu____13559 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____13563) ->
          let uu____13608 = effect_signature FStar_Pervasives_Native.None se
             in
          (match uu____13608 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____13629,t),r) ->
               let uu____13644 =
                 let uu____13645 = FStar_Ident.range_of_lid ftv  in
                 FStar_Syntax_Subst.set_use_range uu____13645 t  in
               FStar_Pervasives_Native.Some uu____13644)
      | uu____13646 -> FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun ftv  ->
      let uu____13657 = try_lookup_effect_lid env ftv  in
      match uu____13657 with
      | FStar_Pervasives_Native.None  ->
          let uu____13660 = name_not_found ftv  in
          let uu____13665 = FStar_Ident.range_of_lid ftv  in
          FStar_Errors.raise_error uu____13660 uu____13665
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
        let uu____13688 = lookup_qname env lid0  in
        match uu____13688 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____13699);
                FStar_Syntax_Syntax.sigrng = uu____13700;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____13702;
                FStar_Syntax_Syntax.sigattrs = uu____13703;_},FStar_Pervasives_Native.None
              ),uu____13704)
            ->
            let lid1 =
              let uu____13758 =
                let uu____13759 = FStar_Ident.range_of_lid lid  in
                let uu____13760 =
                  let uu____13761 = FStar_Ident.range_of_lid lid0  in
                  FStar_Range.use_range uu____13761  in
                FStar_Range.set_use_range uu____13759 uu____13760  in
              FStar_Ident.set_lid_range lid uu____13758  in
            let uu____13762 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___104_13766  ->
                      match uu___104_13766 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13767 -> false))
               in
            if uu____13762
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____13781 =
                      let uu____13782 =
                        let uu____13783 = get_range env  in
                        FStar_Range.string_of_range uu____13783  in
                      let uu____13784 = FStar_Syntax_Print.lid_to_string lid1
                         in
                      let uu____13785 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int
                         in
                      FStar_Util.format3
                        "(%s) Unexpected instantiation of effect %s with %s universes"
                        uu____13782 uu____13784 uu____13785
                       in
                    failwith uu____13781)
                  in
               match (binders, univs1) with
               | ([],uu____13792) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____13809,uu____13810::uu____13811::uu____13812) ->
                   let uu____13817 =
                     let uu____13818 = FStar_Syntax_Print.lid_to_string lid1
                        in
                     let uu____13819 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1)
                        in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____13818 uu____13819
                      in
                   failwith uu____13817
               | uu____13826 ->
                   let uu____13831 =
                     let uu____13836 =
                       let uu____13837 = FStar_Syntax_Util.arrow binders c
                          in
                       (univs1, uu____13837)  in
                     inst_tscheme_with uu____13836 insts  in
                   (match uu____13831 with
                    | (uu____13848,t) ->
                        let t1 =
                          let uu____13851 = FStar_Ident.range_of_lid lid1  in
                          FStar_Syntax_Subst.set_use_range uu____13851 t  in
                        let uu____13852 =
                          let uu____13853 = FStar_Syntax_Subst.compress t1
                             in
                          uu____13853.FStar_Syntax_Syntax.n  in
                        (match uu____13852 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____13900 -> failwith "Impossible")))
        | uu____13907 -> FStar_Pervasives_Native.None
  
let (norm_eff_name : env -> FStar_Ident.lident -> FStar_Ident.lident) =
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____13930 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1  in
        match uu____13930 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____13943,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c  in
            let uu____13950 = find1 l2  in
            (match uu____13950 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l')
         in
      let res =
        let uu____13957 =
          FStar_Util.smap_try_find env.normalized_eff_names l.FStar_Ident.str
           in
        match uu____13957 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____13961 = find1 l  in
            (match uu____13961 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add env.normalized_eff_names
                    l.FStar_Ident.str m;
                  m))
         in
      let uu____13966 = FStar_Ident.range_of_lid l  in
      FStar_Ident.set_lid_range res uu____13966
  
let (lookup_effect_quals :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l  in
      let uu____13980 = lookup_qname env l1  in
      match uu____13980 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____13983;
              FStar_Syntax_Syntax.sigrng = uu____13984;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____13986;
              FStar_Syntax_Syntax.sigattrs = uu____13987;_},uu____13988),uu____13989)
          -> q
      | uu____14040 -> []
  
let (lookup_projector :
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident) =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____14061 =
          let uu____14062 =
            let uu____14063 = FStar_Util.string_of_int i  in
            let uu____14064 = FStar_Syntax_Print.lid_to_string lid  in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____14063 uu____14064
             in
          failwith uu____14062  in
        let uu____14065 = lookup_datacon env lid  in
        match uu____14065 with
        | (uu____14070,t) ->
            let uu____14072 =
              let uu____14073 = FStar_Syntax_Subst.compress t  in
              uu____14073.FStar_Syntax_Syntax.n  in
            (match uu____14072 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____14077) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail1 ()
                 else
                   (let b = FStar_List.nth binders i  in
                    let uu____14108 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i
                       in
                    FStar_All.pipe_right uu____14108
                      FStar_Pervasives_Native.fst)
             | uu____14117 -> fail1 ())
  
let (is_projector : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14128 = lookup_qname env l  in
      match uu____14128 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____14129,uu____14130,uu____14131);
              FStar_Syntax_Syntax.sigrng = uu____14132;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14134;
              FStar_Syntax_Syntax.sigattrs = uu____14135;_},uu____14136),uu____14137)
          ->
          FStar_Util.for_some
            (fun uu___105_14190  ->
               match uu___105_14190 with
               | FStar_Syntax_Syntax.Projector uu____14191 -> true
               | uu____14196 -> false) quals
      | uu____14197 -> false
  
let (is_datacon : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14208 = lookup_qname env lid  in
      match uu____14208 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____14209,uu____14210,uu____14211,uu____14212,uu____14213,uu____14214);
              FStar_Syntax_Syntax.sigrng = uu____14215;
              FStar_Syntax_Syntax.sigquals = uu____14216;
              FStar_Syntax_Syntax.sigmeta = uu____14217;
              FStar_Syntax_Syntax.sigattrs = uu____14218;_},uu____14219),uu____14220)
          -> true
      | uu____14275 -> false
  
let (is_record : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14286 = lookup_qname env lid  in
      match uu____14286 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14287,uu____14288,uu____14289,uu____14290,uu____14291,uu____14292);
              FStar_Syntax_Syntax.sigrng = uu____14293;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____14295;
              FStar_Syntax_Syntax.sigattrs = uu____14296;_},uu____14297),uu____14298)
          ->
          FStar_Util.for_some
            (fun uu___106_14359  ->
               match uu___106_14359 with
               | FStar_Syntax_Syntax.RecordType uu____14360 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____14369 -> true
               | uu____14378 -> false) quals
      | uu____14379 -> false
  
let (qninfo_is_action : qninfo -> Prims.bool) =
  fun qninfo  ->
    match qninfo with
    | FStar_Pervasives_Native.Some
        (FStar_Util.Inr
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
              (uu____14385,uu____14386);
            FStar_Syntax_Syntax.sigrng = uu____14387;
            FStar_Syntax_Syntax.sigquals = quals;
            FStar_Syntax_Syntax.sigmeta = uu____14389;
            FStar_Syntax_Syntax.sigattrs = uu____14390;_},uu____14391),uu____14392)
        ->
        FStar_Util.for_some
          (fun uu___107_14449  ->
             match uu___107_14449 with
             | FStar_Syntax_Syntax.Action uu____14450 -> true
             | uu____14451 -> false) quals
    | uu____14452 -> false
  
let (is_action : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____14463 = lookup_qname env lid  in
      FStar_All.pipe_left qninfo_is_action uu____14463
  
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
      let uu____14477 =
        let uu____14478 = FStar_Syntax_Util.un_uinst head1  in
        uu____14478.FStar_Syntax_Syntax.n  in
      match uu____14477 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          (match fv.FStar_Syntax_Syntax.fv_delta with
           | FStar_Syntax_Syntax.Delta_equational_at_level uu____14482 ->
               true
           | uu____14483 -> false)
      | uu____14484 -> false
  
let (is_irreducible : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let uu____14495 = lookup_qname env l  in
      match uu____14495 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,uu____14497),uu____14498) ->
          FStar_Util.for_some
            (fun uu___108_14546  ->
               match uu___108_14546 with
               | FStar_Syntax_Syntax.Irreducible  -> true
               | uu____14547 -> false) se.FStar_Syntax_Syntax.sigquals
      | uu____14548 -> false
  
let (is_type_constructor : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____14619 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____14635) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____14652 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____14659 ->
                 FStar_Pervasives_Native.Some true
             | uu____14676 -> FStar_Pervasives_Native.Some false)
         in
      let uu____14677 =
        let uu____14680 = lookup_qname env lid  in
        FStar_Util.bind_opt uu____14680 mapper  in
      match uu____14677 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
  
let (num_inductive_ty_params : env -> FStar_Ident.lident -> Prims.int) =
  fun env  ->
    fun lid  ->
      let uu____14730 = lookup_qname env lid  in
      match uu____14730 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____14731,uu____14732,tps,uu____14734,uu____14735,uu____14736);
              FStar_Syntax_Syntax.sigrng = uu____14737;
              FStar_Syntax_Syntax.sigquals = uu____14738;
              FStar_Syntax_Syntax.sigmeta = uu____14739;
              FStar_Syntax_Syntax.sigattrs = uu____14740;_},uu____14741),uu____14742)
          -> FStar_List.length tps
      | uu____14805 ->
          let uu____14806 = name_not_found lid  in
          let uu____14811 = FStar_Ident.range_of_lid lid  in
          FStar_Errors.raise_error uu____14806 uu____14811
  
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
           (fun uu____14855  ->
              match uu____14855 with
              | (d,uu____14863) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
  
let (get_effect_decl :
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl) =
  fun env  ->
    fun l  ->
      let uu____14878 = effect_decl_opt env l  in
      match uu____14878 with
      | FStar_Pervasives_Native.None  ->
          let uu____14893 = name_not_found l  in
          let uu____14898 = FStar_Ident.range_of_lid l  in
          FStar_Errors.raise_error uu____14893 uu____14898
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
  
let (identity_mlift : mlift) =
  {
    mlift_wp = (fun uu____14920  -> fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some
         (fun uu____14939  ->
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
        let uu____14970 = FStar_Ident.lid_equals l1 l2  in
        if uu____14970
        then (l1, identity_mlift, identity_mlift)
        else
          (let uu____14978 =
             ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
                &&
                (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
               ||
               ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                  &&
                  (FStar_Ident.lid_equals l1
                     FStar_Parser_Const.effect_Tot_lid))
              in
           if uu____14978
           then
             (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
               identity_mlift)
           else
             (let uu____14986 =
                FStar_All.pipe_right (env.effects).joins
                  (FStar_Util.find_opt
                     (fun uu____15039  ->
                        match uu____15039 with
                        | (m1,m2,uu____15052,uu____15053,uu____15054) ->
                            (FStar_Ident.lid_equals l1 m1) &&
                              (FStar_Ident.lid_equals l2 m2)))
                 in
              match uu____14986 with
              | FStar_Pervasives_Native.None  ->
                  let uu____15071 =
                    let uu____15076 =
                      let uu____15077 = FStar_Syntax_Print.lid_to_string l1
                         in
                      let uu____15078 = FStar_Syntax_Print.lid_to_string l2
                         in
                      FStar_Util.format2
                        "Effects %s and %s cannot be composed" uu____15077
                        uu____15078
                       in
                    (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____15076)
                     in
                  FStar_Errors.raise_error uu____15071 env.range
              | FStar_Pervasives_Native.Some
                  (uu____15085,uu____15086,m3,j1,j2) -> (m3, j1, j2)))
  
let (monad_leq :
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____15119 =
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
           in
        if uu____15119
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
  'Auu____15135 .
    (FStar_Syntax_Syntax.eff_decl,'Auu____15135)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                  FStar_Syntax_Syntax.syntax)
          FStar_Pervasives_Native.tuple2
  =
  fun decls  ->
    fun m  ->
      let uu____15164 =
        FStar_All.pipe_right decls
          (FStar_Util.find_opt
             (fun uu____15190  ->
                match uu____15190 with
                | (d,uu____15196) ->
                    FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m))
         in
      match uu____15164 with
      | FStar_Pervasives_Native.None  ->
          let uu____15207 =
            FStar_Util.format1
              "Impossible: declaration for monad %s not found"
              m.FStar_Ident.str
             in
          failwith uu____15207
      | FStar_Pervasives_Native.Some (md,_q) ->
          let uu____15220 =
            inst_tscheme
              ((md.FStar_Syntax_Syntax.univs),
                (md.FStar_Syntax_Syntax.signature))
             in
          (match uu____15220 with
           | (uu____15231,s) ->
               let s1 = FStar_Syntax_Subst.compress s  in
               (match ((md.FStar_Syntax_Syntax.binders),
                        (s1.FStar_Syntax_Syntax.n))
                with
                | ([],FStar_Syntax_Syntax.Tm_arrow
                   ((a,uu____15241)::(wp,uu____15243)::[],c)) when
                    FStar_Syntax_Syntax.is_teff
                      (FStar_Syntax_Util.comp_result c)
                    -> (a, (wp.FStar_Syntax_Syntax.sort))
                | uu____15279 -> failwith "Impossible"))
  
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
          let uu____15326 =
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
             in
          if uu____15326
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            (let uu____15328 =
               FStar_Ident.lid_equals eff_name
                 FStar_Parser_Const.effect_GTot_lid
                in
             if uu____15328
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
                  let uu____15336 = get_range env  in
                  let uu____15337 =
                    let uu____15344 =
                      let uu____15345 =
                        let uu____15360 =
                          let uu____15363 = FStar_Syntax_Syntax.as_arg res_t
                             in
                          [uu____15363]  in
                        (null_wp, uu____15360)  in
                      FStar_Syntax_Syntax.Tm_app uu____15345  in
                    FStar_Syntax_Syntax.mk uu____15344  in
                  uu____15337 FStar_Pervasives_Native.None uu____15336  in
                let uu____15369 =
                  let uu____15370 =
                    let uu____15379 = FStar_Syntax_Syntax.as_arg null_wp_res
                       in
                    [uu____15379]  in
                  {
                    FStar_Syntax_Syntax.comp_univs = [res_u];
                    FStar_Syntax_Syntax.effect_name = eff_name1;
                    FStar_Syntax_Syntax.result_typ = res_t;
                    FStar_Syntax_Syntax.effect_args = uu____15370;
                    FStar_Syntax_Syntax.flags = []
                  }  in
                FStar_Syntax_Syntax.mk_Comp uu____15369))
  
let (build_lattice : env -> FStar_Syntax_Syntax.sigelt -> env) =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___125_15392 = env.effects  in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___125_15392.order);
              joins = (uu___125_15392.joins)
            }  in
          let uu___126_15401 = env  in
          {
            solver = (uu___126_15401.solver);
            range = (uu___126_15401.range);
            curmodule = (uu___126_15401.curmodule);
            gamma = (uu___126_15401.gamma);
            gamma_cache = (uu___126_15401.gamma_cache);
            modules = (uu___126_15401.modules);
            expected_typ = (uu___126_15401.expected_typ);
            sigtab = (uu___126_15401.sigtab);
            is_pattern = (uu___126_15401.is_pattern);
            instantiate_imp = (uu___126_15401.instantiate_imp);
            effects;
            generalize = (uu___126_15401.generalize);
            letrecs = (uu___126_15401.letrecs);
            top_level = (uu___126_15401.top_level);
            check_uvars = (uu___126_15401.check_uvars);
            use_eq = (uu___126_15401.use_eq);
            is_iface = (uu___126_15401.is_iface);
            admit = (uu___126_15401.admit);
            lax = (uu___126_15401.lax);
            lax_universes = (uu___126_15401.lax_universes);
            failhard = (uu___126_15401.failhard);
            nosynth = (uu___126_15401.nosynth);
            tc_term = (uu___126_15401.tc_term);
            type_of = (uu___126_15401.type_of);
            universe_of = (uu___126_15401.universe_of);
            check_type_of = (uu___126_15401.check_type_of);
            use_bv_sorts = (uu___126_15401.use_bv_sorts);
            qtbl_name_and_index = (uu___126_15401.qtbl_name_and_index);
            normalized_eff_names = (uu___126_15401.normalized_eff_names);
            proof_ns = (uu___126_15401.proof_ns);
            synth_hook = (uu___126_15401.synth_hook);
            splice = (uu___126_15401.splice);
            is_native_tactic = (uu___126_15401.is_native_tactic);
            identifier_info = (uu___126_15401.identifier_info);
            tc_hooks = (uu___126_15401.tc_hooks);
            dsenv = (uu___126_15401.dsenv);
            dep_graph = (uu___126_15401.dep_graph)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp u r wp1 =
                let uu____15431 = (e1.mlift).mlift_wp u r wp1  in
                (e2.mlift).mlift_wp u r uu____15431  in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun u  ->
                          fun t  ->
                            fun wp  ->
                              fun e  ->
                                let uu____15589 = (e1.mlift).mlift_wp u t wp
                                   in
                                let uu____15590 = l1 u t wp e  in
                                l2 u t uu____15589 uu____15590))
                | uu____15591 -> FStar_Pervasives_Native.None  in
              { mlift_wp; mlift_term }  in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            }  in
          let mk_mlift_wp lift_t u r wp1 =
            let uu____15659 = inst_tscheme_with lift_t [u]  in
            match uu____15659 with
            | (uu____15666,lift_t1) ->
                let uu____15668 =
                  let uu____15675 =
                    let uu____15676 =
                      let uu____15691 =
                        let uu____15694 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15695 =
                          let uu____15698 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          [uu____15698]  in
                        uu____15694 :: uu____15695  in
                      (lift_t1, uu____15691)  in
                    FStar_Syntax_Syntax.Tm_app uu____15676  in
                  FStar_Syntax_Syntax.mk uu____15675  in
                uu____15668 FStar_Pervasives_Native.None
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
            let uu____15770 = inst_tscheme_with lift_t [u]  in
            match uu____15770 with
            | (uu____15777,lift_t1) ->
                let uu____15779 =
                  let uu____15786 =
                    let uu____15787 =
                      let uu____15802 =
                        let uu____15805 = FStar_Syntax_Syntax.as_arg r  in
                        let uu____15806 =
                          let uu____15809 = FStar_Syntax_Syntax.as_arg wp1
                             in
                          let uu____15810 =
                            let uu____15813 = FStar_Syntax_Syntax.as_arg e
                               in
                            [uu____15813]  in
                          uu____15809 :: uu____15810  in
                        uu____15805 :: uu____15806  in
                      (lift_t1, uu____15802)  in
                    FStar_Syntax_Syntax.Tm_app uu____15787  in
                  FStar_Syntax_Syntax.mk uu____15786  in
                uu____15779 FStar_Pervasives_Native.None
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
              let uu____15869 =
                let uu____15870 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____15870
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____15869  in
            let arg = bogus_term "ARG"  in
            let wp = bogus_term "WP"  in
            let e = bogus_term "COMP"  in
            let uu____15874 =
              let uu____15875 = l.mlift_wp FStar_Syntax_Syntax.U_zero arg wp
                 in
              FStar_Syntax_Print.term_to_string uu____15875  in
            let uu____15876 =
              let uu____15877 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____15903 = l1 FStar_Syntax_Syntax.U_zero arg wp e
                        in
                     FStar_Syntax_Print.term_to_string uu____15903)
                 in
              FStar_Util.dflt "none" uu____15877  in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____15874
              uu____15876
             in
          let order = edge :: ((env.effects).order)  in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____15929  ->
                    match uu____15929 with
                    | (e,uu____15937) -> e.FStar_Syntax_Syntax.mname))
             in
          let find_edge order1 uu____15960 =
            match uu____15960 with
            | (i,j) ->
                let uu____15971 = FStar_Ident.lid_equals i j  in
                if uu____15971
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
              let uu____16003 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        let uu____16013 = FStar_Ident.lid_equals i k  in
                        if uu____16013
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  let uu____16024 =
                                    FStar_Ident.lid_equals j k  in
                                  if uu____16024
                                  then []
                                  else
                                    (let uu____16028 =
                                       let uu____16037 =
                                         find_edge order1 (i, k)  in
                                       let uu____16040 =
                                         find_edge order1 (k, j)  in
                                       (uu____16037, uu____16040)  in
                                     match uu____16028 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____16055 =
                                           compose_edges e1 e2  in
                                         [uu____16055]
                                     | uu____16056 -> [])))))
                 in
              FStar_List.append order1 uu____16003  in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)  in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1
             in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____16086 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____16088 =
                          lookup_effect_quals env edge1.mtarget  in
                        FStar_All.pipe_right uu____16088
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect))
                      in
                   if uu____16086
                   then
                     let uu____16093 =
                       let uu____16098 =
                         FStar_Util.format1
                           "Divergent computations cannot be included in an effect %s marked 'total'"
                           (edge1.mtarget).FStar_Ident.str
                          in
                       (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                         uu____16098)
                        in
                     let uu____16099 = get_range env  in
                     FStar_Errors.raise_error uu____16093 uu____16099
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                let uu____16176 = FStar_Ident.lid_equals i j
                                   in
                                if uu____16176
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____16225 =
                                              let uu____16234 =
                                                find_edge order2 (i, k)  in
                                              let uu____16237 =
                                                find_edge order2 (j, k)  in
                                              (uu____16234, uu____16237)  in
                                            match uu____16225 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____16279,uu____16280)
                                                     ->
                                                     let uu____16287 =
                                                       let uu____16292 =
                                                         let uu____16293 =
                                                           find_edge order2
                                                             (k, ub)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16293
                                                          in
                                                       let uu____16296 =
                                                         let uu____16297 =
                                                           find_edge order2
                                                             (ub, k)
                                                            in
                                                         FStar_Util.is_some
                                                           uu____16297
                                                          in
                                                       (uu____16292,
                                                         uu____16296)
                                                        in
                                                     (match uu____16287 with
                                                      | (true ,true ) ->
                                                          let uu____16308 =
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                             in
                                                          if uu____16308
                                                          then
                                                            (FStar_Errors.log_issue
                                                               FStar_Range.dummyRange
                                                               (FStar_Errors.Warning_UpperBoundCandidateAlreadyVisited,
                                                                 "Looking multiple times at the same upper bound candidate");
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
                                            | uu____16333 -> bopt)
                                       FStar_Pervasives_Native.None)
                                 in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))]))))
               in
            let effects =
              let uu___127_16406 = env.effects  in
              { decls = (uu___127_16406.decls); order = order2; joins }  in
            let uu___128_16407 = env  in
            {
              solver = (uu___128_16407.solver);
              range = (uu___128_16407.range);
              curmodule = (uu___128_16407.curmodule);
              gamma = (uu___128_16407.gamma);
              gamma_cache = (uu___128_16407.gamma_cache);
              modules = (uu___128_16407.modules);
              expected_typ = (uu___128_16407.expected_typ);
              sigtab = (uu___128_16407.sigtab);
              is_pattern = (uu___128_16407.is_pattern);
              instantiate_imp = (uu___128_16407.instantiate_imp);
              effects;
              generalize = (uu___128_16407.generalize);
              letrecs = (uu___128_16407.letrecs);
              top_level = (uu___128_16407.top_level);
              check_uvars = (uu___128_16407.check_uvars);
              use_eq = (uu___128_16407.use_eq);
              is_iface = (uu___128_16407.is_iface);
              admit = (uu___128_16407.admit);
              lax = (uu___128_16407.lax);
              lax_universes = (uu___128_16407.lax_universes);
              failhard = (uu___128_16407.failhard);
              nosynth = (uu___128_16407.nosynth);
              tc_term = (uu___128_16407.tc_term);
              type_of = (uu___128_16407.type_of);
              universe_of = (uu___128_16407.universe_of);
              check_type_of = (uu___128_16407.check_type_of);
              use_bv_sorts = (uu___128_16407.use_bv_sorts);
              qtbl_name_and_index = (uu___128_16407.qtbl_name_and_index);
              normalized_eff_names = (uu___128_16407.normalized_eff_names);
              proof_ns = (uu___128_16407.proof_ns);
              synth_hook = (uu___128_16407.synth_hook);
              splice = (uu___128_16407.splice);
              is_native_tactic = (uu___128_16407.is_native_tactic);
              identifier_info = (uu___128_16407.identifier_info);
              tc_hooks = (uu___128_16407.tc_hooks);
              dsenv = (uu___128_16407.dsenv);
              dep_graph = (uu___128_16407.dep_graph)
            }))
      | uu____16408 -> env
  
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
        | uu____16436 -> c  in
      FStar_Syntax_Util.comp_to_comp_typ c1
  
let rec (unfold_effect_abbrev :
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp  in
      let uu____16448 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name
         in
      match uu____16448 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____16465 = FStar_Syntax_Subst.open_comp binders cdef  in
          (match uu____16465 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____16483 =
                     let uu____16488 =
                       let uu____16489 =
                         FStar_Util.string_of_int
                           (FStar_List.length binders1)
                          in
                       let uu____16494 =
                         FStar_Util.string_of_int
                           ((FStar_List.length
                               c.FStar_Syntax_Syntax.effect_args)
                              + (Prims.parse_int "1"))
                          in
                       let uu____16501 =
                         let uu____16502 = FStar_Syntax_Syntax.mk_Comp c  in
                         FStar_Syntax_Print.comp_to_string uu____16502  in
                       FStar_Util.format3
                         "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                         uu____16489 uu____16494 uu____16501
                        in
                     (FStar_Errors.Fatal_ConstructorArgLengthMismatch,
                       uu____16488)
                      in
                   FStar_Errors.raise_error uu____16483
                     comp.FStar_Syntax_Syntax.pos)
                else ();
                (let inst1 =
                   let uu____16507 =
                     let uu____16516 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ
                        in
                     uu____16516 :: (c.FStar_Syntax_Syntax.effect_args)  in
                   FStar_List.map2
                     (fun uu____16533  ->
                        fun uu____16534  ->
                          match (uu____16533, uu____16534) with
                          | ((x,uu____16556),(t,uu____16558)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____16507
                    in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1  in
                 let c2 =
                   let uu____16577 =
                     let uu___129_16578 = comp_to_comp_typ env c1  in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___129_16578.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___129_16578.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___129_16578.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___129_16578.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     }  in
                   FStar_All.pipe_right uu____16577
                     FStar_Syntax_Syntax.mk_Comp
                    in
                 unfold_effect_abbrev env c2)))
  
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
          let uu____16608 = effect_decl_opt env effect_name  in
          match uu____16608 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (ed,qualifiers) ->
              let uu____16641 =
                only_reifiable &&
                  (let uu____16643 =
                     FStar_All.pipe_right qualifiers
                       (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                      in
                   Prims.op_Negation uu____16643)
                 in
              if uu____16641
              then FStar_Pervasives_Native.None
              else
                (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
                 with
                 | FStar_Syntax_Syntax.Tm_unknown  ->
                     FStar_Pervasives_Native.None
                 | uu____16659 ->
                     let c1 = unfold_effect_abbrev env c  in
                     let res_typ = c1.FStar_Syntax_Syntax.result_typ  in
                     let wp =
                       match c1.FStar_Syntax_Syntax.effect_args with
                       | hd1::uu____16678 -> hd1
                       | [] ->
                           let name = FStar_Ident.string_of_lid effect_name
                              in
                           let message =
                             let uu____16707 =
                               FStar_Util.format1
                                 "Not enough arguments for effect %s. " name
                                in
                             Prims.strcat uu____16707
                               (Prims.strcat
                                  "This usually happens when you use a partially applied DM4F effect, "
                                  "like [TAC int] instead of [Tac int].")
                              in
                           let uu____16708 = get_range env  in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                               message) uu____16708
                        in
                     let repr =
                       inst_effect_fun_with [u_c] env ed
                         ([], (ed.FStar_Syntax_Syntax.repr))
                        in
                     let uu____16718 =
                       let uu____16721 = get_range env  in
                       let uu____16722 =
                         let uu____16729 =
                           let uu____16730 =
                             let uu____16745 =
                               let uu____16748 =
                                 FStar_Syntax_Syntax.as_arg res_typ  in
                               [uu____16748; wp]  in
                             (repr, uu____16745)  in
                           FStar_Syntax_Syntax.Tm_app uu____16730  in
                         FStar_Syntax_Syntax.mk uu____16729  in
                       uu____16722 FStar_Pervasives_Native.None uu____16721
                        in
                     FStar_Pervasives_Native.Some uu____16718)
  
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
          let uu____16808 =
            let uu____16813 =
              let uu____16814 = FStar_Ident.string_of_lid l  in
              FStar_Util.format1 "Effect %s cannot be reified" uu____16814
               in
            (FStar_Errors.Fatal_EffectCannotBeReified, uu____16813)  in
          let uu____16815 = get_range env  in
          FStar_Errors.raise_error uu____16808 uu____16815  in
        let uu____16816 = effect_repr_aux true env c u_c  in
        match uu____16816 with
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
      | uu____16862 -> false
  
let (is_reifiable_function : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____16873 =
        let uu____16874 = FStar_Syntax_Subst.compress t  in
        uu____16874.FStar_Syntax_Syntax.n  in
      match uu____16873 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____16877,c) ->
          is_reifiable_comp env c
      | uu____16895 -> false
  
let (push_in_gamma : env -> binding -> env) =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____16925)::uu____16926 -> x :: rest
        | (Binding_sig_inst uu____16935)::uu____16936 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____16951 = push1 x rest1  in local :: uu____16951
         in
      (env.tc_hooks).tc_push_in_gamma_hook env s;
      (let uu___130_16955 = env  in
       let uu____16956 = push1 s env.gamma  in
       {
         solver = (uu___130_16955.solver);
         range = (uu___130_16955.range);
         curmodule = (uu___130_16955.curmodule);
         gamma = uu____16956;
         gamma_cache = (uu___130_16955.gamma_cache);
         modules = (uu___130_16955.modules);
         expected_typ = (uu___130_16955.expected_typ);
         sigtab = (uu___130_16955.sigtab);
         is_pattern = (uu___130_16955.is_pattern);
         instantiate_imp = (uu___130_16955.instantiate_imp);
         effects = (uu___130_16955.effects);
         generalize = (uu___130_16955.generalize);
         letrecs = (uu___130_16955.letrecs);
         top_level = (uu___130_16955.top_level);
         check_uvars = (uu___130_16955.check_uvars);
         use_eq = (uu___130_16955.use_eq);
         is_iface = (uu___130_16955.is_iface);
         admit = (uu___130_16955.admit);
         lax = (uu___130_16955.lax);
         lax_universes = (uu___130_16955.lax_universes);
         failhard = (uu___130_16955.failhard);
         nosynth = (uu___130_16955.nosynth);
         tc_term = (uu___130_16955.tc_term);
         type_of = (uu___130_16955.type_of);
         universe_of = (uu___130_16955.universe_of);
         check_type_of = (uu___130_16955.check_type_of);
         use_bv_sorts = (uu___130_16955.use_bv_sorts);
         qtbl_name_and_index = (uu___130_16955.qtbl_name_and_index);
         normalized_eff_names = (uu___130_16955.normalized_eff_names);
         proof_ns = (uu___130_16955.proof_ns);
         synth_hook = (uu___130_16955.synth_hook);
         splice = (uu___130_16955.splice);
         is_native_tactic = (uu___130_16955.is_native_tactic);
         identifier_info = (uu___130_16955.identifier_info);
         tc_hooks = (uu___130_16955.tc_hooks);
         dsenv = (uu___130_16955.dsenv);
         dep_graph = (uu___130_16955.dep_graph)
       })
  
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
      let uu___131_17000 = env  in
      {
        solver = (uu___131_17000.solver);
        range = (uu___131_17000.range);
        curmodule = (uu___131_17000.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___131_17000.gamma_cache);
        modules = (uu___131_17000.modules);
        expected_typ = (uu___131_17000.expected_typ);
        sigtab = (uu___131_17000.sigtab);
        is_pattern = (uu___131_17000.is_pattern);
        instantiate_imp = (uu___131_17000.instantiate_imp);
        effects = (uu___131_17000.effects);
        generalize = (uu___131_17000.generalize);
        letrecs = (uu___131_17000.letrecs);
        top_level = (uu___131_17000.top_level);
        check_uvars = (uu___131_17000.check_uvars);
        use_eq = (uu___131_17000.use_eq);
        is_iface = (uu___131_17000.is_iface);
        admit = (uu___131_17000.admit);
        lax = (uu___131_17000.lax);
        lax_universes = (uu___131_17000.lax_universes);
        failhard = (uu___131_17000.failhard);
        nosynth = (uu___131_17000.nosynth);
        tc_term = (uu___131_17000.tc_term);
        type_of = (uu___131_17000.type_of);
        universe_of = (uu___131_17000.universe_of);
        check_type_of = (uu___131_17000.check_type_of);
        use_bv_sorts = (uu___131_17000.use_bv_sorts);
        qtbl_name_and_index = (uu___131_17000.qtbl_name_and_index);
        normalized_eff_names = (uu___131_17000.normalized_eff_names);
        proof_ns = (uu___131_17000.proof_ns);
        synth_hook = (uu___131_17000.synth_hook);
        splice = (uu___131_17000.splice);
        is_native_tactic = (uu___131_17000.is_native_tactic);
        identifier_info = (uu___131_17000.identifier_info);
        tc_hooks = (uu___131_17000.tc_hooks);
        dsenv = (uu___131_17000.dsenv);
        dep_graph = (uu___131_17000.dep_graph)
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
            (let uu___132_17055 = env  in
             {
               solver = (uu___132_17055.solver);
               range = (uu___132_17055.range);
               curmodule = (uu___132_17055.curmodule);
               gamma = rest;
               gamma_cache = (uu___132_17055.gamma_cache);
               modules = (uu___132_17055.modules);
               expected_typ = (uu___132_17055.expected_typ);
               sigtab = (uu___132_17055.sigtab);
               is_pattern = (uu___132_17055.is_pattern);
               instantiate_imp = (uu___132_17055.instantiate_imp);
               effects = (uu___132_17055.effects);
               generalize = (uu___132_17055.generalize);
               letrecs = (uu___132_17055.letrecs);
               top_level = (uu___132_17055.top_level);
               check_uvars = (uu___132_17055.check_uvars);
               use_eq = (uu___132_17055.use_eq);
               is_iface = (uu___132_17055.is_iface);
               admit = (uu___132_17055.admit);
               lax = (uu___132_17055.lax);
               lax_universes = (uu___132_17055.lax_universes);
               failhard = (uu___132_17055.failhard);
               nosynth = (uu___132_17055.nosynth);
               tc_term = (uu___132_17055.tc_term);
               type_of = (uu___132_17055.type_of);
               universe_of = (uu___132_17055.universe_of);
               check_type_of = (uu___132_17055.check_type_of);
               use_bv_sorts = (uu___132_17055.use_bv_sorts);
               qtbl_name_and_index = (uu___132_17055.qtbl_name_and_index);
               normalized_eff_names = (uu___132_17055.normalized_eff_names);
               proof_ns = (uu___132_17055.proof_ns);
               synth_hook = (uu___132_17055.synth_hook);
               splice = (uu___132_17055.splice);
               is_native_tactic = (uu___132_17055.is_native_tactic);
               identifier_info = (uu___132_17055.identifier_info);
               tc_hooks = (uu___132_17055.tc_hooks);
               dsenv = (uu___132_17055.dsenv);
               dep_graph = (uu___132_17055.dep_graph)
             }))
    | uu____17056 -> FStar_Pervasives_Native.None
  
let (push_binders : env -> FStar_Syntax_Syntax.binders -> env) =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____17082  ->
             match uu____17082 with | (x,uu____17088) -> push_bv env1 x) env
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
          let x2 =
            let uu___133_17118 = x1  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___133_17118.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___133_17118.FStar_Syntax_Syntax.index);
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
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___134_17158 = env  in
       {
         solver = (uu___134_17158.solver);
         range = (uu___134_17158.range);
         curmodule = (uu___134_17158.curmodule);
         gamma = [];
         gamma_cache = (uu___134_17158.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___134_17158.sigtab);
         is_pattern = (uu___134_17158.is_pattern);
         instantiate_imp = (uu___134_17158.instantiate_imp);
         effects = (uu___134_17158.effects);
         generalize = (uu___134_17158.generalize);
         letrecs = (uu___134_17158.letrecs);
         top_level = (uu___134_17158.top_level);
         check_uvars = (uu___134_17158.check_uvars);
         use_eq = (uu___134_17158.use_eq);
         is_iface = (uu___134_17158.is_iface);
         admit = (uu___134_17158.admit);
         lax = (uu___134_17158.lax);
         lax_universes = (uu___134_17158.lax_universes);
         failhard = (uu___134_17158.failhard);
         nosynth = (uu___134_17158.nosynth);
         tc_term = (uu___134_17158.tc_term);
         type_of = (uu___134_17158.type_of);
         universe_of = (uu___134_17158.universe_of);
         check_type_of = (uu___134_17158.check_type_of);
         use_bv_sorts = (uu___134_17158.use_bv_sorts);
         qtbl_name_and_index = (uu___134_17158.qtbl_name_and_index);
         normalized_eff_names = (uu___134_17158.normalized_eff_names);
         proof_ns = (uu___134_17158.proof_ns);
         synth_hook = (uu___134_17158.synth_hook);
         splice = (uu___134_17158.splice);
         is_native_tactic = (uu___134_17158.is_native_tactic);
         identifier_info = (uu___134_17158.identifier_info);
         tc_hooks = (uu___134_17158.tc_hooks);
         dsenv = (uu___134_17158.dsenv);
         dep_graph = (uu___134_17158.dep_graph)
       })
  
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
        let uu____17200 = FStar_Syntax_Subst.univ_var_opening uvs  in
        match uu____17200 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars  in
            let uu____17228 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms  in
            (env', univ_vars, uu____17228)
  
let (set_expected_typ : env -> FStar_Syntax_Syntax.typ -> env) =
  fun env  ->
    fun t  ->
      let uu___135_17245 = env  in
      {
        solver = (uu___135_17245.solver);
        range = (uu___135_17245.range);
        curmodule = (uu___135_17245.curmodule);
        gamma = (uu___135_17245.gamma);
        gamma_cache = (uu___135_17245.gamma_cache);
        modules = (uu___135_17245.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___135_17245.sigtab);
        is_pattern = (uu___135_17245.is_pattern);
        instantiate_imp = (uu___135_17245.instantiate_imp);
        effects = (uu___135_17245.effects);
        generalize = (uu___135_17245.generalize);
        letrecs = (uu___135_17245.letrecs);
        top_level = (uu___135_17245.top_level);
        check_uvars = (uu___135_17245.check_uvars);
        use_eq = false;
        is_iface = (uu___135_17245.is_iface);
        admit = (uu___135_17245.admit);
        lax = (uu___135_17245.lax);
        lax_universes = (uu___135_17245.lax_universes);
        failhard = (uu___135_17245.failhard);
        nosynth = (uu___135_17245.nosynth);
        tc_term = (uu___135_17245.tc_term);
        type_of = (uu___135_17245.type_of);
        universe_of = (uu___135_17245.universe_of);
        check_type_of = (uu___135_17245.check_type_of);
        use_bv_sorts = (uu___135_17245.use_bv_sorts);
        qtbl_name_and_index = (uu___135_17245.qtbl_name_and_index);
        normalized_eff_names = (uu___135_17245.normalized_eff_names);
        proof_ns = (uu___135_17245.proof_ns);
        synth_hook = (uu___135_17245.synth_hook);
        splice = (uu___135_17245.splice);
        is_native_tactic = (uu___135_17245.is_native_tactic);
        identifier_info = (uu___135_17245.identifier_info);
        tc_hooks = (uu___135_17245.tc_hooks);
        dsenv = (uu___135_17245.dsenv);
        dep_graph = (uu___135_17245.dep_graph)
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
    let uu____17273 = expected_typ env_  in
    ((let uu___136_17279 = env_  in
      {
        solver = (uu___136_17279.solver);
        range = (uu___136_17279.range);
        curmodule = (uu___136_17279.curmodule);
        gamma = (uu___136_17279.gamma);
        gamma_cache = (uu___136_17279.gamma_cache);
        modules = (uu___136_17279.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___136_17279.sigtab);
        is_pattern = (uu___136_17279.is_pattern);
        instantiate_imp = (uu___136_17279.instantiate_imp);
        effects = (uu___136_17279.effects);
        generalize = (uu___136_17279.generalize);
        letrecs = (uu___136_17279.letrecs);
        top_level = (uu___136_17279.top_level);
        check_uvars = (uu___136_17279.check_uvars);
        use_eq = false;
        is_iface = (uu___136_17279.is_iface);
        admit = (uu___136_17279.admit);
        lax = (uu___136_17279.lax);
        lax_universes = (uu___136_17279.lax_universes);
        failhard = (uu___136_17279.failhard);
        nosynth = (uu___136_17279.nosynth);
        tc_term = (uu___136_17279.tc_term);
        type_of = (uu___136_17279.type_of);
        universe_of = (uu___136_17279.universe_of);
        check_type_of = (uu___136_17279.check_type_of);
        use_bv_sorts = (uu___136_17279.use_bv_sorts);
        qtbl_name_and_index = (uu___136_17279.qtbl_name_and_index);
        normalized_eff_names = (uu___136_17279.normalized_eff_names);
        proof_ns = (uu___136_17279.proof_ns);
        synth_hook = (uu___136_17279.synth_hook);
        splice = (uu___136_17279.splice);
        is_native_tactic = (uu___136_17279.is_native_tactic);
        identifier_info = (uu___136_17279.identifier_info);
        tc_hooks = (uu___136_17279.tc_hooks);
        dsenv = (uu___136_17279.dsenv);
        dep_graph = (uu___136_17279.dep_graph)
      }), uu____17273)
  
let (finish_module : env -> FStar_Syntax_Syntax.modul -> env) =
  let empty_lid =
    let uu____17289 =
      let uu____17292 = FStar_Ident.id_of_text ""  in [uu____17292]  in
    FStar_Ident.lid_of_ids uu____17289  in
  fun env  ->
    fun m  ->
      let sigs =
        let uu____17298 =
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
           in
        if uu____17298
        then
          let uu____17301 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___109_17311  ->
                    match uu___109_17311 with
                    | Binding_sig (uu____17314,se) -> [se]
                    | uu____17320 -> []))
             in
          FStar_All.pipe_right uu____17301 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports  in
      add_sigelts env sigs;
      (let uu___137_17327 = env  in
       {
         solver = (uu___137_17327.solver);
         range = (uu___137_17327.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___137_17327.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___137_17327.expected_typ);
         sigtab = (uu___137_17327.sigtab);
         is_pattern = (uu___137_17327.is_pattern);
         instantiate_imp = (uu___137_17327.instantiate_imp);
         effects = (uu___137_17327.effects);
         generalize = (uu___137_17327.generalize);
         letrecs = (uu___137_17327.letrecs);
         top_level = (uu___137_17327.top_level);
         check_uvars = (uu___137_17327.check_uvars);
         use_eq = (uu___137_17327.use_eq);
         is_iface = (uu___137_17327.is_iface);
         admit = (uu___137_17327.admit);
         lax = (uu___137_17327.lax);
         lax_universes = (uu___137_17327.lax_universes);
         failhard = (uu___137_17327.failhard);
         nosynth = (uu___137_17327.nosynth);
         tc_term = (uu___137_17327.tc_term);
         type_of = (uu___137_17327.type_of);
         universe_of = (uu___137_17327.universe_of);
         check_type_of = (uu___137_17327.check_type_of);
         use_bv_sorts = (uu___137_17327.use_bv_sorts);
         qtbl_name_and_index = (uu___137_17327.qtbl_name_and_index);
         normalized_eff_names = (uu___137_17327.normalized_eff_names);
         proof_ns = (uu___137_17327.proof_ns);
         synth_hook = (uu___137_17327.synth_hook);
         splice = (uu___137_17327.splice);
         is_native_tactic = (uu___137_17327.is_native_tactic);
         identifier_info = (uu___137_17327.identifier_info);
         tc_hooks = (uu___137_17327.tc_hooks);
         dsenv = (uu___137_17327.dsenv);
         dep_graph = (uu___137_17327.dep_graph)
       })
  
let (uvars_in_env : env -> FStar_Syntax_Syntax.uvars) =
  fun env  ->
    let no_uvs = FStar_Syntax_Free.new_uv_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____17418)::tl1 -> aux out tl1
      | (Binding_lid (uu____17422,(uu____17423,t)))::tl1 ->
          let uu____17438 =
            let uu____17445 = FStar_Syntax_Free.uvars t  in
            ext out uu____17445  in
          aux uu____17438 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17452;
            FStar_Syntax_Syntax.index = uu____17453;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17460 =
            let uu____17467 = FStar_Syntax_Free.uvars t  in
            ext out uu____17467  in
          aux uu____17460 tl1
      | (Binding_sig uu____17474)::uu____17475 -> out
      | (Binding_sig_inst uu____17484)::uu____17485 -> out  in
    aux no_uvs env.gamma
  
let (univ_vars : env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set) =
  fun env  ->
    let no_univs = FStar_Syntax_Free.new_universe_uvar_set ()  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____17550)::tl1 -> aux out tl1
      | (Binding_univ uu____17562)::tl1 -> aux out tl1
      | (Binding_lid (uu____17566,(uu____17567,t)))::tl1 ->
          let uu____17582 =
            let uu____17585 = FStar_Syntax_Free.univs t  in
            ext out uu____17585  in
          aux uu____17582 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17588;
            FStar_Syntax_Syntax.index = uu____17589;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17596 =
            let uu____17599 = FStar_Syntax_Free.univs t  in
            ext out uu____17599  in
          aux uu____17596 tl1
      | (Binding_sig uu____17602)::uu____17603 -> out  in
    aux no_univs env.gamma
  
let (univnames : env -> FStar_Syntax_Syntax.univ_name FStar_Util.set) =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names  in
    let ext out uvs = FStar_Util.set_union out uvs  in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____17666)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____17682 = FStar_Util.set_add uname out  in
          aux uu____17682 tl1
      | (Binding_lid (uu____17685,(uu____17686,t)))::tl1 ->
          let uu____17701 =
            let uu____17704 = FStar_Syntax_Free.univnames t  in
            ext out uu____17704  in
          aux uu____17701 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____17707;
            FStar_Syntax_Syntax.index = uu____17708;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____17715 =
            let uu____17718 = FStar_Syntax_Free.univnames t  in
            ext out uu____17718  in
          aux uu____17715 tl1
      | (Binding_sig uu____17721)::uu____17722 -> out  in
    aux no_univ_names env.gamma
  
let (bound_vars_of_bindings :
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list) =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___110_17748  ->
            match uu___110_17748 with
            | Binding_var x -> [x]
            | Binding_lid uu____17752 -> []
            | Binding_sig uu____17757 -> []
            | Binding_univ uu____17764 -> []
            | Binding_sig_inst uu____17765 -> []))
  
let (binders_of_bindings : binding Prims.list -> FStar_Syntax_Syntax.binders)
  =
  fun bs  ->
    let uu____17783 =
      let uu____17786 = bound_vars_of_bindings bs  in
      FStar_All.pipe_right uu____17786
        (FStar_List.map FStar_Syntax_Syntax.mk_binder)
       in
    FStar_All.pipe_right uu____17783 FStar_List.rev
  
let (bound_vars : env -> FStar_Syntax_Syntax.bv Prims.list) =
  fun env  -> bound_vars_of_bindings env.gamma 
let (all_binders : env -> FStar_Syntax_Syntax.binders) =
  fun env  -> binders_of_bindings env.gamma 
let (print_gamma : env -> unit) =
  fun env  ->
    let uu____17814 =
      let uu____17815 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___111_17825  ->
                match uu___111_17825 with
                | Binding_var x ->
                    let uu____17827 = FStar_Syntax_Print.bv_to_string x  in
                    Prims.strcat "Binding_var " uu____17827
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____17830) ->
                    let uu____17831 = FStar_Ident.string_of_lid l  in
                    Prims.strcat "Binding_lid " uu____17831
                | Binding_sig (ls,uu____17833) ->
                    let uu____17838 =
                      let uu____17839 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____17839
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig " uu____17838
                | Binding_sig_inst (ls,uu____17849,uu____17850) ->
                    let uu____17855 =
                      let uu____17856 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid)
                         in
                      FStar_All.pipe_right uu____17856
                        (FStar_String.concat ", ")
                       in
                    Prims.strcat "Binding_sig_inst " uu____17855))
         in
      FStar_All.pipe_right uu____17815 (FStar_String.concat "::\n")  in
    FStar_All.pipe_right uu____17814 (FStar_Util.print1 "%s\n")
  
let (eq_gamma : env -> env -> Prims.bool) =
  fun env  ->
    fun env'  ->
      let uu____17877 = FStar_Util.physical_equality env.gamma env'.gamma  in
      if uu____17877
      then true
      else
        (let g = all_binders env  in
         let g' = all_binders env'  in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____17905  ->
                 fun uu____17906  ->
                   match (uu____17905, uu____17906) with
                   | ((b1,uu____17924),(b2,uu____17926)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
  
let fold_env : 'a . env -> ('a -> binding -> 'a) -> 'a -> 'a =
  fun env  ->
    fun f  ->
      fun a  ->
        FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
  
let (string_of_delta_level : delta_level -> Prims.string) =
  fun uu___112_17977  ->
    match uu___112_17977 with
    | NoDelta  -> "NoDelta"
    | Inlining  -> "Inlining"
    | Eager_unfolding_only  -> "Eager_unfolding_only"
    | Unfold uu____17978 -> "Unfold _"
    | UnfoldTac  -> "UnfoldTac"
  
let (lidents : env -> FStar_Ident.lident Prims.list) =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___113_17998  ->
             match uu___113_17998 with
             | Binding_sig (lids,uu____18004) -> FStar_List.append lids keys
             | uu____18009 -> keys) [] env.gamma
       in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____18015  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
  
let (should_enc_path : env -> Prims.string Prims.list -> Prims.bool) =
  fun env  ->
    fun path  ->
      let rec list_prefix xs ys =
        match (xs, ys) with
        | ([],uu____18057) -> true
        | (x::xs1,y::ys1) -> (x = y) && (list_prefix xs1 ys1)
        | (uu____18076,uu____18077) -> false  in
      let uu____18086 =
        FStar_List.tryFind
          (fun uu____18104  ->
             match uu____18104 with | (p,uu____18112) -> list_prefix p path)
          env.proof_ns
         in
      match uu____18086 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some (uu____18123,b) -> b
  
let (should_enc_lid : env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun lid  ->
      let uu____18145 = FStar_Ident.path_of_lid lid  in
      should_enc_path env uu____18145
  
let (cons_proof_ns : Prims.bool -> env -> name_prefix -> env) =
  fun b  ->
    fun e  ->
      fun path  ->
        let uu___138_18163 = e  in
        {
          solver = (uu___138_18163.solver);
          range = (uu___138_18163.range);
          curmodule = (uu___138_18163.curmodule);
          gamma = (uu___138_18163.gamma);
          gamma_cache = (uu___138_18163.gamma_cache);
          modules = (uu___138_18163.modules);
          expected_typ = (uu___138_18163.expected_typ);
          sigtab = (uu___138_18163.sigtab);
          is_pattern = (uu___138_18163.is_pattern);
          instantiate_imp = (uu___138_18163.instantiate_imp);
          effects = (uu___138_18163.effects);
          generalize = (uu___138_18163.generalize);
          letrecs = (uu___138_18163.letrecs);
          top_level = (uu___138_18163.top_level);
          check_uvars = (uu___138_18163.check_uvars);
          use_eq = (uu___138_18163.use_eq);
          is_iface = (uu___138_18163.is_iface);
          admit = (uu___138_18163.admit);
          lax = (uu___138_18163.lax);
          lax_universes = (uu___138_18163.lax_universes);
          failhard = (uu___138_18163.failhard);
          nosynth = (uu___138_18163.nosynth);
          tc_term = (uu___138_18163.tc_term);
          type_of = (uu___138_18163.type_of);
          universe_of = (uu___138_18163.universe_of);
          check_type_of = (uu___138_18163.check_type_of);
          use_bv_sorts = (uu___138_18163.use_bv_sorts);
          qtbl_name_and_index = (uu___138_18163.qtbl_name_and_index);
          normalized_eff_names = (uu___138_18163.normalized_eff_names);
          proof_ns = ((path, b) :: (e.proof_ns));
          synth_hook = (uu___138_18163.synth_hook);
          splice = (uu___138_18163.splice);
          is_native_tactic = (uu___138_18163.is_native_tactic);
          identifier_info = (uu___138_18163.identifier_info);
          tc_hooks = (uu___138_18163.tc_hooks);
          dsenv = (uu___138_18163.dsenv);
          dep_graph = (uu___138_18163.dep_graph)
        }
  
let (add_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns true e path 
let (rem_proof_ns : env -> name_prefix -> env) =
  fun e  -> fun path  -> cons_proof_ns false e path 
let (get_proof_ns : env -> proof_namespace) = fun e  -> e.proof_ns 
let (set_proof_ns : proof_namespace -> env -> env) =
  fun ns  ->
    fun e  ->
      let uu___139_18203 = e  in
      {
        solver = (uu___139_18203.solver);
        range = (uu___139_18203.range);
        curmodule = (uu___139_18203.curmodule);
        gamma = (uu___139_18203.gamma);
        gamma_cache = (uu___139_18203.gamma_cache);
        modules = (uu___139_18203.modules);
        expected_typ = (uu___139_18203.expected_typ);
        sigtab = (uu___139_18203.sigtab);
        is_pattern = (uu___139_18203.is_pattern);
        instantiate_imp = (uu___139_18203.instantiate_imp);
        effects = (uu___139_18203.effects);
        generalize = (uu___139_18203.generalize);
        letrecs = (uu___139_18203.letrecs);
        top_level = (uu___139_18203.top_level);
        check_uvars = (uu___139_18203.check_uvars);
        use_eq = (uu___139_18203.use_eq);
        is_iface = (uu___139_18203.is_iface);
        admit = (uu___139_18203.admit);
        lax = (uu___139_18203.lax);
        lax_universes = (uu___139_18203.lax_universes);
        failhard = (uu___139_18203.failhard);
        nosynth = (uu___139_18203.nosynth);
        tc_term = (uu___139_18203.tc_term);
        type_of = (uu___139_18203.type_of);
        universe_of = (uu___139_18203.universe_of);
        check_type_of = (uu___139_18203.check_type_of);
        use_bv_sorts = (uu___139_18203.use_bv_sorts);
        qtbl_name_and_index = (uu___139_18203.qtbl_name_and_index);
        normalized_eff_names = (uu___139_18203.normalized_eff_names);
        proof_ns = ns;
        synth_hook = (uu___139_18203.synth_hook);
        splice = (uu___139_18203.splice);
        is_native_tactic = (uu___139_18203.is_native_tactic);
        identifier_info = (uu___139_18203.identifier_info);
        tc_hooks = (uu___139_18203.tc_hooks);
        dsenv = (uu___139_18203.dsenv);
        dep_graph = (uu___139_18203.dep_graph)
      }
  
let (unbound_vars :
  env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set) =
  fun e  ->
    fun t  ->
      let uu____18218 = FStar_Syntax_Free.names t  in
      let uu____18221 = bound_vars e  in
      FStar_List.fold_left (fun s  -> fun bv  -> FStar_Util.set_remove bv s)
        uu____18218 uu____18221
  
let (closed : env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      let uu____18242 = unbound_vars e t  in
      FStar_Util.set_is_empty uu____18242
  
let (closed' : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____18250 = FStar_Syntax_Free.names t  in
    FStar_Util.set_is_empty uu____18250
  
let (string_of_proof_ns : env -> Prims.string) =
  fun env  ->
    let aux uu____18269 =
      match uu____18269 with
      | (p,b) ->
          if (p = []) && b
          then "*"
          else
            (let uu____18285 = FStar_Ident.text_of_path p  in
             Prims.strcat (if b then "+" else "-") uu____18285)
       in
    let uu____18287 =
      let uu____18290 = FStar_List.map aux env.proof_ns  in
      FStar_All.pipe_right uu____18290 FStar_List.rev  in
    FStar_All.pipe_right uu____18287 (FStar_String.concat " ")
  
let (dummy_solver : solver_t) =
  {
    init = (fun uu____18307  -> ());
    push = (fun uu____18309  -> ());
    pop = (fun uu____18311  -> ());
    snapshot =
      (fun uu____18313  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    rollback = (fun uu____18322  -> fun uu____18323  -> ());
    encode_modul = (fun uu____18334  -> fun uu____18335  -> ());
    encode_sig = (fun uu____18338  -> fun uu____18339  -> ());
    preprocess =
      (fun e  ->
         fun g  ->
           let uu____18345 =
             let uu____18352 = FStar_Options.peek ()  in (e, g, uu____18352)
              in
           [uu____18345]);
    solve = (fun uu____18368  -> fun uu____18369  -> fun uu____18370  -> ());
    finish = (fun uu____18376  -> ());
    refresh = (fun uu____18378  -> ())
  } 